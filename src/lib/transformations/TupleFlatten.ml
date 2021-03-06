open Batteries
open Nv_lang
open Nv_datastructures
open Collections
open Syntax
open Nv_utils.OCamlUtils
open Nv_solution

(*
Given a tuple type and an index into that tuple, return:
  * The size of the flattened tuple
  * A range of indices in the flattened tuple that correspond to the input index
*)
let size_and_index_after_flattening flatten_ty ty lo hi =
  let flattened_size ty =
    match flatten_ty ty with
    | TTuple lst -> List.length lst
    | _ -> 1
  in
  match ty with
  | TTuple elts ->
    let sizes = List.map (fun ty -> flattened_size ty) elts in
    let hd, rest = List.takedrop lo sizes in
    let mid, tl = List.takedrop (hi - lo + 1) rest in
    let offset = List.fold_left ( + ) 0 hd in
    let diff = List.fold_left ( + ) 0 mid in
    let total_size = offset + diff + List.fold_left ( + ) 0 tl in
    total_size, offset, offset + diff - 1
  | _ -> failwith "Called size_and_index_after_flattening without tuple type"
;;

let ty_transformer (recursors : Transformers.recursors) ty =
  match ty with
  | TTuple tys ->
    let tys = List.map recursors.recurse_ty tys in
    let tys' =
      List.fold_right
        (fun ty acc ->
          match ty with
          | TTuple ts -> List.append ts acc
          | _ -> ty :: acc)
        tys
        []
    in
    Some (TTuple tys')
  | TArrow (t1, t2) ->
    let t1, t2 = recursors.recurse_ty t1, recursors.recurse_ty t2 in
    begin
      match t1 with
      | TTuple tys -> Some (List.fold_right (fun t acc -> TArrow (t, acc)) tys t2)
      | _ -> Some (TArrow (t1, t2))
    end
  | _ -> None
;;

let pattern_transformer (recursors : Transformers.recursors) p ty =
  match p, ty with
  | PTuple ps, TTuple tys ->
    let ps = List.map2 recursors.recurse_pattern ps tys in
    let ps' =
      List.fold_right
        (fun p acc ->
          match p with
          | PTuple ps -> ps @ acc
          | _ -> p :: acc)
        ps
        []
    in
    Some (PTuple ps')
  | PVar x, TTuple _ ->
    begin
      match recursors.recurse_ty ty with
      | TTuple tys ->
        let ps = List.mapi (fun i _ -> PVar (proj_var i x)) tys in
        Some (PTuple ps)
      | _ -> failwith "impossible"
    end
  | PWild, TTuple _ ->
    begin
      match recursors.recurse_ty ty with
      | TTuple tys -> Some (PTuple (List.map (fun _ -> PWild) tys))
      | _ -> failwith "impossible"
    end
  | _ -> None
;;

let value_transformer (recursors : Transformers.recursors) v =
  match v.v with
  | VTuple vs ->
    let vs = List.map recursors.recurse_value vs in
    let vs' =
      List.fold_right
        (fun v acc ->
          match v.v with
          | VTuple vs -> List.append vs acc
          | _ -> v :: acc)
        vs
        []
    in
    Some (vtuple vs')
  | _ -> None
;;

let exp_transformer (recursors : Transformers.recursors) e =
  let flatten_ty = recursors.recurse_ty in
  let flatten_exp = recursors.recurse_exp in
  match e.e with
  | EVar x ->
    begin
      match flatten_ty (oget e.ety) with
      | TTuple ts ->
        let es =
          List.mapi (fun i ty -> aexp (evar (proj_var i x), Some ty, Span.default)) ts
        in
        Some (etuple es)
      | _ -> None
    end
  | EFun { arg = x; argty = Some xty; resty = Some _; body } ->
    begin
      match flatten_ty xty with
      | TTuple ts ->
        Some
          (List.fold_righti
             (fun i ty acce ->
               aexp
                 ( efun
                     { arg = proj_var i x
                     ; argty = Some ty
                     ; resty = acce.ety
                     ; body = acce
                     }
                 , Some (TArrow (ty, oget acce.ety))
                 , e.espan ))
             ts
             (flatten_exp body))
      | _ -> None
    end
  | EFun _ -> failwith "missing types in function declaration"
  | EApp (e1, e2) ->
    let e2 = flatten_exp e2 in
    begin
      match e2.e with
      | ETuple es -> Some (apps (flatten_exp e1) es)
      | _ -> Some (eapp (flatten_exp e1) e2)
    end
  | ELet (x, e1, e2) ->
    let e1 = flatten_exp e1 in
    let ty = flatten_ty (oget e.ety) in
    begin
      match e1.e with
      | ETuple es ->
        let es = List.mapi (fun i e -> proj_var i x, e) es in
        Some
          (List.fold_right
             (fun (xi, ei) acc -> aexp (elet xi ei acc, Some ty, ei.espan))
             es
             (flatten_exp e2))
      | _ ->
        begin
          match oget e1.ety with
          | TTuple ts ->
            let ps = List.mapi (fun i _ -> PVar (proj_var i x)) ts in
            Some (ematch e1 (addBranch (PTuple ps) (flatten_exp e2) emptyBranch))
          | _ -> Some (elet x e1 (flatten_exp e2))
        end
    end
  | ETuple es ->
    let es = List.map flatten_exp es in
    (* Dummy exp which is only used as an argument to wrap *)
    let wrapper = aexp (etuple [], Some (flatten_ty (oget e.ety)), e.espan) in
    (* Extract the elements of e, then call cont to move on to the next e.
       Once we have all of them we'll put them together into one big tuple exp *)
    let curry_elts e (cont : exp list -> exp) =
      match e.e with
      | ETuple es -> cont es
      | EVal v ->
        (match v.v with
        | VTuple vs -> cont (List.map e_val vs)
        | _ -> cont [e])
      | _ ->
        (match oget e.ety with
        | TTuple tys ->
          (* Tuple type, but not directly a tuple expression. We need to name its
             elements, so we have to use a match expression. *)
          let freshvarexps, pat =
            List.fold_left
              (fun (exps, pats) ty ->
                let v = Nv_datastructures.Var.fresh "TupleFlattenVar" in
                aexp (evar v, Some ty, e.espan) :: exps, PVar v :: pats)
              ([], [])
              (List.rev tys)
          in
          let body = cont freshvarexps in
          ematch e (addBranch (PTuple pat) body emptyBranch) |> wrap wrapper
        | _ -> cont [e])
    in
    let rec build_exp lst acc =
      match lst with
      | [] -> etuple (List.rev acc) |> wrap wrapper
      | hd :: tl -> curry_elts hd (fun es -> build_exp tl (List.rev_append es acc))
    in
    Some (build_exp es [])
  | EOp (op, es) ->
    let size_and_index_after_flattening =
      size_and_index_after_flattening recursors.recurse_ty
    in
    (match op with
    | MMap | MMapFilter | MMerge | MFoldNode | MFoldEdge ->
      failwith "TODO: Not sure if we need to do anything special for these ops"
    | TGet (_, lo, hi) ->
      let tup =
        match es with
        | [e] -> e
        | _ -> failwith "Bad TGet"
      in
      let size, lo, hi = size_and_index_after_flattening (oget tup.ety) lo hi in
      Some (eop (TGet (size, lo, hi)) (List.map flatten_exp es))
    | TSet (_, lo, hi) ->
      let tup =
        match es with
        | [e1; _] -> e1
        | _ -> failwith "Bad TSet"
      in
      let size, lo, hi = size_and_index_after_flattening (oget tup.ety) lo hi in
      Some (eop (TSet (size, lo, hi)) (List.map flatten_exp es))
    | Eq ->
      (match es with
      | [e1; e2]
        when match oget e1.ety with
             | TTuple _ -> true
             | _ -> false ->
        let e1 = flatten_exp e1 in
        let e2 = flatten_exp e2 in
        (match tupleToListSafe e1, tupleToListSafe e2 with
        | (_ :: _ :: _ as es1), (_ :: _ :: _ as es2) ->
          Some
            (List.fold_left2
               (fun acc e1 e2 ->
                 let eq12 = eop Eq [e1; e2] |> wrap e in
                 eop And [eq12; acc] |> wrap e)
               (e_val (vbool true) |> wrap e)
               es1
               es2)
        | _ -> None)
      | _ -> None)
    | _ -> None)
  | _ -> None
;;

let rec flattened_size ty =
  match ty with
  | TTuple tys -> List.fold_left (fun acc ty -> acc + flattened_size ty) 0 tys
  | _ -> 1
;;

let unflatten_list (vs : value list) (tys : ty list) =
  let vs, excess =
    List.fold_left
      (fun (acc, rest) ty ->
        match ty with
        | TTuple _ ->
          let vs, tl = List.takedrop (flattened_size ty) rest in
          vtuple vs :: acc, tl
        | _ -> List.hd rest :: acc, List.tl rest)
      ([], vs)
      tys
  in
  assert (List.is_empty excess);
  List.rev vs
;;

let map_back_transformer recurse _ v orig_ty =
  match v.v, orig_ty with
  | VTuple vs, TTuple tys ->
    let vs' = unflatten_list vs tys in
    Some (vtuple (List.map2 recurse vs' tys))
  | _ -> None
;;

let mask_transformer = map_back_transformer

(* Currently, Transformers doesn't support changing the number of symbolics. So we
   have to do that manually here *)

let proj_symbolic (var, toe) =
  (* Flattening should have already happened *)
  match toe with
  | Exp e ->
    (match tupleToListSafe e with
    | [e] -> [var, Exp e]
    | es -> List.mapi (fun i ei -> proj_var i var, Exp ei) es)
  | Ty ty ->
    (match ty with
    | TTuple ts -> List.mapi (fun i ty -> proj_var i var, Ty ty) ts
    | ty -> [var, Ty ty])
;;

(*NOTE: Taking the easy way out of here by converting to a map first. It should
   be correct though because likely we have unique bindings.*)
let unproj_sym_solve (map : (Var.t * 'a) list) =
  let map = List.fold_left (fun acc (k, v) -> VarMap.add k v acc) VarMap.empty map in
  let unboxed_map =
    VarMap.fold
      (fun var v acc ->
        let index, var' =
          try unproj_var var with
          | Not_found -> 0, var
        in
        VarMap.modify_def [] var' (fun xs -> (index, v) :: xs) acc)
      map
      VarMap.empty
  in
  (* Transform our lists of (index, 'a) pairs into the corresponding tuples *)
  (* The SmtModel code does this for labels, but we need to do it here for
     symbolics and solves.*)
  let unprojed =
    VarMap.map
      (fun elts ->
        let lst = List.sort (fun a b -> compare (fst a) (fst b)) elts in
        List.map snd lst)
      unboxed_map
  in
  unprojed
;;

let unproj_symbolics_and_solves (sol : Solution.t) =
  let symbs =
    VarMap.fold
      (fun var lst acc ->
        ( var
        , match lst with
          | [v] -> v
          | _ -> vtuple lst )
        :: acc)
      (unproj_sym_solve sol.symbolics)
      []
  in
  let solves =
    let open Solution in
    VarMap.fold
      (fun var lst acc ->
        match lst with
        | [solve] -> (var, solve) :: acc
        | _ ->
          (* For a given solution, either all masks are None or all are Some.
                I think. *)
          let masked = (List.hd lst).mask <> None in
          let sol_val = vtuple (List.map (fun s -> s.sol_val) lst) in
          let sol_ty = List.map (fun s -> s.attr_ty) lst in
          let mask =
            if not masked
            then None
            else Some (vtuple (List.map (fun s -> oget s.mask) lst))
          in
          let attr_ty = TTuple sol_ty in
          (var, { sol_val; mask; attr_ty }) :: acc) (*NOTE: type here might be wrong *)
      (unproj_sym_solve sol.solves)
      []
  in
  { sol with symbolics = symbs; solves }
;;

let make_toplevel (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer
    ~name:"TupleFlatten"
    ty_transformer
    pattern_transformer
    value_transformer
    exp_transformer
    map_back_transformer
    mask_transformer
;;

let flatten_decl d =
  match d with
  | DSymbolic (x, toe) ->
    let flattened = proj_symbolic (x, toe) in
    List.map (fun (x, toe) -> DSymbolic (x, toe)) flattened
  | _ -> [d]
;;

let flatten_declarations decls =
  let decls, f = make_toplevel Transformers.transform_declarations decls in
  List.map flatten_decl decls |> List.concat, f % unproj_symbolics_and_solves
;;
