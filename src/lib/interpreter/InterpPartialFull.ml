open Nv_datastructures
open Nv_lang
open Nv_lang.Syntax
open Nv_lang.Collections
open Nv_utils.OCamlUtils
open InterpUtils
open Interp

(** * Simplifications *)
let simplify_and v1 e2 =
  match v1.v with
  | VBool true -> e2
  | VBool false -> exp_of_value (vbool false)
  | _ -> failwith "illegal value to boolean"
;;

let simplify_or v1 e2 =
  match v1.v with
  | VBool true -> exp_of_value (vbool true)
  | VBool false -> e2
  | _ -> failwith "illegal value to boolean"
;;

let rec simplify_tget lo hi e =
  match e.e with
  | ETuple es ->
    Some
      (if lo = hi
      then List.nth es lo
      else etuple (es |> BatList.drop lo |> BatList.take (hi - lo + 1)))
  | _ -> None
;;

let simplify_tset lo hi tup v =
  match tup.e with
  | ETuple es ->
    if lo = hi
    then Some (etuple (BatList.modify_at lo (fun _ -> v) es))
    else (
      match v.e with
      | ETuple vs -> Some (etuple (replaceSlice lo hi es vs))
      | _ -> None)
  | _ -> None
;;

let simplify_exps op pes =
  match op with
  | And ->
    begin
      match pes with
      | [e1; e2] when is_value e1 -> simplify_and (to_value e1) e2
      | [e1; e2] when is_value e2 -> simplify_and (to_value e2) e1
      | _ -> eop op pes
    end
  | Or ->
    begin
      match pes with
      | [e1; e2] when is_value e1 -> simplify_or (to_value e1) e2
      | [e1; e2] when is_value e2 -> simplify_or (to_value e2) e1
      | [e1; e2] when equal_exps ~cmp_meta:false e1 e2 -> e1
      | [e1; e2] ->
        (match e1.e with
        | EOp (Not, [e1']) when equal_exps ~cmp_meta:false e1' e2 ->
          exp_of_value (vbool true)
        | _ ->
          (match e2.e with
          | EOp (Not, [e2']) when equal_exps ~cmp_meta:false e1 e2' ->
            exp_of_value (vbool true)
          | _ -> eop op pes))
      | _ -> eop op pes
    end
  | TGet (_, lo, hi) ->
    begin
      match pes with
      | [e] ->
        (match simplify_tget lo hi e with
        | None -> eop op pes
        | Some e -> e)
      | _ -> failwith "Bad TGet"
    end
  | TSet (_, lo, hi) ->
    begin
      match pes with
      | [e1; e2] ->
        (match simplify_tset lo hi e1 e2 with
        | None -> eop op pes
        | Some e -> e)
      | _ -> failwith "Bad TSet"
    end
  | _ -> eop op pes
;;

type 'a isMatch =
  | Match of 'a
  | NoMatch
  | Delayed

(* matches p b is Some env if v matches p and None otherwise; assumes no repeated variables in pattern *)
let rec matches p (e : Syntax.exp) : Syntax.exp Env.t isMatch =
  match p with
  | PWild -> Match Env.empty
  | PUnit -> Match Env.empty
  | PVar x -> Match (Env.bind x e)
  | PBool true ->
    if is_value e
    then (
      match (to_value e).v with
      | VBool true -> Match Env.empty
      | _ -> NoMatch)
    else Delayed
  | PBool false ->
    if is_value e
    then (
      match (to_value e).v with
      | VBool false -> Match Env.empty
      | _ -> NoMatch)
    else Delayed
  | PInt i1 ->
    if is_value e
    then (
      match (to_value e).v with
      | VInt i2 -> if Integer.equal i1 i2 then Match Env.empty else NoMatch
      | _ -> NoMatch)
    else Delayed
  | PNode n1 ->
    if is_value e
    then (
      match (to_value e).v with
      | VNode n2 -> if n1 = n2 then Match Env.empty else NoMatch
      | _ -> NoMatch)
    else Delayed
  | PEdge (p1, p2) ->
    if is_value e
    then (
      match (to_value e).v with
      | VEdge (n1, n2) ->
        matches_list [p1; p2] [e_val (vnode n1); e_val (vnode n2)] Env.empty
      | _ -> NoMatch)
    else Delayed
  | PTuple ps ->
    (* only match tuples when all components match *)
    if is_value e
    then (
      match e.e with
      | ETuple es -> matches_list ps es Env.empty
      | EVal v ->
        (match v.v with
        | VTuple vs -> matches_list ps (BatList.map exp_of_value vs) Env.empty
        | _ -> NoMatch)
      | _ -> NoMatch)
    else Delayed
  | POption None ->
    if is_value e
    then (
      match (to_value e).v with
      | VOption None -> Match Env.empty
      | _ -> NoMatch)
    else Delayed
  | POption (Some p) ->
    (match e.e with
    | ESome e1 -> matches p e1
    | _ when is_value e ->
      (match (to_value e).v with
      | VOption (Some v) -> matches p (exp_of_value v)
      | _ -> NoMatch)
    | _ -> Delayed)
  | PRecord _ -> failwith "Record found during partial interpretation"

and matches_list ps es env =
  match ps, es with
  | [], [] -> Match env
  | p :: ps, e :: es ->
    (match matches p e with
    | NoMatch -> NoMatch
    | Delayed -> Delayed
    | Match env1 -> matches_list ps es (Env.updates env env1))
  | _, _ -> NoMatch
;;

let rec match_branches_lst branches v =
  match branches with
  | [] -> NoMatch
  | (p, e) :: branches ->
    (match matches p v with
    | Match env -> Match (env, e)
    | NoMatch -> match_branches_lst branches v
    | Delayed -> Delayed)
;;

let rec matchExpPat pat pe1 env =
  match pat, pe1.e with
  | PWild, _ -> Match env
  | PUnit, _ -> Match env
  | PVar x, _ -> Match (Env.update env x pe1)
  | POption (Some p), ESome e -> matchExpPat p e env
  | PTuple ps, ETuple es ->
    (match ps, es with
    | [], [] -> Match env
    | p :: ps, e :: es ->
      (match matchExpPat p e env with
      | Delayed -> Delayed
      | Match env -> matchExpPat (PTuple ps) (etuple es) env
      | NoMatch -> failwith "No match?")
    | _, _ -> Delayed)
  | _, _ -> Delayed
;;

(*for now *)

let rec matchExp branches pe1 =
  match popBranch branches with
  | (pat, e), branches' ->
    if isEmptyBranch branches'
    then (
      match matchExpPat pat pe1 Env.empty with
      | Delayed -> Delayed
      | Match env -> Match (env, e)
      | NoMatch -> failwith "No match?")
    else Delayed
;;

let rec matchExpPatFull pat pe1 env =
  (* Printf.printf
   *   "pat:%s, exp:%s\n"
   *   (Printing.pattern_to_string pat)
   *   (Printing.exp_to_string pe1); *)
  match pat, pe1.e with
  | PWild, _ -> Match env
  | PUnit, _ -> Match env
  | PVar x, _ -> Match (Env.update env x pe1)
  | POption (Some p), ESome e -> matchExpPatFull p e env
  | POption None, ESome _ -> NoMatch
  | PTuple ps, ETuple es ->
    (match ps, es with
    | [], [] -> Match env
    | p :: ps, e :: es ->
      (match matchExpPatFull p e env with
      | Delayed -> Delayed
      | Match env -> matchExpPatFull (PTuple ps) (etuple es) env
      | NoMatch -> NoMatch)
    | _, _ -> Delayed)
  | _, EVal _ -> matches pat pe1
  | _, _ -> Delayed
;;

(* more aggressive expression matcher.
 * will look at every branch instead of just the first. *)
(* procedure:
 * check each branch for the pattern.
 * if the branch *could* match, but we're not sure, stop and return Delayed
 * if it definitely can't match, continue
 * if it matches, return Match *)
(* TODO: remove branches that can't match *)
let rec matchExpFull branches pe1 =
  match popBranch branches with
  | (pat, e), branches' ->
    (match matchExpPatFull pat pe1 Env.empty with
    | Delayed -> Delayed
    | Match env -> Match (env, e)
    | NoMatch ->
      if isEmptyBranch branches' then failwith "No match?" else matchExpFull branches' pe1)
;;

(* I guess this means we only try to match supposedly-irrefutable patterns *)

let rec match_branches branches v =
  if is_value v
  then (
    (* Printf.printf "v:%s" (Printing.exp_to_string v);
     * iterBranches (fun (p,e) -> Printf.printf "pat:%s\n" (Printing.pattern_to_string p)) branches; *)
    match lookUpPat (val_to_pat (to_value v)) branches with
    | Found e -> Match (Env.empty, e)
    | Rest ls -> match_branches_lst ls v)
  else matchExpFull branches v
;;

(** Assumes that inlining has been performed.  Not CBN in the
    strict sense. It will just do function applications over
    expressions, not just values.*)
let rec interp_exp_partial (env : Syntax.exp Env.t) e =
  match e.e with
  | ETy (e, _) -> interp_exp_partial env e
  | EVar x ->
    (match Env.lookup_opt env x with
    | None -> env, e
    | Some e1 -> env, e1)
  | EVal _ -> env, e
  | EOp (op, es) -> env, aexp (interp_op_partial env (oget e.ety) op es, e.ety, e.espan)
  | EFun _ -> env, e
  (* either need to do the partial interpretation here, or return a pair
     of the efun and the env at this point to be used, sort of like a closure.*)
  | EApp (e1, e2) ->
    let cenv, pe1 = interp_exp_partial env e1 in
    let _, pe2 = interp_exp_partial env e2 in
    (match pe1.e with
    | EFun f -> interp_exp_partial (Env.update cenv f.arg pe2) f.body
    | _ ->
      (*this case shouldn't show up for us *)
      failwith "This case shouldn't show up")
  | EIf (e1, e2, e3) ->
    let _, pe1 = interp_exp_partial env e1 in
    if is_value pe1
    then (
      match (to_value pe1).v with
      | VBool true -> interp_exp_partial env e2
      | VBool false -> interp_exp_partial env e3
      | _ -> failwith "bad if condition")
    else
      ( env
      , aexp
          ( eif pe1 (snd (interp_exp_partial env e2)) (snd (interp_exp_partial env e3))
          , e.ety
          , e.espan ) )
  | ELet (x, e1, e2) ->
    let _, pe1 = interp_exp_partial env e1 in
    (* if is_value pe1 then *)
    interp_exp_partial (Env.update env x pe1) e2
  (* else
   *   (env, aexp(elet x pe1 (snd (interp_exp_partial env e2)), Some (oget e.ety), e.espan)) *)
  | ETuple es ->
    ( env
    , aexp
        (etuple (BatList.map (fun e -> snd (interp_exp_partial env e)) es), e.ety, e.espan)
    )
  | ESome e' -> env, aexp (esome (snd (interp_exp_partial env e')), e.ety, e.espan)
  | EMatch (e1, branches) ->
    let _, pe1 = interp_exp_partial env e1 in
    (match match_branches branches pe1 with
    | Match (env2, e) -> interp_exp_partial (Env.updates env env2) e
    | NoMatch ->
      failwith
        ("exp "
        ^ Printing.exp_to_string pe1
        ^ " did not match any pattern in match statement")
    | Delayed ->
      ( env
      , aexp
          ( ematch
              pe1
              (mapBranches (fun (p, e) -> p, snd (interp_exp_partial env e)) branches)
          , e.ety
          , e.espan ) ))
  | ERecord _ | EProject _ -> failwith "Record found during partial interpretation"

(* this is same as above, minus the app boolean. see again if we can get rid of that? *)
and interp_op_partial env ty op es =
  let pes = BatList.map (fun e -> snd (interp_exp_partial env e)) es in
  if BatList.exists (fun pe -> not (is_value pe)) pes || op = MCreate
  then simplify_exps op pes
  else
    exp_of_value
    @@
    match op, BatList.map to_value pes with
    | And, [{ v = VBool b1 }; { v = VBool b2 }] -> vbool (b1 && b2)
    | Or, [{ v = VBool b1 }; { v = VBool b2 }] -> vbool (b1 || b2)
    | Not, [{ v = VBool b1 }] -> vbool (not b1)
    | UAdd _, [{ v = VInt i1 }; { v = VInt i2 }] -> vint (Integer.add i1 i2)
    | Eq, [v1; v2] ->
      if equal_values ~cmp_meta:false v1 v2 then vbool true else vbool false
    | ULess _, [{ v = VInt i1 }; { v = VInt i2 }] ->
      if Integer.lt i1 i2 then vbool true else vbool false
    | ULeq _, [{ v = VInt i1 }; { v = VInt i2 }] ->
      if Integer.leq i1 i2 then vbool true else vbool false
    | UAnd _, [{ v = VInt i1 }; { v = VInt i2 }] -> vint (Integer.uand i1 i2)
    | NLess, [{ v = VNode n1 }; { v = VNode n2 }] ->
      if n1 < n2 then vbool true else vbool false
    | NLeq, [{ v = VNode n1 }; { v = VNode n2 }] ->
      if n1 <= n2 then vbool true else vbool false
    | TGet (size, lo, hi), [{ v = VTuple elts }] ->
      assert (List.length elts = size);
      (* Sanity check *)
      if lo = hi
      then List.nth elts lo
      else vtuple (elts |> BatList.drop lo |> BatList.take (hi - lo + 1))
    | TSet (size, lo, hi), [{ v = VTuple elts }; v] ->
      assert (List.length elts = size);
      (* Sanity check *)
      if lo = hi
      then vtuple (BatList.modify_at lo (fun _ -> v) elts)
      else (
        match v.v with
        | VTuple velts ->
          let hd, rest = BatList.takedrop lo elts in
          let _, tl = BatList.takedrop (hi - lo + 1) rest in
          vtuple (hd @ velts @ tl)
        | _ -> failwith "Bad TSet")
    | MCreate, [v] ->
      ignore v;
      ignore ty;
      (* Doing this before map unrolling was breaking stuff, so I'm disabling it
         for now. We could imagine having a flag that tells you whether or not
         to simplify map operations, but I suspect for the most part we just
         don't want to in the first case *)
      failwith "Disabled"
      (* (match get_inner_type ty with
         | TMap (kty, _) -> vmap (BddMap.create ~key_ty:kty v)
         | _ -> failwith "runtime error: missing map key type") *)
    | MGet, [{ v = VMap m }; v] -> BddMap.find m v
    | MSet, [{ v = VMap m }; vkey; vval] -> vmap (BddMap.update m vkey vval)
    | MMap, [{ v = VClosure (c_env, f) }; { v = VMap m }] ->
      let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
      let free = Syntax.free seen f.body in
      let env = build_env c_env free in
      vmap (BddMap.map ~op_key:(f.body, env) (fun v -> apply c_env f v) m)
    | MFoldNode, [{ v = VClosure (c_env, f) }; acc; { v = VMap m }]
    | MFoldEdge, [{ v = VClosure (c_env, f) }; acc; { v = VMap m }] ->
      let bindings, _ = BddMap.bindings m in
      let apply_f acc (k, v) =
        match apply c_env f k with
        | { v = VClosure (c_env', f') } ->
          begin
            match apply c_env' f' v with
            | { v = VClosure (c_env'', f'') } -> apply c_env'' f'' acc
            | _ -> failwith "internal error (interp_op_partial)"
          end
        | _ -> failwith "internal error (interp_op_partial)"
      in
      List.fold_left apply_f acc bindings
    | MMerge, { v = VClosure (c_env, f) } :: { v = VMap m1 } :: { v = VMap m2 } :: rest ->
      let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
      let env = build_env c_env (Syntax.free seen f.body) in
      (* TO DO:  Need to preserve types in VOptions here ? *)
      let f_lifted v1 v2 =
        match apply c_env f v1 with
        | { v = VClosure (c_env, f) } -> apply c_env f v2
        | _ -> failwith "internal error (interp_op)"
      in
      (match rest with
      | [el0; el1; er0; er1] ->
        let opt = el0, el1, er0, er1 in
        vmap (BddMap.merge ~opt ~op_key:(f.body, env) f_lifted m1 m2)
      | _ -> vmap (BddMap.merge ~op_key:(f.body, env) f_lifted m1 m2))
    | ( MMapFilter
      , [{ v = VClosure (c_env1, f1) }; { v = VClosure (c_env2, f2) }; { v = VMap m }] )
      ->
      let seen = BatSet.PSet.singleton ~cmp:Var.compare f2.arg in
      let env = build_env c_env2 (Syntax.free seen f2.body) in
      let seen1 = Syntax.free (BatSet.PSet.singleton ~cmp:Var.compare f1.arg) f1.body in
      let usedValEnv = Env.filter c_env1.value (fun x _ -> BatSet.PSet.mem x seen1) in
      let lookupVal = f1.body, usedValEnv in
      let mtbdd =
        match ExpEnvMap.Exceptionless.find lookupVal !bddfunc_cache with
        | None ->
          let bddf = BddFunc.create_value (Nv_utils.OCamlUtils.oget f1.argty) in
          let env =
            Env.update (Env.map usedValEnv (fun v -> BddFunc.eval_value v)) f1.arg bddf
          in
          let bddf = BddFunc.eval env f1.body in
          (match bddf with
          | BBool bdd ->
            let mtbdd = BddFunc.wrap_mtbdd bdd in
            bddfunc_cache := ExpEnvMap.add lookupVal mtbdd !bddfunc_cache;
            mtbdd
          | _ -> failwith "impossible")
        | Some bddf -> bddf
      in
      let f v = apply c_env2 f2 v in
      vmap (BddMap.map_when ~op_key:(f2.body, env) mtbdd f m)
    | _, _ ->
      failwith (Printf.sprintf "bad operator application: %s" (Printing.op_to_string op))
;;

let interp_partial e = snd (interp_exp_partial Env.empty e)

let interp_partial_fun (fn : Syntax.exp) (args : exp list) =
  let e = Syntax.apps fn args in
  interp_partial e
;;
