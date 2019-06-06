open Syntax
open Typing

let is_function_ty e =
  match get_inner_type (oget e.ety) with
  | TArrow _ -> true
  | _ -> false

let rec has_var p x =
  match p with
  | PWild | PUnit | PBool _ | PInt _ -> false
  | PVar y -> Var.equals x y
  | PTuple ps ->
      BatList.fold_left (fun acc p -> acc || has_var p x) false ps
  | POption None -> false
  | POption (Some p) -> has_var p x
  | PRecord _ -> failwith "Found record during Inlining"

let rec remove_all env p =
  match p with
  | PWild | PUnit | PBool _ | PInt _ -> env
  | PVar x -> Env.remove env x
  | PTuple ps ->
      BatList.fold_left (fun acc p -> remove_all acc p) env ps
  | POption None -> env
  | POption (Some p) -> remove_all env p
  | PRecord _ -> failwith "Found record during Inlining"

let rec substitute x e1 e2 =
  match e1.e with
  | EVar y -> if Var.equals x y then e2 else e1
  | EFun f ->
      if Var.equals x f.arg then e1
      else efun {f with body= substitute x f.body e2} |> wrap e1
  | EApp (e3, e4) ->
      eapp (substitute x e3 e2) (substitute x e4 e2) |> wrap e1
  | EIf (e3, e4, e5) ->
      eif (substitute x e3 e2) (substitute x e4 e2)
        (substitute x e5 e2)
      |> wrap e1
  | ELet (y, e3, e4) ->
      if Var.equals x y then elet y (substitute x e3 e2) e4
      else
        elet y (substitute x e3 e2) (substitute x e4 e2) |> wrap e1
  | ETy (e1, ty) -> ety (substitute x e1 e2) ty |> wrap e1
  | EMatch (e, bs) ->
      ematch (substitute x e e2)
        (mapBranches (fun (p,e) -> substitute_pattern x e2 (p,e)) bs)
      |> wrap e1
  | ESome e -> esome (substitute x e e2) |> wrap e1
  | ETuple es ->
      etuple (BatList.map (fun e -> substitute x e e2) es) |> wrap e1
  | EOp (op, es) ->
      eop op (BatList.map (fun e -> substitute x e e2) es) |> wrap e1
  | EVal _ -> e1
  | ERecord _ | EProject _ -> failwith "Found record during Inlining"


and substitute_pattern x e2 (p, e) =
  if has_var p x then (p, e) else (p, substitute x e e2)

let rec inline_app env e1 e2 : exp =
  let exp =
    match e1.e with
    | EVar x -> (
      match Env.lookup_opt env x with
      | None -> eapp e1 e2 |> wrap e1
      | Some e -> inline_app env e e2 )
    | EFun f ->
        let e = substitute f.arg f.body e2 in
        inline_exp env e
    | EIf (e3, e4, e5) ->
        let etrue = inline_app env e4 e2 in
        let efalse = inline_app env e5 e2 in
        eif e3 etrue efalse |> wrap e1
    | ELet (x, e3, e4) ->
        let e5 = inline_exp env (eapp e4 e2 |> wrap e4) in
        elet x e3 e5 |> wrap e1
    | ETy (e1, ty) -> inline_app env e1 e2
    | EMatch (e, bs) ->
        let e = inline_exp env e in
        let branches =
          mapBranches (fun (p,e) -> inline_branch_app env e2 (p,e)) bs
        in
        ematch e branches |> wrap e1
    | EApp _ -> eapp e1 e2 |> wrap e1
    | ESome _ | ETuple _ | EOp _ | EVal _ | ERecord _ | EProject _->
        failwith
          (Printf.sprintf "inline_app: %s"
             (Printing.exp_to_string e1))
  in
  (* Printf.printf "inline_app e1: %s\ninline_app e2: %s)\n"
    (Printing.exp_to_string e1)
    (Printing.exp_to_string e2) ;
  Printf.printf "result: %s\n\n" (Printing.exp_to_string exp); *)
  exp

and inline_branch_app env e2 (p, e) = (p, inline_app env e e2)

and inline_exp (env: exp Env.t) (e: exp) : exp =
  match e.e with
  | EVar x -> (
    match Env.lookup_opt env x with None -> e | Some e1 -> e1 )
  | EVal v -> e
  | EOp (op, es) -> eop op (BatList.map (inline_exp env) es) |> wrap e
  | EFun f ->
     let body = inline_exp env f.body in
     efun {f with body} |> wrap e
  | EApp (e1, e2) ->
     inline_app env (inline_exp env e1) (inline_exp env e2)
  | EIf (e1, e2, e3) ->
     eif (inline_exp env e1) (inline_exp env e2)
         (inline_exp env e3)
     |> wrap e
  | ELet (x, e1, e2) ->
       let e1' = inline_exp env e1 in
       (* (match e1.ety with *)
       (* | None -> Printf.printf "no type\n"; *)
       (* | Some ty -> *)
       (*    Printf.printf "crashes here: %s\n" (Printing.ty_to_string ty)); *)
       (* Printf.printf "crashes here: %s\n" (Printing.exp_to_string e1); *)
       if is_function_ty e1 then
           inline_exp (Env.update env x e1') e2
       else elet x e1' (inline_exp env e2) |> wrap e
  | ETuple es -> etuple (BatList.map (inline_exp env) es) |> wrap e
  | ESome e1 -> esome (inline_exp env e1) |> wrap e
  | EMatch (e1, bs) ->
     ematch (inline_exp env e1)
            (mapBranches (fun (p,e) -> inline_branch env (p,e)) bs)
     |> wrap e
  | ETy (e1, ty) -> ety (inline_exp env e1) ty |> wrap e
  | ERecord _ | EProject _ -> failwith "Found record during Inlining"

  (* Printf.printf "inline: %s\n" (Printing.exp_to_string e);
  Printf.printf "result: %s\n\n" (Printing.exp_to_string ret); *)

(* TODO: right now this is assuming that patterns won't contain functions
   this will fail for example with an expression like:  Some (fun v -> v) *)
and inline_branch env (p, e) =
  let env' = remove_all env p in
  (p, inline_exp env' e)

let inline_declaration (env: exp Env.t) (d: declaration) =
  match d with
  | DLet (x, tyo, e) ->
     let e = inline_exp env e in
     (* TODO: Ask Ryan, why not always inline? performance reasons presumably? *)
     (Env.update env x e, None)
      (* if is_function_ty e then (Env.update env x e, None) *)
      (* else (env, Some (DLet (x, tyo, e))) *)
  | DSymbolic (x, e) ->
     (env, Some (DSymbolic (x, e)))
  | DMerge e -> (env, Some (DMerge (inline_exp env e)))
  | DTrans e -> (env, Some (DTrans (inline_exp env e)))
  | DInit e -> (env, Some (DInit (inline_exp env e)))
  | DAssert e -> (env, Some (DAssert (inline_exp env e)))
  | DRequire e -> (env, Some (DRequire (inline_exp env e)))
  | DATy _ | DUserTy _ | DNodes _ | DEdges _ -> (env, Some d)

let rec inline_declarations (ds: declarations) =
  match get_attr_type ds with
  | None ->
     failwith "attribute type not declared: type attribute = ..."
  | Some ty -> inline_declarations_aux Env.empty ds

and inline_declarations_aux env (ds: declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' = inline_declaration env d in
      match d' with
      | None -> inline_declarations_aux env' ds'
      | Some d' -> d' :: inline_declarations_aux env' ds'