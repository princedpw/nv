open Nv_lang
open Nv_datastructures
open Nv_utils
open Syntax
open Memoization
open Printing
open Collections
open InterpUtils
open Batteries

(* Interpreter Errors *)
(* Interpreter Environments *)

let update_values env venv = { env with value = Env.updates env.value venv }
let update_ty env x t = { env with ty = Env.update env.ty x t }

let update_tys env tvs tys =
  let rec loop tenv tvs tys =
    match tvs, tys with
    | [], [] -> tenv
    | tv :: tvs, ty :: tys -> loop (Env.update tenv tv ty) tvs tys
    | _, _ -> failwith "wrong arity in type application"
  in
  { env with ty = loop env.ty tvs tys }
;;

let rec match_branches branches v env =
  (* iterBranches (fun (p,e) ->  Printf.printf "%s\n" (Printing.pattern_to_string p)) branches;
   * Printf.printf "val: %s\n" (Printing.value_to_string v); *)
  match lookUpPat (val_to_pat v) branches with
  | Found e -> Some (env, e)
  | Rest ls -> match_branches_lst ls v env
;;

let rec interp_exp env e =
  match e.e with
  | ETy (e, _) -> interp_exp env e
  | EVar x ->
    (match Env.lookup_opt env.value x with
    | None ->
      failwith
        (Printf.sprintf "runtime exception - unbound variable: %s" (Var.to_string x))
    | Some v -> v)
  | EVal v -> avalue (v, e.ety, e.espan)
  | EOp (op, es) -> interp_op env (OCamlUtils.oget e.ety) op es
  | EFun f -> avalue (vclosure (env, f), e.ety, e.espan)
  | EApp (e1, e2) ->
    let v1 = interp_exp env e1 in
    let v2 = interp_exp env e2 in
    (match v1.v with
    | VClosure (c_env, f) ->
      interp_exp (update_env c_env f.arg v2 (OCamlUtils.oget f.argty)) f.body
    | _ -> failwith "bad functional application")
  | EIf (e1, e2, e3) ->
    (match (interp_exp env e1).v with
    | VBool true -> interp_exp env e2
    | VBool false -> interp_exp env e3
    | _ -> failwith "bad if condition")
  | ELet (x, e1, e2) ->
    let v1 = interp_exp env e1 in
    interp_exp (update_env env x v1 (Nv_utils.OCamlUtils.oget e1.ety)) e2
  | ETuple es -> avalue (vtuple (List.map (interp_exp env) es), e.ety, e.espan)
  | ESome e -> avalue (voption (Some (interp_exp env e)), e.ety, e.espan)
  | EMatch (e1, branches) ->
    let v = interp_exp env e1 in
    (match match_branches branches v env.value with
    | Some (env2, e) -> interp_exp { env with value = env2 } e
    | None ->
      failwith
        ("value " ^ value_to_string v ^ " did not match any pattern in match statement"))
  | ERecord _ | EProject _ -> failwith "Record found during interpretation"

and interp_op env ty op es =
  (* if arity op != List.length es then
     failwith
      (sprintf "operation %s has arity %d not arity %d"
         (op_to_string op) (arity op) (List.length es)) ; *)
  let vs = BatList.map (interp_exp env) es in
  match op, vs with
  | And, [{ v = VBool b1 }; { v = VBool b2 }] -> vbool (b1 && b2)
  | Or, [{ v = VBool b1 }; { v = VBool b2 }] -> vbool (b1 || b2)
  | Not, [{ v = VBool b1 }] -> vbool (not b1)
  | UAdd _, [{ v = VInt i1 }; { v = VInt i2 }] -> vint (Integer.add i1 i2)
  | Eq, [v1; v2] -> if equal_values ~cmp_meta:false v1 v2 then vbool true else vbool false
  | ULess _, [{ v = VInt i1 }; { v = VInt i2 }] ->
    if Integer.lt i1 i2 then vbool true else vbool false
  | ULeq _, [{ v = VInt i1 }; { v = VInt i2 }] ->
    if Integer.leq i1 i2 then vbool true else vbool false
  | UAnd _, [{ v = VInt i1 }; { v = VInt i2 }] -> vint (Integer.uand i1 i2)
  | NLess, [{ v = VNode n1 }; { v = VNode n2 }] ->
    if n1 < n2 then vbool true else vbool false
  | NLeq, [{ v = VNode n1 }; { v = VNode n2 }] ->
    if n1 <= n2 then vbool true else vbool false
  | TGet (_, lo, hi), [{ v = VTuple elts }] ->
    (* assert (List.length elts = size) ; (\* Sanity check *\) *)
    if lo = hi
    then List.nth elts lo
    else vtuple (elts |> BatList.drop lo |> BatList.take (hi - lo + 1))
  | TSet (_, lo, hi), [{ v = VTuple elts }; v] ->
    (* assert (List.length elts = size) ; (\* Sanity check *\) *)
    if lo = hi
    then vtuple (BatList.modify_at lo (fun _ -> v) elts)
    else (
      match v.v with
      | VTuple velts -> vtuple (OCamlUtils.replaceSlice lo hi elts velts)
      | _ -> failwith "Bad TSet")
  | MCreate, [v] ->
    (match get_inner_type ty with
    | TMap (kty, _) -> vmap (BddMap.create ~key_ty:kty v)
    | _ -> failwith "runtime error: missing map key type")
  | MGet, [{ v = VMap m }; v] -> BddMap.find m v
  | MSet, [{ v = VMap m }; vkey; vval] -> vmap (BddMap.update m vkey vval)
  | MMap, [{ v = VClosure (c_env, f) }; { v = VMap m }] ->
    let seen = BatSet.PSet.singleton ~cmp:Var.compare f.arg in
    let free = Syntax.free seen f.body in
    let env = build_env c_env free in
    vmap (BddMap.map ~op_key:(f.body, env) (fun v -> apply c_env f v) m)
  | MFoldNode, [{ v = VClosure (c_env, f) }; { v = VMap m }; acc]
  | MFoldEdge, [{ v = VClosure (c_env, f) }; { v = VMap m }; acc] ->
    let bindings, _ = BddMap.bindings m in
    let apply_f acc (k, v) =
      match apply c_env f k with
      | { v = VClosure (c_env', f') } ->
        begin
          match apply c_env' f' v with
          | { v = VClosure (c_env'', f'') } -> apply c_env'' f'' acc
          | _ -> failwith "internal error (interp_op)"
        end
      | _ -> failwith "internal error (interp_op)"
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
    , [{ v = VClosure (c_env1, f1) }; { v = VClosure (c_env2, f2) }; { v = VMap m }] ) ->
    (* Compute the closure of the function applied over the leafs *)
    let seen2 = BatSet.PSet.singleton ~cmp:Var.compare f2.arg in
    let env2 = build_env c_env2 (Syntax.free seen2 f2.body) in
    (* Likewise for the predicate, and create a cache entry *)
    let seen1 = Syntax.free (BatSet.PSet.singleton ~cmp:Var.compare f1.arg) f1.body in
    let usedValEnv = Env.filter c_env1.value (fun x _ -> BatSet.PSet.mem x seen1) in
    let lookupVal = f1.body, usedValEnv in
    let mtbdd =
      match ExpEnvMap.Exceptionless.find lookupVal !bddfunc_cache with
      | None ->
        let bddf = BddFunc.create_value (Nv_utils.OCamlUtils.oget f1.argty) in
        let env =
          Env.update (Env.map usedValEnv (fun v -> BddFunc.Value v)) f1.arg bddf
        in
        (* Compute BDD out of predicate *)
        let bddf = BddFunc.eval env f1.body in
        let bddf =
          match bddf with
          | Value v -> BddFunc.eval_value v
          | _ -> bddf
        in
        (match bddf with
        | BBool bdd ->
          let mtbdd = BddFunc.wrap_mtbdd bdd in
          bddfunc_cache := ExpEnvMap.add lookupVal mtbdd !bddfunc_cache;
          mtbdd
        | BMap mtbdd ->
          let mtbdd = BddFunc.value_mtbdd_bool_mtbdd (fst mtbdd) in
          bddfunc_cache := ExpEnvMap.add lookupVal mtbdd !bddfunc_cache;
          mtbdd
        | _ -> failwith "impossible")
      | Some bddf -> bddf
    in
    let f v = apply c_env2 f2 v in
    vmap (BddMap.map_when ~op_key:(f2.body, env2) mtbdd f m)
  | ( MMapIte
    , [ { v = VClosure (c_env0, p) }
      ; { v = VClosure (c_env1, f1) }
      ; { v = VClosure (c_env2, f2) }
      ; { v = VMap m } ] ) ->
    let seen1 = BatSet.PSet.singleton ~cmp:Var.compare f1.arg in
    let env1 = build_env c_env1 (Syntax.free seen1 f1.body) in
    let seen2 = BatSet.PSet.singleton ~cmp:Var.compare f2.arg in
    let env2 = build_env c_env2 (Syntax.free seen2 f2.body) in
    (* Create closure for predicate *)
    let seen0 = Syntax.free (BatSet.PSet.singleton ~cmp:Var.compare p.arg) p.body in
    let usedValEnv = Env.filter c_env0.value (fun x _ -> BatSet.PSet.mem x seen0) in
    let lookupVal = p.body, usedValEnv in
    let mtbdd =
      match ExpEnvMap.Exceptionless.find lookupVal !bddfunc_cache with
      | None ->
        let bddf = BddFunc.create_value (Nv_utils.OCamlUtils.oget p.argty) in
        let env =
          Env.update (Env.map usedValEnv (fun v -> BddFunc.eval_value v)) p.arg bddf
        in
        let bddf = BddFunc.eval env p.body in
        (match bddf with
        | BBool bdd ->
          let mtbdd = BddFunc.wrap_mtbdd bdd in
          bddfunc_cache := ExpEnvMap.add lookupVal mtbdd !bddfunc_cache;
          mtbdd
        | _ -> failwith "impossible")
      | Some bddf -> bddf
    in
    let f1_fun v = apply c_env1 f1 v in
    let f2_fun v = apply c_env2 f2 v in
    vmap
      (BddMap.map_ite
         ~op_key1:(f1.body, env1)
         ~op_key2:(f2.body, env2)
         mtbdd
         f1_fun
         f2_fun
         m)
  | MForAll, [{ v = VClosure (c_env1, f1) }; { v = VClosure (c_env2, f2) }; { v = VMap m }]
    ->
    (* Compute the closure of the function applied over the leafs *)
    let seen2 = BatSet.PSet.singleton ~cmp:Var.compare f2.arg in
    let env2 = build_env c_env2 (Syntax.free seen2 f2.body) in
    (* Likewise for the predicate, and create a cache entry *)
    let seen1 = Syntax.free (BatSet.PSet.singleton ~cmp:Var.compare f1.arg) f1.body in
    let usedValEnv = Env.filter c_env1.value (fun x _ -> BatSet.PSet.mem x seen1) in
    let lookupVal = f1.body, usedValEnv in
    let mtbdd =
      match ExpEnvMap.Exceptionless.find lookupVal !bddfunc_cache with
      | None ->
        let bddf = BddFunc.create_value (Nv_utils.OCamlUtils.oget f1.argty) in
        let env =
          Env.update (Env.map usedValEnv (fun v -> BddFunc.Value v)) f1.arg bddf
        in
        (* Compute BDD out of predicate *)
        let bddf = BddFunc.eval env f1.body in
        let bddf =
          match bddf with
          | Value v -> BddFunc.eval_value v
          | _ -> bddf
        in
        (match bddf with
        | BBool bdd ->
          let mtbdd = BddFunc.wrap_mtbdd bdd in
          bddfunc_cache := ExpEnvMap.add lookupVal mtbdd !bddfunc_cache;
          mtbdd
        | BMap mtbdd ->
          let mtbdd = BddFunc.value_mtbdd_bool_mtbdd (fst mtbdd) in
          bddfunc_cache := ExpEnvMap.add lookupVal mtbdd !bddfunc_cache;
          mtbdd
        | _ -> failwith "impossible")
      | Some bddf -> bddf
    in
    let f v = apply c_env2 f2 v in
    BddMap.forall ~op_key:(f2.body, env2) mtbdd f m
  | _, _ ->
    failwith (Printf.sprintf "bad operator application: %s" (Printing.op_to_string op))

and apply env f v = interp_exp (update_value env f.arg v) f.body

let interp e = interp_exp empty_env e
let interp = MemoizeExp.memoize ~size:1000 interp

let interp_closure cl (args : value list) =
  let exp = Syntax.apply_closure cl args in
  interp exp
;;
