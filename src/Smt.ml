open Unsigned
open Syntax
open Z3

type smt_env = {solver: Z3.Solver.solver; ctx: Z3.context}

let create_fresh descr s =
  Printf.sprintf "%s-%s" descr (Var.fresh s |> Var.to_string)

let create_name descr n = Printf.sprintf "%s-%s" descr (Var.to_string n)

let mk_int_u32 ctx i =
  Expr.mk_numeral_string ctx (UInt32.to_string i)
    (Arithmetic.Integer.mk_sort ctx)

let mk_int ctx i = mk_int_u32 ctx (UInt32.of_int i)

let mk_bool ctx b = Boolean.mk_val ctx b

let add_f ctx =
  let zero = mk_int ctx 0 in
  Arithmetic.mk_add ctx [zero; zero] |> Expr.get_func_decl

let sub_f ctx =
  let zero = mk_int ctx 0 in
  Arithmetic.mk_sub ctx [zero; zero] |> Expr.get_func_decl

let lt_f ctx =
  let zero = mk_int ctx 0 in
  Arithmetic.mk_lt ctx zero zero |> Expr.get_func_decl

let le_f ctx =
  let zero = mk_int ctx 0 in
  Arithmetic.mk_le ctx zero zero |> Expr.get_func_decl

let eq_f ctx e = Boolean.mk_eq ctx e e |> Expr.get_func_decl

let and_f ctx =
  let tru = mk_bool ctx true in
  Boolean.mk_and ctx [tru; tru] |> Expr.get_func_decl

let or_f ctx =
  let tru = mk_bool ctx true in
  Boolean.mk_or ctx [tru; tru] |> Expr.get_func_decl

let not_f ctx =
  let tru = mk_bool ctx true in
  Boolean.mk_not ctx tru |> Expr.get_func_decl

let ite_f ctx e2 e3 =
  let tru = mk_bool ctx true in
  Boolean.mk_ite ctx tru e2 e3 |> Expr.get_func_decl

let peel ctx e = Z3Array.mk_select ctx e (mk_int ctx 0)

let add solver args =
  (* List.iter (fun e -> Printf.printf "(assert %s)\n" (Expr.to_string e)) args; *)
  Solver.add solver args

let rec ty_to_smtlib (ty: ty) : string =
  match ty with
  | TVar {contents= Link t} -> ty_to_smtlib t
  | TBool -> "Bool"
  | TInt i -> Printf.sprintf "_ BitVec %s" (UInt32.to_string i)
  | TTuple ts -> (
    match ts with
    | [] -> Console.error "empty tuple"
    | [t] -> ty_to_smtlib t
    | t :: ts ->
        Printf.sprintf "Pair (%s) (%s)" (ty_to_smtlib t)
          (ty_to_smtlib (TTuple ts)) )
  | TOption ty -> Printf.sprintf "Option (%s)" (ty_to_smtlib ty)
  | TMap _ -> Console.error "unimplemented"
  | TVar _ | QVar _ | TArrow _ ->
      Console.error
        (Printf.sprintf "internal error (ty_to_smtlib): %s"
           (Printing.ty_to_string ty))

let mk_array_sort ctx sort =
  Z3Array.mk_sort ctx (Arithmetic.Integer.mk_sort ctx) sort

let rec ty_to_sort ctx (ty: ty) : Z3.Sort.sort =
  match ty with
  | TVar {contents= Link t} -> ty_to_sort ctx t
  | TInt _ -> Z3.Arithmetic.Integer.mk_sort ctx
  | TOption t ->
      let issome = Z3.Symbol.mk_string ctx "is-some" in
      let isnone = Z3.Symbol.mk_string ctx "is-none" in
      let v = Z3.Symbol.mk_string ctx "val" in
      let ty = ty_to_sort ctx t in
      let some =
        Z3.Datatype.mk_constructor_s ctx "some" issome [v] [Some ty] [0]
      in
      let none = Z3.Datatype.mk_constructor_s ctx "none" isnone [] [] [] in
      let name = Printf.sprintf "Option%s" (Z3.Sort.to_string ty) in
      Z3.Datatype.mk_sort_s ctx name [none; some]
  | TBool -> Z3.Boolean.mk_sort ctx
  | TTuple ts ->
      let len = List.length ts in
      let istup = Z3.Symbol.mk_string ctx "is-pair" in
      let getters =
        List.mapi
          (fun i _ -> Z3.Symbol.mk_string ctx (Printf.sprintf "proj%d" i))
          ts
      in
      let tys = List.map (ty_to_sort ctx) ts in
      let tyso = List.map (fun x -> Some x) tys in
      let is = List.map (fun _ -> 0) ts in
      let some =
        Z3.Datatype.mk_constructor_s ctx
          (Printf.sprintf "mk-pair%d" len)
          istup getters tyso is
      in
      let name =
        List.fold_left (fun acc ty -> acc ^ Sort.to_string ty) "" tys
      in
      let name = Printf.sprintf "Pair%d%s" (List.length ts) name in
      Z3.Datatype.mk_sort_s ctx name [some]
  | TMap (i, t) -> mk_array_sort ctx (ty_to_sort ctx t)
  | TVar _ | QVar _ | TArrow _ -> Console.error "internal error (ty_to_sort)"

let mk_array ctx value = Z3Array.mk_const_array ctx (ty_to_sort ctx tint) value

type array_info =
  {f: Sort.sort -> Sort.sort; make: Expr.expr -> Expr.expr; lift: bool}

let rec encode_exp_z3 descr env arr (e: exp) =
  (* Printf.printf "expr: %s\n" (Printing.exp_to_string e) ; *)
  match e.e with
  | EVar x ->
      let sort = ty_to_sort env.ctx (oget e.ety) |> arr.f in
      Z3.Expr.mk_const_s env.ctx (create_name descr x) sort
  | EVal v -> encode_value_z3 descr env arr v
  | EOp (op, es) -> (
    match (op, es) with
    | And, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (and_f env.ctx) [e1; e2]
          else fun e1 e2 -> Boolean.mk_and env.ctx [e1; e2]
        in
        encode_op_z3 descr env f arr es
    | Or, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (or_f env.ctx) [e1; e2]
          else fun e1 e2 -> Boolean.mk_or env.ctx [e1; e2]
        in
        encode_op_z3 descr env f arr es
    | Not, _ ->
        let ze = List.hd es |> encode_exp_z3 descr env arr in
        if arr.lift then Z3Array.mk_map env.ctx (not_f env.ctx) [ze]
        else Boolean.mk_not env.ctx ze
    | UAdd, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (add_f env.ctx) [e1; e2]
          else fun e1 e2 -> Arithmetic.mk_add env.ctx [e1; e2]
        in
        encode_op_z3 descr env f arr es
    | USub, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (sub_f env.ctx) [e1; e2]
          else fun e1 e2 -> Arithmetic.mk_sub env.ctx [e1; e2]
        in
        encode_op_z3 descr env f arr es
    | UEq, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (eq_f env.ctx (peel env.ctx e1)) [e1; e2]
          else Boolean.mk_eq env.ctx
        in
        encode_op_z3 descr env f arr es
    | ULess, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (lt_f env.ctx) [e1; e2]
          else Arithmetic.mk_lt env.ctx
        in
        encode_op_z3 descr env f arr es
    | ULeq, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (le_f env.ctx) [e1; e2]
          else Arithmetic.mk_le env.ctx
        in
        encode_op_z3 descr env f arr es
    | MCreate, [_; e2] ->
        if arr.lift then Console.error "not supported yet" ;
        let e2 = encode_exp_z3 descr env arr e2 in
        let sort = Arithmetic.Integer.mk_sort env.ctx |> arr.f in
        Z3Array.mk_const_array env.ctx sort e2
    | MGet, [e1; e2] ->
        if arr.lift then Console.error "not supported yet" ;
        let e1 = encode_exp_z3 descr env arr e1 in
        let e2 = encode_exp_z3 descr env arr e2 in
        Z3Array.mk_select env.ctx e1 e2
    | MSet, [e1; e2; e3] ->
        if arr.lift then Console.error "not supported yet" ;
        let e1 = encode_exp_z3 descr env arr e1 in
        let e2 = encode_exp_z3 descr env arr e2 in
        let e3 = encode_exp_z3 descr env arr e3 in
        Z3Array.mk_store env.ctx e1 e2 e3
    | MMap, [{e= EFun {arg= x; argty= ty1; resty= ty2; body= e1}}; e2] ->
        let arr2 =
          { f= (fun s -> mk_array_sort env.ctx (arr.f s))
          ; make= (fun e -> mk_array env.ctx (arr.make e))
          ; lift= true }
        in
        let e1 = encode_exp_z3 descr env arr2 e1 in
        let e2 = encode_exp_z3 descr env arr e2 in
        let x = create_name descr x in
        let xty = ty_to_sort env.ctx (oget ty1) |> arr2.f in
        let xarg = Expr.mk_const_s env.ctx x xty in
        Solver.add env.solver [Boolean.mk_eq env.ctx xarg e2] ;
        e1
        (* let sort1 = ty_to_sort env.ctx (oget ty1) in
        let e1 = encode_exp_z3 descr env e1 in
        let e2 = encode_exp_z3 descr env e2 in
        let name = create_fresh descr "map" in
        let x = create_name descr x in
        let x = Symbol.mk_string env.ctx x in
        let xarg = Expr.mk_const env.ctx x (ty_to_sort env.ctx (oget ty1)) in
        let f = FuncDecl.mk_func_decl_s env.ctx name [sort1] sort1 in
        let app = Expr.mk_app env.ctx f [xarg] in
        let body = Boolean.mk_eq env.ctx app e1 in
        (* note: do not use mk_forall, appears to be broken *)
        let q =
          Quantifier.mk_forall_const env.ctx [xarg] body None [] [] None None
          |> Quantifier.expr_of_quantifier
        in
        add env.solver [q] ;
        Z3Array.mk_map env.ctx f [e2] *)
    | ( MMerge
      , [ { e=
              EFun
                { arg= x
                ; argty= ty1
                ; body= {e= EFun {arg= y; argty= ty2; body= e1}} } }
        ; e2
        ; e3 ] ) ->
        let arr2 =
          { f= (fun s -> mk_array_sort env.ctx (arr.f s))
          ; make= (fun e -> mk_array env.ctx (arr.make e))
          ; lift= true }
        in
        let e1 = encode_exp_z3 descr env arr2 e1 in
        let e2 = encode_exp_z3 descr env arr e2 in
        let e3 = encode_exp_z3 descr env arr e3 in
        let x = create_name descr x in
        let xty = ty_to_sort env.ctx (oget ty1) |> arr2.f in
        let xarg = Expr.mk_const_s env.ctx x xty in
        let y = create_name descr y in
        let yty = ty_to_sort env.ctx (oget ty2) |> arr2.f in
        let yarg = Expr.mk_const_s env.ctx y yty in
        Solver.add env.solver [Boolean.mk_eq env.ctx xarg e2] ;
        Solver.add env.solver [Boolean.mk_eq env.ctx yarg e3] ;
        e1
        (* let sort1 = ty_to_sort env.ctx (oget ty1) in
        let e1 = encode_exp_z3 descr env e1 in
        let e2 = encode_exp_z3 descr env e2 in
        let e3 = encode_exp_z3 descr env e3 in
        let name = create_fresh descr "combine" in
        let x = create_name descr x in
        let x = Symbol.mk_string env.ctx x in
        let y = create_name descr y in
        let y = Symbol.mk_string env.ctx y in
        let f = FuncDecl.mk_func_decl_s env.ctx name [sort1; sort1] sort1 in
        let xarg = Expr.mk_const env.ctx x (ty_to_sort env.ctx (oget ty1)) in
        let yarg = Expr.mk_const env.ctx y (ty_to_sort env.ctx (oget ty2)) in
        let app = Expr.mk_app env.ctx f [xarg; yarg] in
        let body = Boolean.mk_eq env.ctx app e1 in
        let q =
          Quantifier.mk_forall_const env.ctx [xarg; yarg] body None [] [] None
            None
          |> Quantifier.expr_of_quantifier
        in
        add env.solver [q] ;
        Z3Array.mk_map env.ctx f [e2; e3] *)
    | MFilter, _ -> Console.error "unsupported: filter in smt encoding"
    | _ -> Console.error "internal error (encode_exp_z3)" )
  | EIf (e1, e2, e3) ->
      let ze1 = encode_exp_z3 descr env arr e1 in
      let ze2 = encode_exp_z3 descr env arr e2 in
      let ze3 = encode_exp_z3 descr env arr e3 in
      if arr.lift then
        Z3Array.mk_map env.ctx
          (ite_f env.ctx (peel env.ctx ze2) (peel env.ctx ze3))
          [ze1; ze2; ze3]
      else Boolean.mk_ite env.ctx ze1 ze2 ze3
  | ELet (x, e1, e2) ->
      let xstr = create_name descr x in
      let za =
        Expr.mk_const_s env.ctx xstr (oget e.ety |> ty_to_sort env.ctx |> arr.f)
      in
      let ze1 = encode_exp_z3 descr env arr e1 in
      let ze2 = encode_exp_z3 descr env arr e2 in
      add env.solver [Boolean.mk_eq env.ctx za ze1] ;
      ze2
  | ETuple es -> (
      let ty = oget e.ety in
      match ty with
      | TTuple ts ->
          let pair_sort = ty_to_sort env.ctx ty in
          let zes = List.map (encode_exp_z3 descr env arr) es in
          let f = Datatype.get_constructors pair_sort |> List.hd in
          if arr.lift then Z3Array.mk_map env.ctx f zes
          else Expr.mk_app env.ctx f zes
      | _ -> Console.error "internal error (encode_exp_z3)" )
  | ESome e1 ->
      let ty = oget e.ety |> ty_to_sort env.ctx in
      let f = List.nth (Datatype.get_constructors ty) 1 in
      let ze = encode_exp_z3 descr env arr e1 in
      if arr.lift then Z3Array.mk_map env.ctx f [ze]
      else Expr.mk_app env.ctx f [ze]
  | EMatch (e, bs) ->
      let name = create_fresh descr "match" in
      let za =
        Expr.mk_const_s env.ctx name (oget e.ety |> ty_to_sort env.ctx |> arr.f)
      in
      let ze1 = encode_exp_z3 descr env arr e in
      add env.solver [Boolean.mk_eq env.ctx za ze1] ;
      encode_branches_z3 descr env arr za bs (oget e.ety)
  | ETy (e, ty) -> encode_exp_z3 descr env arr e
  | EFun _ | EApp _ -> Console.error "function in smt encoding"

and encode_op_z3 descr env f arr es =
  match es with
  | [] -> Console.error "internal error (encode_op)"
  | [e] -> encode_exp_z3 descr env arr e
  | e :: es ->
      let ze1 = encode_exp_z3 descr env arr e in
      let ze2 = encode_op_z3 descr env f arr es in
      f ze1 ze2

and encode_branches_z3 descr env arr name bs (t: ty) =
  match List.rev bs with
  | [] -> Console.error "internal error (encode_branches)"
  | (p, e) :: bs ->
      let ze = encode_exp_z3 descr env arr e in
      (* we make the last branch fire no matter what *)
      let _ = encode_pattern_z3 descr env arr name p t in
      encode_branches_aux_z3 descr env arr name (List.rev bs) ze t

(* I'm assuming here that the cases are exhaustive *)
and encode_branches_aux_z3 descr env arr name bs accze (t: ty) =
  match bs with
  | [] -> accze
  | (p, e) :: bs ->
      let ze = encode_exp_z3 descr env arr e in
      let zp = encode_pattern_z3 descr env arr name p t in
      let ze =
        if arr.lift then
          Z3Array.mk_map env.ctx
            (ite_f env.ctx (peel env.ctx ze) (peel env.ctx accze))
            [zp; ze; accze]
        else Boolean.mk_ite env.ctx zp ze accze
      in
      encode_branches_aux_z3 descr env arr name bs ze t

and encode_pattern_z3 descr env arr zname p (t: ty) =
  let ty = Typing.get_inner_type t in
  match (p, ty) with
  | PWild, _ ->
      if arr.lift then arr.make (mk_bool env.ctx true)
      else Boolean.mk_true env.ctx
  | PVar x, t ->
      let local_name = create_name descr x in
      let za =
        Expr.mk_const_s env.ctx local_name (ty_to_sort env.ctx t |> arr.f)
      in
      add env.solver [Boolean.mk_eq env.ctx za zname] ;
      if arr.lift then arr.make (mk_bool env.ctx true)
      else Boolean.mk_true env.ctx
  | PBool b, TBool ->
      if arr.lift then
        let a = arr.make (mk_bool env.ctx b) in
        Z3Array.mk_map env.ctx (eq_f env.ctx (peel env.ctx zname)) [zname; a]
      else Boolean.mk_eq env.ctx zname (Boolean.mk_val env.ctx b)
  | PUInt32 i, TInt _ ->
      if arr.lift then
        let a = arr.make (mk_int_u32 env.ctx i) in
        Z3Array.mk_map env.ctx (eq_f env.ctx (peel env.ctx zname)) [zname; a]
      else
        let const = mk_int_u32 env.ctx i in
        Boolean.mk_eq env.ctx zname const
  | PTuple ps, TTuple ts -> (
    match (ps, ts) with
    | [p], [t] -> encode_pattern_z3 descr env arr zname p t
    | ps, ts ->
        let znames =
          List.mapi
            (fun i t ->
              let sort = ty_to_sort env.ctx t |> arr.f in
              ( Expr.mk_const_s env.ctx
                  (Printf.sprintf "elem%d" i |> create_fresh descr)
                  sort
              , sort
              , t ) )
            ts
        in
        let tup_sort = ty_to_sort env.ctx ty in
        let fs = Datatype.get_accessors tup_sort |> List.concat in
        List.combine znames fs
        |> List.iter (fun ((elem, _, _), f) ->
               let e =
                 if arr.lift then Z3Array.mk_map env.ctx f [zname]
                 else Expr.mk_app env.ctx f [zname]
               in
               add env.solver [Boolean.mk_eq env.ctx elem e] ) ;
        let matches =
          List.map
            (fun (p, (zname, _, ty)) ->
              encode_pattern_z3 descr env arr zname p ty )
            (List.combine ps znames)
        in
        let f acc e =
          if arr.lift then Z3Array.mk_map env.ctx (and_f env.ctx) [acc; e]
          else Boolean.mk_and env.ctx [acc; e]
        in
        let b = mk_bool env.ctx true in
        let base = if arr.lift then arr.make b else b in
        List.fold_left f base matches )
  | POption None, TOption _ ->
      let opt_sort = ty_to_sort env.ctx t in
      let f = Datatype.get_recognizers opt_sort |> List.hd in
      if arr.lift then Z3Array.mk_map env.ctx f [zname]
      else Expr.mk_app env.ctx f [zname]
  | POption (Some p), TOption t ->
      let new_name = create_fresh descr "option" in
      let za =
        Expr.mk_const_s env.ctx new_name (ty_to_sort env.ctx t |> arr.f)
      in
      let opt_sort = ty_to_sort env.ctx ty in
      let get_val =
        Datatype.get_accessors opt_sort |> List.concat |> List.hd
      in
      let is_some = List.nth (Datatype.get_recognizers opt_sort) 1 in
      let e =
        if arr.lift then Z3Array.mk_map env.ctx get_val [zname]
        else Expr.mk_app env.ctx get_val [zname]
      in
      add env.solver [Boolean.mk_eq env.ctx za e] ;
      let zp = encode_pattern_z3 descr env arr za p t in
      if arr.lift then
        let e = Z3Array.mk_map env.ctx is_some [zname] in
        Z3Array.mk_map env.ctx (and_f env.ctx) [e; zp]
      else Boolean.mk_and env.ctx [Expr.mk_app env.ctx is_some [zname]; zp]
  | _ ->
      Console.error
        (Printf.sprintf "internal error (encode_pattern): (%s, %s)"
           (Printing.pattern_to_string p)
           (Printing.ty_to_string (Typing.get_inner_type t)))

and encode_value_z3 descr env arr (v: Syntax.value) =
  match v.v with
  | VBool b ->
      let b = mk_bool env.ctx b in
      if arr.lift then arr.make b else b
  | VUInt32 i ->
      let i = mk_int_u32 env.ctx i in
      if arr.lift then arr.make i else i
  | VTuple vs -> (
    match oget v.vty with
    | TTuple ts ->
        let pair_sort = ty_to_sort env.ctx (oget v.vty) |> arr.f in
        let zes = List.map (encode_value_z3 descr env arr) vs in
        let f = Datatype.get_constructors pair_sort |> List.hd in
        if arr.lift then Z3Array.mk_map env.ctx f zes
        else Expr.mk_app env.ctx f zes
    | _ -> Console.error "internal error (encode_value)" )
  | VOption None ->
      let opt_sort = ty_to_sort env.ctx (oget v.vty) in
      let f = Datatype.get_constructors opt_sort |> List.hd in
      let e = Expr.mk_app env.ctx f [] in
      if arr.lift then arr.make e else e
  | VOption (Some v1) ->
      let opt_sort = ty_to_sort env.ctx (oget v.vty) in
      let f = List.nth (Datatype.get_constructors opt_sort) 1 in
      let zv = encode_value_z3 descr env arr v1 in
      if arr.lift then Z3Array.mk_map env.ctx f [zv]
      else Expr.mk_app env.ctx f [zv]
  | VClosure _ -> Console.error "internal error (closure in smt)"
  | VMap _ -> Console.error "unimplemented: map"

let encode_z3_merge str env e =
  match e.e with
  | EFun
      { arg= node
      ; argty= nodety
      ; body=
          { e=
              EFun
                { arg= x
                ; argty= xty
                ; body= {e= EFun {arg= y; argty= yty; body= exp}} } } } ->
      let nodestr =
        Expr.mk_const_s env.ctx (create_name str node)
          (ty_to_sort env.ctx (oget nodety))
      in
      let xstr =
        Expr.mk_const_s env.ctx (create_name str x)
          (ty_to_sort env.ctx (oget xty))
      in
      let ystr =
        Expr.mk_const_s env.ctx (create_name str y)
          (ty_to_sort env.ctx (oget yty))
      in
      let name = Printf.sprintf "%s-result" str in
      let result =
        Expr.mk_const_s env.ctx name (oget exp.ety |> ty_to_sort env.ctx)
      in
      let e =
        Expr.simplify
          (encode_exp_z3 str env
             {f= (fun x -> x); make= (fun e -> e); lift= false}
             exp)
          None
      in
      add env.solver [Boolean.mk_eq env.ctx result e] ;
      (result, nodestr, xstr, ystr)
  | _ -> Console.error "internal error"

let encode_z3_trans str env e =
  match e.e with
  | EFun
      { arg= edge
      ; argty= edgety
      ; body= {e= EFun {arg= x; argty= xty; body= exp}} } ->
      let edgestr =
        Expr.mk_const_s env.ctx (create_name str edge)
          (ty_to_sort env.ctx (oget edgety))
      in
      let xstr =
        Expr.mk_const_s env.ctx (create_name str x)
          (ty_to_sort env.ctx (oget xty))
      in
      let name = Printf.sprintf "%s-result" str in
      let result =
        Expr.mk_const_s env.ctx name (oget exp.ety |> ty_to_sort env.ctx)
      in
      let e =
        Expr.simplify
          (encode_exp_z3 str env
             {f= (fun x -> x); make= (fun e -> e); lift= false}
             exp)
          None
      in
      add env.solver [Boolean.mk_eq env.ctx result e] ;
      (result, edgestr, xstr)
  | _ -> Console.error "internal error"

let encode_z3_init str env e =
  match e.e with
  | EFun {arg= node; argty= nodety; body= e} ->
      let nodestr =
        Expr.mk_const_s env.ctx (create_name str node)
          (ty_to_sort env.ctx (oget nodety))
      in
      let name = Printf.sprintf "%s-result" str in
      let result =
        Expr.mk_const_s env.ctx name (oget e.ety |> ty_to_sort env.ctx)
      in
      let e =
        Expr.simplify
          (encode_exp_z3 str env
             {f= (fun x -> x); make= (fun e -> e); lift= false}
             e)
          None
      in
      add env.solver [Boolean.mk_eq env.ctx result e] ;
      (result, nodestr)
  | _ -> Console.error "internal error"

module NodeMap = Map.Make (struct
  type t = int

  let compare = compare
end)

module EdgeMap = Map.Make (struct
  type t = UInt32.t * UInt32.t

  let compare (a, b) (c, d) =
    let cmp = UInt32.compare a c in
    if cmp <> 0 then cmp else UInt32.compare b d
end)

let cfg = [("model_validate", "true")]

let encode_z3 (ds: declarations) : smt_env =
  Var.reset () ;
  let ctx = Z3.mk_context cfg in
  let t1 = Tactic.mk_tactic ctx "simplify" in
  let t2 = Tactic.mk_tactic ctx "propagate-values" in
  let t3 = Tactic.mk_tactic ctx "bit-blast" in
  let t4 = Tactic.mk_tactic ctx "smt" in
  let t =
    Tactic.and_then ctx t1
      (Tactic.and_then ctx t2 (Tactic.and_then ctx t3 t4 []) [])
      []
  in
  let solver = Z3.Solver.mk_solver_t ctx t in
  (* let solver = Z3.Solver.mk_solver ctx None in *)
  let env = {solver; ctx} in
  let emerge, etrans, einit, nodes, edges, aty =
    match
      ( get_merge ds
      , get_trans ds
      , get_init ds
      , get_nodes ds
      , get_edges ds
      , get_attr_type ds )
    with
    | Some emerge, Some etrans, Some einit, Some n, Some es, Some aty ->
        (emerge, etrans, einit, n, es, aty)
    | _ ->
        Console.error
          "missing definition of nodes, edges, merge, trans or init"
  in
  (* map each node to the init result variable *)
  let init_map = ref NodeMap.empty in
  for i = 0 to UInt32.to_int nodes - 1 do
    let init, n = encode_z3_init (Printf.sprintf "init-%d" i) env einit in
    add env.solver [Boolean.mk_eq env.ctx n (mk_int ctx i)] ;
    init_map := NodeMap.add i init !init_map
  done ;
  (* map each edge to transfer function result *)
  let incoming_map = ref NodeMap.empty in
  let trans_map = ref EdgeMap.empty in
  let trans_input_map = ref EdgeMap.empty in
  List.iter
    (fun (i, j) ->
      ( try
          let idxs = NodeMap.find (UInt32.to_int j) !incoming_map in
          incoming_map :=
            NodeMap.add (UInt32.to_int j) ((i, j) :: idxs) !incoming_map
        with _ ->
          incoming_map := NodeMap.add (UInt32.to_int j) [(i, j)] !incoming_map
      ) ;
      let trans, e, x =
        encode_z3_trans
          (Printf.sprintf "trans-%d-%d" (UInt32.to_int i) (UInt32.to_int j))
          env etrans
      in
      trans_input_map := EdgeMap.add (i, j) x !trans_input_map ;
      let ie = mk_int_u32 env.ctx i in
      let je = mk_int_u32 env.ctx j in
      let pair_sort =
        ty_to_sort env.ctx
          (TTuple [TInt (UInt32.of_int 32); TInt (UInt32.of_int 32)])
      in
      let f = Datatype.get_constructors pair_sort |> List.hd in
      add env.solver [Boolean.mk_eq env.ctx e (Expr.mk_app env.ctx f [ie; je])] ;
      trans_map := EdgeMap.add (i, j) trans !trans_map )
    edges ;
  (* compute the labelling as the merge of all inputs *)
  let labelling = ref NodeMap.empty in
  for i = 0 to UInt32.to_int nodes - 1 do
    let init = NodeMap.find i !init_map in
    let in_edges = try NodeMap.find i !incoming_map with Not_found -> [] in
    let idx = ref 0 in
    let merged =
      List.fold_left
        (fun acc (x, y) ->
          incr idx ;
          let trans = EdgeMap.find (x, y) !trans_map in
          let str = Printf.sprintf "merge-%d-%d" i !idx in
          let merge_result, n, x, y = encode_z3_merge str env emerge in
          add solver [Boolean.mk_eq ctx trans x] ;
          add solver [Boolean.mk_eq ctx acc y] ;
          add solver [Boolean.mk_eq ctx n (mk_int env.ctx i)] ;
          merge_result )
        init in_edges
    in
    let l =
      Expr.mk_const_s ctx (Printf.sprintf "label-%d" i) (ty_to_sort ctx aty)
    in
    add solver [Boolean.mk_eq ctx l merged] ;
    labelling := NodeMap.add i l !labelling
  done ;
  (* Propagate labels across edges outputs *)
  EdgeMap.iter
    (fun (i, j) x ->
      let label = NodeMap.find (UInt32.to_int i) !labelling in
      add solver [Boolean.mk_eq ctx label x] )
    !trans_input_map ;
  env

let rec z3_to_exp (e: Expr.expr) : Syntax.exp option =
  try
    let i = UInt32.of_string (Expr.to_string e) in
    Some (EVal (VUInt32 i |> value) |> exp)
  with _ ->
    try
      let f = Expr.get_func_decl e in
      let es = Expr.get_args e in
      let name = FuncDecl.get_name f |> Symbol.to_string in
      match name with
      | "true" -> Some (EVal (VBool true |> value) |> exp)
      | "false" -> Some (EVal (VBool false |> value) |> exp)
      | "some" -> (
          let e = z3_to_exp (List.hd es) in
          match e with None -> None | Some e -> Some (ESome e |> exp) )
      | "none" -> Some (EVal (VOption None |> value) |> exp)
      | _ ->
          if String.length name >= 7 && String.sub name 0 7 = "mk-pair" then
            let es = List.map z3_to_exp es in
            if
              List.exists
                (fun e -> match e with None -> true | Some _ -> false)
                es
            then None
            else Some (ETuple (List.map oget es) |> exp)
          else None
    with _ -> None

type smt_result = Unsat | Sat of exp option NodeMap.t | Unknown

let solve ds =
  let num_nodes, aty =
    match (get_nodes ds, get_attr_type ds) with
    | Some n, Some aty -> (n, aty)
    | _ -> Console.error "internal error (encode)"
  in
  let env = encode_z3 ds in
  (* print_endline (Solver.to_string env.solver) ; *)
  let q = Solver.check env.solver [] in
  match q with
  | UNSATISFIABLE -> Unsat
  | UNKNOWN -> Unknown
  | SATISFIABLE ->
      let m = Solver.get_model env.solver in
      match m with
      | None -> Console.error "internal error (encode)"
      | Some m ->
          (* print_endline (Model.to_string m) ; *)
          let map = ref NodeMap.empty in
          for i = 0 to UInt32.to_int num_nodes - 1 do
            let l =
              Expr.mk_const_s env.ctx
                (Printf.sprintf "label-%d" i)
                (ty_to_sort env.ctx aty)
            in
            let e = Model.eval m l true |> oget in
            let e = z3_to_exp e in
            map := NodeMap.add i e !map
          done ;
          Sat !map
