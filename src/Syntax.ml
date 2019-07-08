(* Abstract syntax of SRP attribute processing expressions *)
open Cudd
open Hashcons
open RecordUtils

(* indices into maps or map sizes must be static constants *)
type index = int

type node = int
[@@deriving eq, ord, show]

type edge = node * node
[@@deriving eq, ord, show]

type bitwidth = int
[@@deriving eq, ord, show]

(* see:  http://okmij.org/ftp/ML/generalization.html *)
type level = int
[@@deriving ord, eq]

type var = Var.t
[@@deriving ord, eq]

type tyname = Var.t
[@@deriving ord, eq]

type ty =
  | TVar of tyvar ref
  | QVar of tyname
  | TUnit
  | TBool
  | TInt of bitwidth
  | TArrow of ty * ty
  | TTuple of ty list
  | TOption of ty
  | TMap of ty * ty
  | TRecord of ty StringMap.t
  | TNode
  | TEdge
[@@deriving ord, eq]

and tyvar = Unbound of tyname * level | Link of ty

type op =
  | And
  | Or
  | Not
  | Eq
  | UAdd of bitwidth
  | USub of bitwidth
  | ULess of bitwidth
  | ULeq of bitwidth
  | NLess
  | NLeq
  | AtMost of int
  | MCreate
  | MGet
  | MSet
  | MMap
  | MMapFilter
  | MMerge
[@@deriving show, ord, eq]

type pattern =
  | PWild
  | PVar of var
  | PUnit
  | PBool of bool
  | PInt of Integer.t
  | PTuple of pattern list
  | POption of pattern option
  | PRecord of pattern StringMap.t
  | PNode of node
  | PEdge of pattern * pattern
[@@deriving ord, eq]

module Pat =
struct
  type t = pattern

  let rec isConcretePat p =
    match p with
    | PInt _ | PBool _ | PNode _ | POption None -> true
    | PEdge (p1, p2) -> isConcretePat p1 && isConcretePat p2
    | POption (Some p) -> isConcretePat p
    | PTuple ps ->
      BatList.for_all (isConcretePat) ps
    | _ -> false

  let rec compare p1 p2 =
    match p1, p2 with
    | PInt n1, PInt n2 ->
      Pervasives.compare n1 n2
    | PBool b1, PBool b2 ->
      Pervasives.compare b1 b2
    | PNode n1, PNode n2 ->
      Pervasives.compare n1 n2
    | PEdge (p1, p2), PEdge (p1', p2') ->
      Pervasives.compare (p1, p2) (p1', p2')
    | POption p1, POption p2 ->
      Pervasives.compare p1 p2
    | PTuple ps1, PTuple ps2 ->
      BatList.fold_left2 (fun b p1 p2 ->
          if b = 0 then
            begin
              let c = compare p1 p2 in
              if (c = 0) then b
              else c
            end
          else b) 0 ps1 ps2
    | _, _ -> failwith "No comparison between non-concrete patterns"
end

module PatMap = BatMap.Make(Pat)

type v =
  | VUnit
  | VBool of bool
  | VInt of Integer.t
  | VMap of mtbdd
  | VTuple of value list
  | VOption of value option
  | VClosure of closure
  | VRecord of value StringMap.t
  | VNode of node
  | VEdge of edge
[@@deriving ord]

and value =
  {v: v;
   vty: ty option [@compare fun _ _ -> 0];
   vspan: Span.t [@compare fun _ _ -> 0];
   vtag: int [@compare fun _ _ -> 0];
   vhkey: int [@compare fun _ _ -> 0];
  }
[@@deriving ord]

and mtbdd = (value Mtbdd.t * ty)
    [@compare fun _ _ -> failwith "Map value comparison not supported"]
[@@deriving ord]

and e =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EFun of func
  | EApp of exp * exp
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | ESome of exp
  | EMatch of exp * branches
  | ETy of exp * ty
  | ERecord of exp StringMap.t
  | EProject of exp * string
[@@deriving ord]

and exp =
  {e: e;
   ety: ty option [@compare fun _ _ -> 0];
   espan: Span.t [@compare fun _ _ -> 0];
   etag: int [@compare fun _ _ -> 0];
   ehkey: int [@compare fun _ _ -> 0];
  }
[@@deriving ord]

and branches = { pmap              : exp PatMap.t;
                 plist             : (pattern * exp) list
               }

and func = {arg: var; argty: ty option; resty: ty option; body: exp}

and closure = (env * func)
    [@compare fun _ _ -> failwith "Map value comparison not supported"]
[@@deriving ord]

and env = {ty: ty Env.t; value: value Env.t}

and ty_or_exp = Ty of ty | Exp of exp

type declaration =
  | DLet of var * ty option * exp
  | DSymbolic of var * ty_or_exp
  | DATy of ty (* Declaration of the attribute type *)
  | DUserTy of var * ty (* Declaration of a record type *)
  | DMerge of exp
  | DTrans of exp
  | DInit of exp
  | DAssert of exp
  | DRequire of exp
  | DNodes of int
  | DEdges of (node * node) list

type declarations = declaration list

type network =
  { attr_type : ty;
    init : exp;
    trans : exp;
    merge : exp;
    assertion : exp option;
    symbolics : (var * ty_or_exp) list;
    defs : (var * ty option * exp) list;
    utys : (var * ty) list;
    requires : exp list;
    graph : AdjGraph.t;
  }

type srp_unfold =
  { srp_attr : ty;
    srp_constraints : exp AdjGraph.VertexMap.t;
    srp_labels : (var * ty) list AdjGraph.VertexMap.t;
    srp_symbolics : (var * ty_or_exp) list;
    srp_assertion : exp option;
    srp_requires : exp list;
    srp_graph : AdjGraph.t
  }

(** * Handling branches *)

type branchLookup = Found of exp | Rest of (pattern * exp) list
(* adding to the right place won't really work.. *)
let addBranch p e b =
  {b with plist = (p,e) :: b.plist}

(* f should preserve concrete patterns *)
let mapBranches f b =
  {pmap = PatMap.fold (fun p e pmap ->
       let p, e = f (p, e) in
       PatMap.add p e pmap) b.pmap PatMap.empty;
   plist = BatList.map f b.plist}

let iterBranches f b =
  PatMap.iter (fun p e -> f (p,e)) b.pmap;
  BatList.iter f b.plist

let foldBranches f acc b =
  BatList.fold_left (fun acc x -> f x acc)
    (PatMap.fold (fun p e acc -> f (p,e) acc) b.pmap acc) b.plist

let lookUpPat p b =
  match PatMap.Exceptionless.find p b.pmap with
  | Some e ->
    Found e
  | None ->
    Rest b.plist

let popBranch b =
  if PatMap.is_empty b.pmap then
    match b.plist with
    | [] -> raise Not_found
    | (p,e) :: bs ->
      (p,e), {b with plist = bs}
  else
    let (pe, pmap) = PatMap.pop b.pmap in
    (pe, {b with pmap = pmap})

let emptyBranch =
  { pmap = PatMap.empty;
    plist = []
  }

let isEmptyBranch b =
  PatMap.is_empty b.pmap && BatList.is_empty b.plist

let optimizeBranches b =
  let rec loop map lst =
    match lst with
    | [] -> {pmap = map; plist = []}
    | (p,e) :: lst' ->
      if Pat.isConcretePat p = true then
        loop (PatMap.add p e map) lst'
      else
        {pmap = map; plist = lst}
  in
  loop b.pmap b.plist

let branchToList b =
  (PatMap.fold (fun p e acc -> (p,e) :: acc) b.pmap b.plist)

let branchSize b =
  Printf.printf "%d\n" (PatMap.cardinal b.pmap)

(* structural printing *)
(* TODO: This should probably be its own file *)

let show_span (span: Span.t) =
  Printf.sprintf "(%d,%d)" span.start span.finish

let show_opt s o =
  match o with
  | None -> "None"
  | Some x -> Printf.sprintf "Some (%s)" (s x)

let show_list s ls =
  "[" ^ List.fold_left (fun acc x -> acc ^ "," ^ s x) "" ls ^ "]"

let show_record f prefix map =
  let str = StringMap.fold
      (fun l elt acc -> Printf.sprintf "%s; %s: %s" acc l (f elt))
      map ""
  in
  Printf.sprintf "%s { %s }" prefix str

let rec show_ty ty =
  match ty with
  | TVar tyvar -> (
      match !tyvar with
      | Unbound (name, _) ->
        Printf.sprintf "TVar (Unbound %s)" (Var.to_string name)
      | Link t -> Printf.sprintf "Link (%s)" (show_ty t) )
  | QVar name -> Printf.sprintf "QVar (%s)" (Var.to_string name)
  | TBool -> "TBool"
  | TInt _ -> "TInt"
  | TArrow (ty1, ty2) ->
    Printf.sprintf "TArrow (%s,%s)" (show_ty ty1) (show_ty ty2)
  | TTuple ts ->
    let str = show_list show_ty ts in
    Printf.sprintf "TTuple %s" str
  | TOption t -> Printf.sprintf "TOption (%s)" (show_ty t)
  | TMap (ty1, ty2) ->
    Printf.sprintf "TMap (%s,%s)" (show_ty ty1) (show_ty ty2)
  | TRecord map -> show_record show_ty "TRecord" map
  | TUnit -> "TUnit"
  | TNode -> "TNode"
  | TEdge -> "TEdge"


let rec show_exp ~show_meta e =
  if show_meta then
    Printf.sprintf "{e=%s; ety=%s; espan=%s; etag=%d; ehkey=%d}"
      (show_e ~show_meta e.e)
      (show_opt show_ty e.ety)
      (show_span e.espan) e.etag e.ehkey
  else
    Printf.sprintf "e=%s" (show_e ~show_meta e.e)

and show_e ~show_meta e =
  match e with
  | EVar x -> Printf.sprintf "EVar %s" (Var.to_string x)
  | EVal v -> Printf.sprintf "EVal (%s)" (show_value ~show_meta v)
  | EOp (op, es) ->
    Printf.sprintf "EOp (%s,%s)" (show_op op)
      (show_list (show_exp ~show_meta) es)
  | EFun f -> Printf.sprintf "EFun %s" (show_func ~show_meta f)
  | EApp (e1, e2) ->
    Printf.sprintf "EApp (%s,%s)" (show_exp ~show_meta e1) (show_exp ~show_meta e2)
  | EIf (e1, e2, e3) ->
    Printf.sprintf "EIf (%s,%s,%s)" (show_exp ~show_meta e1) (show_exp ~show_meta e2)
      (show_exp ~show_meta e3)
  | ELet (x, e1, e2) ->
    Printf.sprintf "ELet (%s,%s,%s)" (Var.to_string x)
      (show_exp ~show_meta e1) (show_exp ~show_meta e2)
  | ETuple es -> Printf.sprintf "ETuple %s" (show_list (show_exp ~show_meta) es)
  | ESome e -> Printf.sprintf "ESome (%s)" (show_exp ~show_meta e)
  | EMatch (e, bs) ->
    Printf.sprintf "EMatch (%s,%s)" (show_exp ~show_meta e)
      (show_list (show_branch ~show_meta) (branchToList bs))
  | ETy (e, ty) ->
    Printf.sprintf "ETy (%s,%s)" (show_exp ~show_meta e) (show_ty ty)
  | ERecord map ->
    show_record (show_exp ~show_meta) "ERecord" map
  | EProject (e, label) ->
    Printf.sprintf "%s.%s" (show_exp ~show_meta e) label

and show_func ~show_meta f =
  Printf.sprintf "{arg=%s; argty=%s; resty=%s; body=%s}"
    (Var.to_string f.arg)
    (show_opt show_ty f.argty)
    (show_opt show_ty f.resty)
    (show_exp ~show_meta f.body)

and show_branch ~show_meta (p, e) =
  Printf.sprintf "(%s,%s)" (show_pattern p) (show_exp ~show_meta e)

and show_pattern p =
  match p with
  | PWild -> "PWild"
  | PUnit -> "PUnit"
  | PVar x -> Printf.sprintf "PVar %s" (Var.to_string x)
  | PBool b -> Printf.sprintf "PBool %b" b
  | PInt n -> Printf.sprintf "PInt %s" (Integer.to_string n)
  | PTuple ps ->
    Printf.sprintf "PTuple %s" (show_list show_pattern ps)
  | POption None -> "POption None"
  | POption (Some p) ->
    Printf.sprintf "POption (Some %s)" (show_pattern p)
  | PRecord map ->
    show_record show_pattern "PRecord" map
  | PNode node ->
    Printf.sprintf "PNode %d" node
  | PEdge (p1, p2) ->
    Printf.sprintf "PEdge %s~%s" (show_pattern p1) (show_pattern p2)

and show_value ~show_meta v =
  if show_meta then
    Printf.sprintf "{e=%s; ety=%s; espan=%s; etag=%d; ehkey=%d}"
      (show_v ~show_meta v.v)
      (show_opt show_ty v.vty)
      (show_span v.vspan) v.vtag v.vhkey
  else
    Printf.sprintf "{v=%s;}"
      (show_v ~show_meta v.v)

and show_v ~show_meta v =
  match v with
  | VUnit -> "VUnit"
  | VBool b -> Printf.sprintf "VBool %b" b
  | VInt i -> Printf.sprintf "VInt %s" (Integer.to_string i)
  | VMap m -> "VMap <opaque>"
  | VTuple vs -> Printf.sprintf "VTuple %s" (show_list (show_value ~show_meta) vs)
  | VOption vo ->
    Printf.sprintf "VOption (%s)" (show_opt (show_value ~show_meta) vo)
  | VClosure c -> Printf.sprintf "VClosure %s" (show_closure ~show_meta c)
  | VRecord map -> show_record (show_value ~show_meta) "VRecord" map
  | VNode node -> Printf.sprintf "VNode %dn" node
  | VEdge (n1, n2) -> Printf.sprintf "VEdge %dn-%dn" n1 n2

and show_closure ~show_meta (e, f) =
  Printf.sprintf "{env=%s; func=%s}" (show_env ~show_meta e) (show_func ~show_meta f)

and show_env ~show_meta e =
  Printf.sprintf "{ty=%s; value=%s}"
    (Env.to_string show_ty e.ty)
    (Env.to_string (show_value ~show_meta) e.value)

(* equality / hashing *)

let equal_spans (s1: Span.t) (s2: Span.t) =
  s1.start = s2.start && s1.finish = s2.finish

let equal_opt e o1 o2 =
  match (o1, o2) with
  | None, None -> true
  | None, Some _ | Some _, None -> false
  | Some x, Some y -> e x y

let rec equal_lists eq_elts lst1 lst2 =
  match lst1, lst2 with
  | [], [] -> true
  | [], _ :: _ | _ :: _, [] -> false
  | t1 :: ts1, t2 :: ts2 -> eq_elts t1 t2 && equal_lists eq_elts ts1 ts2

let rec equal_tys ty1 ty2 =
  match (ty1, ty2) with
  | TBool, TBool
  | TInt _, TInt _
  | TNode, TNode
  | TEdge, TEdge -> true
  | TVar t1, TVar t2 -> (
      match (!t1, !t2) with
      | Unbound (n1, x1), Unbound (n2, x2) ->
        Var.equals n1 n2 && x1 = x2
      | Link t1, Link t2 -> equal_tys t1 t2
      | _ -> false )
  | QVar n1, QVar n2 -> Var.equals n1 n2
  | TArrow (t1, t2), TArrow (s1, s2) ->
    equal_tys t1 s1 && equal_tys t2 s2
  | TTuple ts1, TTuple ts2 -> equal_lists equal_tys ts1 ts2
  | TRecord map1, TRecord map2 -> StringMap.equal equal_tys map1 map2
  | TOption t1, TOption t2 -> equal_tys t1 t2
  | TMap (t1, t2), TMap (s1, s2) ->
    equal_tys t1 s1 && equal_tys t2 s2
  | _ -> false

let rec equal_values ~cmp_meta (v1: value) (v2: value) =
  let cfg = Cmdline.get_cfg () in
  let b =
    if cfg.hashcons then v1.vtag = v2.vtag
    else equal_vs ~cmp_meta v1.v v2.v
  in
  if cmp_meta then
    b
    && equal_opt equal_tys v1.vty v2.vty
    && equal_spans v1.vspan v2.vspan
  else b

and equal_vs ~cmp_meta v1 v2 =
  match (v1, v2) with
  | VBool b1, VBool b2 -> b1 = b2
  | VNode n1, VNode n2 -> n1 = n2
  | VEdge e1, VEdge e2 -> e1 = e2
  | VInt i1, VInt i2 -> Integer.equal i1 i2
  | VMap (m1, ty1), VMap (m2, ty2) ->
    Mtbdd.is_equal m1 m2 && equal_tys ty1 ty2
  | VTuple vs1, VTuple vs2 -> equal_lists ~cmp_meta vs1 vs2
  | VOption vo1, VOption vo2 -> (
      match (vo1, vo2) with
      | None, None -> true
      | None, Some _ -> false
      | Some _, None -> false
      | Some x, Some y -> equal_values ~cmp_meta x y )
  | VClosure (e1, f1), VClosure (e2, f2) ->
    let {ty= ty1; value= value1} = e1 in
    let {ty= ty2; value= value2} = e2 in
    Env.equal equal_tys ty1 ty1
    && Env.equal (equal_values ~cmp_meta) value1 value2
    && equal_funcs ~cmp_meta f1 f2
  | VRecord map1, VRecord map2 ->
    StringMap.equal (equal_values ~cmp_meta) map1 map2
  | _, _ -> false

and equal_lists ~cmp_meta vs1 vs2 =
  match (vs1, vs2) with
  | [], [] -> true
  | [], _ | _, [] -> false
  | v1 :: vs1, v2 :: vs2 ->
    equal_values ~cmp_meta v1 v2 && equal_lists ~cmp_meta vs1 vs2

and equal_exps ~cmp_meta (e1: exp) (e2: exp) =
  let cfg = Cmdline.get_cfg () in
  let b =
    if cfg.hashcons then e1.etag = e2.etag
    else equal_es ~cmp_meta e1.e e2.e
  in
  if cmp_meta then
    b
    && equal_opt equal_tys e1.ety e2.ety
    && equal_spans e1.espan e2.espan
  else b

and equal_es ~cmp_meta e1 e2 =
  match (e1, e2) with
  | EVar x1, EVar x2 -> Var.equals x1 x2
  | EVal v1, EVal v2 -> equal_values ~cmp_meta v1 v2
  | EOp (op1, es1), EOp (op2, es2) ->
    equal_op op1 op2 && equal_lists_es ~cmp_meta es1 es2
  | EFun f1, EFun f2 -> equal_funcs ~cmp_meta f1 f2
  | EApp (e1, e2), EApp (e3, e4) ->
    equal_exps ~cmp_meta e1 e3 && equal_exps ~cmp_meta e2 e4
  | EIf (e1, e2, e3), EIf (e4, e5, e6) ->
    equal_exps ~cmp_meta e1 e4
    && equal_exps ~cmp_meta e2 e5
    && equal_exps ~cmp_meta e3 e6
  | ELet (x1, e1, e2), ELet (x2, e3, e4) ->
    Var.equals x1 x2
    && equal_exps ~cmp_meta e1 e3
    && equal_exps ~cmp_meta e2 e4
  | ETuple es1, ETuple es2 -> equal_lists_es ~cmp_meta es1 es2
  | ESome e1, ESome e2 -> equal_exps ~cmp_meta e1 e2
  | EMatch (e1, bs1), EMatch (e2, bs2) ->
    equal_exps ~cmp_meta e1 e2 && equal_branches ~cmp_meta bs1 bs2
  | ETy (e1, ty1), ETy (e2, ty2) ->
    equal_exps ~cmp_meta e1 e2 && ty1 = ty2
  | ERecord map1, ERecord map2 ->
    StringMap.equal (equal_exps ~cmp_meta) map1 map2
  | EProject (e1, label1), EProject (e2, label2) ->
    String.equal label1 label2 && equal_exps ~cmp_meta e1 e2
  | _, _ -> false

and equal_lists_es ~cmp_meta es1 es2 =
  match (es1, es2) with
  | [], [] -> true
  | [], _ | _, [] -> false
  | e1 :: es1, e2 :: es2 ->
    equal_exps ~cmp_meta e1 e2 && equal_lists_es ~cmp_meta es1 es2

and equal_branches ~cmp_meta bs1 bs2 =
  let rec equal_branches_lst bs1 bs2 =
    match (bs1, bs2) with
    | [], [] -> true
    | [], _ | _, [] -> false
    | (p1, e1) :: bs1, (p2, e2) :: bs2 ->
      equal_patterns p1 p2
      && equal_exps ~cmp_meta e1 e2
      && equal_branches_lst bs1 bs2
  in
  let equal_branches_map bs1 bs2 =
    PatMap.cardinal bs1.pmap = PatMap.cardinal bs2.pmap &&
    PatMap.for_all (fun p e -> match PatMap.Exceptionless.find p bs2.pmap with
        | None -> false
        | Some e' -> equal_exps ~cmp_meta e e') bs1.pmap
  in
  (equal_branches_map bs1 bs2) && (equal_branches_lst bs1.plist bs2.plist)

and equal_patterns p1 p2 =
  match (p1, p2) with
  | PWild, PWild -> true
  | PVar x1, PVar x2 -> Var.equals x1 x2
  | PBool b1, PBool b2 -> b1 = b2
  | PInt i, PInt j -> Integer.equal i j
  | PTuple ps1, PTuple ps2 -> equal_patterns_list ps1 ps2
  | POption None, POption None -> true
  | POption (Some p1), POption (Some p2) -> equal_patterns p1 p2
  | PRecord map1, PRecord map2 -> StringMap.equal equal_patterns map1 map2
  | PNode n1, PNode n2 -> n1 = n2
  | PEdge (p1, p2), PEdge (p1', p2') -> equal_patterns p1 p1' && equal_patterns p2 p2'
  | _ -> false

and equal_patterns_list ps1 ps2 =
  match (ps1, ps2) with
  | [], [] -> true
  | _ :: _, [] | [], _ :: _ -> false
  | p1 :: ps1, p2 :: ps2 ->
    equal_patterns p1 p2 && equal_patterns_list ps1 ps2

and equal_funcs ~cmp_meta f1 f2 =
  let {arg= x; argty= aty1; resty= rty1; body= e1} = f1 in
  let {arg= y; argty= aty2; resty= rty2; body= e2} = f2 in
  let b =
    if cmp_meta then
      equal_opt equal_tys aty1 aty2 && equal_opt equal_tys rty1 rty2
    else true
  in
  b && Var.equals x y && equal_exps ~cmp_meta e1 e2

let hash_string str =
  let acc = ref 7 in
  for i = 0 to String.length str - 1 do
    let c : char = str.[i] in
    acc := (31 * !acc) + int_of_char c
  done ;
  !acc

let rec hash_ty ty =
  match ty with
  | TVar tyvar -> (
      match !tyvar with
      | Unbound (name, x) -> hash_string (Var.to_string name) + x
      | Link t -> 2 + hash_ty t )
  | QVar name -> 3 + hash_string (Var.to_string name)
  | TBool -> 4
  | TInt _ -> 5
  | TArrow (ty1, ty2) -> 6 + hash_ty ty1 + hash_ty ty2
  | TTuple ts ->
    List.fold_left (fun acc t -> acc + hash_ty t) 0 ts + 7
  | TOption t -> 8 + hash_ty t
  | TMap (ty1, ty2) -> 9 + hash_ty ty1 + hash_ty ty2
  | TRecord map ->
    StringMap.fold (fun l t acc -> acc + + hash_string l + hash_ty t) map 0 + 10
  | TUnit -> 11
  | TNode -> 12
  | TEdge -> 13

let hash_span (span: Span.t) = (19 * span.start) + span.finish

let hash_opt h o =
  match o with None -> 1 | Some x -> (19 * h x) + 2

let rec hash_value ~hash_meta v : int =
  let cfg = Cmdline.get_cfg () in
  let m =
    if hash_meta then
      (19 * hash_opt hash_ty v.vty) + hash_span v.vspan
    else 0
  in
  if cfg.hashcons then (19 * v.vhkey) + m
  else (19 * hash_v ~hash_meta v.v) + m

and hash_v ~hash_meta v =
  match v with
  | VBool b -> if b then 1 else 0
  | VInt i -> (19 * Integer.to_int i) + 1
  | VMap m -> (19 * Hashtbl.hash m) + 2
  | VTuple vs ->
    let acc =
      List.fold_left
        (fun acc v -> acc + hash_value ~hash_meta v)
        0 vs
    in
    (19 * acc) + 3
  | VOption vo -> (
      match vo with
      | None -> 4
      | Some x -> (19 * hash_value ~hash_meta x) + 4 )
  | VClosure (e1, f1) ->
    let {ty= ty1; value= v} = e1 in
    let vs = Env.to_list v in
    let acc =
      List.fold_left
        (fun acc (x, v) ->
           let x = hash_string (Var.to_string x) in
           acc + x + hash_value ~hash_meta v )
        0 vs
    in
    (19 * acc) + 5
  | VRecord map ->
    let acc =
      StringMap.fold
        (fun l v acc -> acc + + hash_string l + hash_value ~hash_meta v)
        map 0
    in
    (19 * acc) + 7
  | VUnit -> 8
  | VNode n -> (19 * n) + 9
  | VEdge (e1, e2) -> (19 * (e1 + 19 * e2)) + 10

and hash_exp ~hash_meta e =
  let cfg = Cmdline.get_cfg () in
  let m =
    if hash_meta then
      (19 * hash_opt hash_ty e.ety) + hash_span e.espan
    else 0
  in
  if cfg.hashcons then (19 * e.ehkey) + m
  else (19 * hash_e ~hash_meta e.e) + m

and hash_e ~hash_meta e =
  match e with
  | EVar x -> hash_var x
  | EVal v -> (19 * hash_value ~hash_meta v) + 1
  | EOp (op, es) ->
    (19 * ((19 * hash_op op) + hash_es ~hash_meta es)) + 2
  | EFun f ->
    let i =
      if hash_meta then
        hash_opt hash_ty f.argty + hash_opt hash_ty f.resty
      else 0
    in
    19
    * ( (19 * ((19 * hash_var f.arg) + hash_exp ~hash_meta f.body))
        + i )
    + 3
  | EApp (e1, e2) ->
    (19 * ((19 * hash_exp ~hash_meta e1) + hash_exp ~hash_meta e2))
    + 4
  | EIf (e1, e2, e3) ->
    19
    * ( 19
        * ((19 * hash_exp ~hash_meta e1) + hash_exp ~hash_meta e2)
        + hash_exp ~hash_meta e3 )
    + 5
  | ELet (x, e1, e2) ->
    19
    * ( (19 * ((19 * hash_var x) + hash_exp ~hash_meta e1))
        + hash_exp ~hash_meta e2 )
    + 6
  | ETuple es -> (19 * hash_es ~hash_meta es) + 7
  | ESome e -> (19 * hash_exp ~hash_meta e) + 8
  | EMatch (e, bs) ->
    19
    * ((19 * hash_exp ~hash_meta e) + hash_branches ~hash_meta bs)
    + 9
  | ETy (e, ty) ->
    (19 * ((19 * hash_exp ~hash_meta e) + hash_ty ty)) + 10
  | ERecord map ->
    (19 *
     StringMap.fold
       (fun l e acc -> acc + + hash_string l + hash_exp ~hash_meta e) map 0
     + 11)
  | EProject (e, label) ->
    (19 * hash_exp ~hash_meta e + hash_string label + 12)

and hash_var x = hash_string (Var.to_string x)

and hash_es ~hash_meta es =
  List.fold_left (fun acc e -> acc + hash_exp ~hash_meta e) 0 es

and hash_branches ~hash_meta bs =
  let acc1 = BatList.fold_left
      (fun acc (p, e) -> acc + hash_pattern p + hash_exp ~hash_meta e)
      0 bs.plist
  in
  PatMap.fold
    (fun p e acc -> acc + hash_pattern p + hash_exp ~hash_meta e) bs.pmap acc1

and hash_pattern p =
  match p with
  | PUnit -> 0
  | PWild -> 1
  | PVar x -> (19 * hash_var x) + 2
  | PBool b -> (19 * if b then 1 else 0) + 3
  | PInt i -> (19 * Integer.to_int i) + 4
  | PTuple ps -> (19 * hash_patterns ps) + 5
  | POption None -> 6
  | POption (Some p) -> (19 * hash_pattern p) + 7
  | PRecord map ->
    (19 *
     StringMap.fold (fun l p acc -> acc + + hash_string l + hash_pattern p) map 0
     + 8)
  | PNode n -> (19 * n) + 9
  | PEdge (p1, p2) -> (19 * (hash_pattern p1 + 19 * hash_pattern p2)) + 10

and hash_patterns ps =
  List.fold_left (fun acc p -> acc + hash_pattern p) 0 ps

and hash_op op =
  match op with
  | And -> 1
  | Or -> 2
  | Not -> 3
  | Eq -> 4
  | MCreate -> 5
  | MGet -> 6
  | MSet -> 7
  | MMap -> 8
  | MMapFilter -> 9
  | MMerge -> 10
  | UAdd n -> 11  + n + 256
  | USub n -> 11  + n + 256 * 2
  | ULess n -> 11 + n + 256 * 3
  | ULeq n -> 11  + n + 256 * 4
  | AtMost n -> 12 + n
  | NLess -> 13
  | NLeq -> 14
(* hashconsing information/tables *)

let meta_v : (v, value) meta =
  { hash= hash_v ~hash_meta:true
  ; equal= equal_vs ~cmp_meta:true
  ; node= (fun v -> v.v)
  ; make=
      (fun ~tag ~hkey v ->
         {v; vty= None; vspan= Span.default; vtag= tag; vhkey= hkey}
      )
  ; hkey= (fun v -> v.vhkey) }

let meta_e : (e, exp) meta =
  { hash= hash_e ~hash_meta:true
  ; equal= equal_es ~cmp_meta:true
  ; node= (fun e -> e.e)
  ; make=
      (fun ~tag ~hkey e ->
         {e; ety= None; espan= Span.default; etag= tag; ehkey= hkey}
      )
  ; hkey= (fun e -> e.ehkey) }

let tbl_v = Hashcons.create meta_v 251

let tbl_e = Hashcons.create meta_e 251

(* Utilities *)

let arity op =
  match op with
  | And -> 2
  | Or -> 2
  | Not -> 1
  | UAdd _ -> 2
  | USub _ -> 2
  | Eq -> 2
  | ULess _ -> 2
  | ULeq _ -> 2
  | NLess -> 2
  | NLeq -> 2
  | AtMost _ -> 3
  | MCreate -> 1
  | MGet -> 2
  | MSet -> 3
  | MMap -> 2
  | MMapFilter -> 3
  | MMerge -> 3

(* Useful constructors *)

let tint_of_size n = TInt n

let tint_of_value n = TInt (Integer.size n)

let exp e =
  let cfg = Cmdline.get_cfg () in
  if cfg.hashcons then Hashcons.hashcons tbl_e e
  else {e; ety= None; espan= Span.default; etag= 0; ehkey= 0}

let value v =
  let cfg = Cmdline.get_cfg () in
  if cfg.hashcons then Hashcons.hashcons tbl_v v
  else {v; vty= None; vspan= Span.default; vtag= 0; vhkey= 0}

let aexp (e, t, span) = {e with ety= t; espan= span}

let avalue (v, t, span) = {v with vty= t; vspan= span}

let wrap exp e = {e with ety= exp.ety; espan= exp.espan}

(* Constructors *)

let vunit () = value VUnit

let vbool b = {(value (VBool b)) with vty = Some TBool}

let vnode n = value (VNode n)

let vedge e = value (VEdge e)

let vint i = value (VInt i)

let vmap m = value (VMap m)

let vtuple vs = value (VTuple vs)

let vrecord map = value (VRecord map)

let voption vo = value (VOption vo)

let vclosure c = value (VClosure c)

let evar x = exp (EVar x)

let e_val v = exp (EVal v)

let eop op es = exp (EOp (op, es))

let efun f = exp (EFun f)

let eapp e1 e2 = exp (EApp (e1, e2))

let eif e1 e2 e3 = exp (EIf (e1, e2, e3))

let elet x e1 e2 = exp (ELet (x, e1, e2))

let etuple es = exp (ETuple es)

let eproject e l = exp (EProject (e,l))

let erecord map = exp (ERecord map)

let esome e = exp (ESome e)

let ematch e bs = exp (EMatch (e, bs))

let ety e ty = exp (ETy (e, ty))

let deconstructFun exp =
  match exp.e with
  | EFun f ->
    f
  | _ -> failwith "expected a function"

let rec is_value e =
  match e.e with
  | EVal _ -> true
  | ETuple es -> BatList.for_all is_value es
  | ERecord map -> StringMap.for_all (fun _ e -> is_value e) map
  | ESome e -> is_value e
  | ETy (e, _) -> is_value e
  | EVar _
  | EOp _
  | EFun _
  | EApp _
  | EIf _
  | ELet _
  | EMatch _
  | EProject _ ->
    false

let rec to_value e =
  match e.e with
  | EVal v -> v
  | ETy (e, _) -> to_value e
  | ETuple es ->
    avalue (vtuple (BatList.map to_value es), e.ety, e.espan)
  | ESome e1 -> avalue (voption (Some (to_value e1)), e.ety, e.espan)
  | _ -> failwith "internal error (to_value)"


let exp_of_v x = exp (EVal (value x))

let rec exp_of_value v =
  match v.v with
  | VUnit | VBool _ | VInt _ | VMap _ | VClosure _ | VOption None | VNode _ | VEdge _->
    let e = e_val v in
    {e with ety= v.vty; espan=v.vspan}
  | VTuple vs ->
    let e = etuple (BatList.map exp_of_value vs) in
    {e with ety= v.vty; espan=v.vspan}
  | VRecord map ->
    let e = erecord (StringMap.map exp_of_value map) in
    {e with ety= v.vty; espan=v.vspan}
  | VOption (Some v1) ->
    let e = esome (exp_of_value v1) in
    {e with ety= v.vty; espan=v.vspan}

let rec val_to_pattern v =
  match v.v with
  | VUnit -> PUnit
  | VNode n -> PNode n
  | VEdge (n1, n2) -> PEdge (PNode n1, PNode n2)
  | VBool b -> PBool b
  | VInt i -> PInt i
  | VTuple vs -> PTuple (BatList.map val_to_pattern vs)
  | VOption None -> POption None
  | VOption (Some v) -> POption (Some (val_to_pattern v))
  | VRecord rs -> PRecord (StringMap.map val_to_pattern rs)
  | VClosure _ | VMap _ -> failwith "can't use these type of values as patterns"

let rec exp_to_pattern e =
  match e.e with
  | EVal v ->
    val_to_pattern v
  | ETuple es -> PTuple (BatList.map exp_to_pattern es)
  | ESome e -> POption (Some (exp_to_pattern e))
  | ETy (e, _) -> exp_to_pattern e
  | EVar x -> PVar x
  | ERecord rs -> PRecord (StringMap.map exp_to_pattern rs)
  | EProject _
  | EOp _
  | EFun _
  | EApp _
  | EIf _
  | ELet _
  | EMatch _ ->
    failwith "can't use these expressions as patterns"

let func x body = {arg= x; argty= None; resty= None; body}

let funcFull x argty resty body = {arg= x; argty= argty; resty= resty; body}

let efunc f =
  match f.argty, f.resty with
  | Some argty, Some resty ->
    aexp (exp (EFun f), Some (TArrow (argty, resty)), Span.default)
  | _, _ ->
    exp (EFun f)

let lam x body = exp (EFun (func x body))

let annot ty e = {e with ety= Some ty; espan= e.espan}

let annotv ty v = {v with vty= Some ty; vspan= v.vspan}

let oget (x: 'a option) : 'a =
  match x with
  | None -> failwith "internal error (oget)"
  | Some y -> y

let omap (f : 'a -> 'b) (x: 'a option): 'b option =
  match x with
  | None -> None
  | Some y -> Some(f y)

let rec lams params body =
  match params with
  | [] -> failwith "lams: no parameters"
  | [p] -> lam p body
  | p :: params -> lam p (lams params body)

let rec apps f args : exp =
  match args with
  | [] -> failwith "apps: no arguments"
  | [a] -> exp (EApp (f, a))
  | a :: args -> apps (exp (EApp (f, a))) args

let apply_closure cl (args: value list) =
  apps (exp_of_v (VClosure cl)) (List.map (fun a -> e_val a) args)

(* Requires that e is of type TTuple *)
let tupleToList (e : exp) =
  match e.e with
  | ETuple es -> es
  | EVal v ->
    (match v.v with
     | VTuple vs ->
       BatList.map (fun v -> aexp(e_val v, v.vty, v.vspan)) vs
     | _ -> failwith "Not a tuple type")
  | _ -> failwith "Not a tuple type"

let tupleToListSafe (e : exp) =
  match e.e with
  | ETuple _| EVal _ -> tupleToList e
  | _ -> [e]


let get_decl ds f =
  try
    let daty : declaration =
      List.find
        (fun d -> match f d with None -> false | Some _ -> true)
        ds
    in
    f daty
  with _ -> None

let get_lets ds =
  BatList.filter_map (fun d -> match d with DLet (x,ty,e) -> Some (x,ty,e) | _ -> None) ds

let get_attr_type ds =
  get_decl ds (fun d -> match d with DATy ty -> Some ty | _ -> None)

let get_merge ds =
  get_decl ds (fun d -> match d with DMerge e -> Some e | _ -> None)

let get_trans ds =
  get_decl ds (fun d -> match d with DTrans e -> Some e | _ -> None)

let get_init ds =
  get_decl ds (fun d -> match d with DInit e -> Some e | _ -> None)

let get_assert ds =
  get_decl ds (fun d ->
      match d with DAssert e -> Some e | _ -> None )

let get_edges ds =
  get_decl ds (fun d ->
      match d with DEdges es -> Some es | _ -> None )

let get_nodes ds =
  get_decl ds (fun d -> match d with DNodes i -> Some i | _ -> None)

let get_symbolics ds =
  List.fold_left
    (fun acc d ->
       match d with DSymbolic (x, e) -> (x, e) :: acc | _ -> acc )
    [] ds
  |> List.rev

let get_requires ds =
  List.fold_left
    (fun acc d -> match d with DRequire e -> e :: acc | _ -> acc)
    [] ds
  |> List.rev

let get_types ds =
  BatList.filter_map (fun d -> match d with DUserTy (x,ty) -> Some (x,ty) | _ -> None) ds

let get_record_types ds =
  List.fold_left
    (fun acc d ->
       match d with
       | DUserTy (_, TRecord lst) -> (lst) :: acc
       | _ -> acc
    )
    [] ds

let rec get_inner_type t : ty =
  match t with TVar {contents= Link t} -> get_inner_type t | _ -> t

let get_ty_from_tyexp (et : ty_or_exp) : ty =
  match et with
  | Ty t -> t
  | Exp e -> oget (e.ety)

let bool_of_val (v : value) : bool option =
  match v.v with
  | VBool b -> Some b
  | _ -> None

let proj_var (n: int) (x: var) =
  let (s,i) = Var.from_var x in
  Var.to_var (Printf.sprintf "%s-proj-%d" s n,i)

let unproj_var (x : var) =
  let (s,i) = Var.from_var x in
  let name, n = BatString.split s "-proj-" in
  (int_of_string n, Var.to_var (name, i))

open BatSet

let rec free (seen: Var.t PSet.t) (e: exp) : Var.t PSet.t =
  match e.e with
  | EVar v ->
    if PSet.mem v seen then PSet.create Var.compare
    else PSet.singleton ~cmp:Var.compare v
  | EVal _ -> PSet.create Var.compare
  | EOp (_, es) | ETuple es ->
    List.fold_left
      (fun set e -> PSet.union set (free seen e))
      (PSet.create Var.compare)
      es
  | ERecord map ->
    StringMap.fold
      (fun _ e set -> PSet.union set (free seen e))
      map
      (PSet.create Var.compare)
  | EFun f -> free (PSet.add f.arg seen) f.body
  | EApp (e1, e2) -> PSet.union (free seen e1) (free seen e2)
  | EIf (e1, e2, e3) ->
    PSet.union (free seen e1)
      (PSet.union (free seen e2) (free seen e3))
  | ELet (x, e1, e2) ->
    let seen = PSet.add x seen in
    PSet.union (free seen e1) (free seen e2)
  | ESome e | ETy (e, _) | EProject (e, _) -> free seen e
  | EMatch (e, bs) ->
    let bs1 =
      PatMap.fold
        (fun p e set ->
           let seen = PSet.union seen (pattern_vars p) in
           PSet.union set (free seen e) )
        bs.pmap
        (PSet.create Var.compare)
    in
    let bs =
      BatList.fold_left
        (fun set (p, e) ->
           let seen = PSet.union seen (pattern_vars p) in
           PSet.union set (free seen e) )
        bs1
        bs.plist
    in
    PSet.union (free seen e) bs

and pattern_vars p =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | POption None | PNode _ ->
    PSet.create Var.compare
  | PVar v -> PSet.singleton ~cmp:Var.compare v
  | PEdge (p1, p2) -> pattern_vars (PTuple [p1; p2]) 
  | PTuple ps ->
    List.fold_left
      (fun set p -> PSet.union set (pattern_vars p))
      (PSet.create Var.compare)
      ps
  | PRecord map ->
    StringMap.fold
      (fun _ p set -> PSet.union set (pattern_vars p))
      map
      (PSet.create Var.compare)
  | POption (Some p) -> pattern_vars p

let rec free_dead_vars (e : exp) =
  match e.e with
  | ETy (e, _) -> free_dead_vars e
  | EVal v ->
    (match v.v with
     | VClosure (env, f) ->
       let fv = free (PSet.empty) f.body in
       vclosure ({env with value = Env.filter env.value (fun x _ -> PSet.mem x fv)},
                 {f with body = free_dead_vars f.body})
       |> exp_of_value
       |> wrap e
     | _ -> e)
  | EVar _ | EFun _ -> e
  | EOp (op, es) ->
    eop op (List.map free_dead_vars es)
  | EApp (e1, e2) ->
    let e1 = free_dead_vars e1 in
    let e2 = free_dead_vars e2 in
    eapp e1 e2
  | EIf (e1, e2, e3) ->
    let e1 = free_dead_vars e1 in
    let e2 = free_dead_vars e2 in
    let e3 = free_dead_vars e3 in
    eif e1 e2 e3
  | ELet (x, e1, e2) ->
    let e1 = free_dead_vars e1 in
    let e2 = free_dead_vars e2 in
    elet x e1 e2
  | ETuple es ->
    etuple (List.map free_dead_vars es)
  | ERecord map ->
    erecord (StringMap.map free_dead_vars map)
  | ESome e -> esome (free_dead_vars e)
  | EMatch (e1, branches) ->
    let e1 = free_dead_vars e1 in
    ematch e1
      (mapBranches (fun (ps, e) -> (ps, free_dead_vars e)) branches)
  | EProject (e, l) -> eproject (free_dead_vars e) l


(* This is used because for SMT we represent maps as map expression
   and not values, and we want some type of default value for them as
   well *)
let rec default_exp_value ty =
  match ty with
  | TUnit -> exp_of_value (avalue (vunit (), Some ty, Span.default))
  | TBool -> exp_of_value (avalue (vbool false, Some ty, Span.default))
  | TNode -> exp_of_value (avalue (vnode 0, Some TNode, Span.default))
  | TEdge -> exp_of_value (avalue (vedge (0, 1), Some TEdge, Span.default))
  | TInt size ->
    exp_of_value (avalue (vint (Integer.create ~value:0 ~size:size), Some ty, Span.default))
  | TTuple ts ->
    aexp (etuple (BatList.map default_exp_value ts), Some ty, Span.default)
  | TRecord map -> aexp (etuple (BatList.map default_exp_value @@ get_record_entries map),
                         Some ty, Span.default)
  | TOption _ ->
    exp_of_value (avalue (voption None, Some ty, Span.default))
  | TMap (ty1, ty2) ->
    aexp(eop MCreate [default_exp_value ty2], Some ty, Span.default)
  | TVar {contents= Link t} ->
    default_exp_value t
  | TVar _ | QVar _ | TArrow _ ->
    failwith "internal error (default_value)"

(* Memoization *)

module type MEMOIZER = sig
  type t

  val memoize : size:int -> (t -> 'a) -> t -> 'a
end

module Memoize (K : Lru_cache.Key) :
  MEMOIZER with type t = K.t =
struct
  module L = Lru_cache.Make (K)

  type t = K.t

  let memoize ~size (f: 'a -> 'b) : 'a -> 'b =
    let map = L.init size in
    fun x ->
      let cfg = Cmdline.get_cfg () in
      if cfg.hashcons && cfg.memoize then L.get map x f else f x
end

module VKey = struct
  type t = value

  let compare v1 v2 = v1.vtag - v2.vtag

  let witness = vbool true
end

module EKey = struct
  type t = exp

  let compare e1 e2 = e1.etag - e2.etag

  let witness = e_val (vbool true)
end

module MemoizeValue = Memoize (VKey)
module MemoizeExp = Memoize (EKey)

let compare_vs = compare_value
let compare_es = compare_exp

let compare_values v1 v2 =
  let cfg = Cmdline.get_cfg () in
  if cfg.hashcons then v1.vtag - v2.vtag
  else Pervasives.compare v1 v2

let compare_exps e1 e2 =
  let cfg = Cmdline.get_cfg () in
  if cfg.hashcons then e1.etag - e2.etag
  else Pervasives.compare e1 e2

(* Include the map type here to avoid circular dependency *)

module BddUtils = struct
  let mgr = Man.make_v ()

  let set_size sz =
    let num_vars = Man.get_bddvar_nb mgr in
    if num_vars < sz then
      for i = 1 to sz - num_vars do ignore (Bdd.newvar mgr) done

  let ithvar i =
    set_size (i + 1) ;
    Bdd.ithvar mgr i

  let rec ty_to_size ty =
    match get_inner_type ty with
    | TUnit -> 1 (* I don't understand how Cudd BDDs work, so encode TUnit as false *)
    | TBool -> 1
    | TInt _ -> 32
    | TOption tyo -> 1 + ty_to_size tyo
    | TTuple ts ->
      List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
    | TRecord tmap -> ty_to_size (TTuple (get_record_entries tmap))
    | TNode -> ty_to_size (TInt 32) (* Encode as int *)
    | TEdge -> ty_to_size (TTuple [TNode; TNode]) (* Encode as node pair *)
    | TArrow _ | TMap _ | TVar _ | QVar _ ->
      failwith ("internal error (ty_to_size): " ^ (show_ty ty))

  let tbl =
    Mtbdd.make_table
      ~hash:(hash_value ~hash_meta:false)
      ~equal:(equal_values ~cmp_meta:false)

  let tbl_bool =
    Mtbdd.make_table ~hash:(fun b -> if b then 1 else 0) ~equal:( = )

  let get_bit (n: Integer.t) (i: int) : bool =
    let z = Integer.value n in
    let marker = (Z.shift_left Z.one i) in
    Z.logand z marker <> Z.zero

  let mk_int i idx =
    let acc = ref (Bdd.dtrue mgr) in
    let sz = Integer.size i in
    for j = 0 to sz - 1 do
      let var = ithvar (idx + j) in
      let bit = get_bit i j in
      let bdd = if bit then Bdd.dtrue mgr else Bdd.dfalse mgr in
      acc := Bdd.dand !acc (Bdd.eq var bdd)
    done ;
    !acc

  let tbool_to_bool tb =
    match tb with Man.False | Man.Top -> false | Man.True -> true
end

module BddMap = struct
  module B = BddUtils

  (* TODO: optimize variable ordering  *)
  type t = mtbdd

  (* let res = User.map_op2
     ~commutative:true ~idempotent:true
     ~special:(fun bdd1 bdd2 ->
      if Vdd.is_cst bdd1 && Vdd.dval bdd1 = false then Some(bdd1)
      else if Vdd.is_cst bdd2 && Vdd.dval bdd2 = false then Some(bdd2)
      else None)
     (fun b1 b2 -> b1 && b2) *)

  let create ~key_ty:ty (v: value) : t =
    B.set_size (B.ty_to_size ty) ;
    (Mtbdd.cst B.mgr B.tbl v, ty)

  let rec default_value ty =
    match ty with
    | TUnit -> avalue (vunit (), Some ty, Span.default)
    | TBool -> avalue (vbool false, Some ty, Span.default)
    | TInt size ->
      avalue (vint (Integer.create ~value:0 ~size:size), Some ty, Span.default)
    | TRecord map -> avalue (vtuple (BatList.map default_value @@ get_record_entries map),
                             Some ty, Span.default)
    | TTuple ts ->
      avalue (vtuple (BatList.map default_value ts), Some ty, Span.default)
    | TOption _ ->
      avalue (voption None, Some ty, Span.default)
    | TMap (ty1, ty2) ->
      avalue (vmap (create ~key_ty:ty1 (default_value ty2)), Some ty, Span.default)
    | TNode -> avalue (vnode 0, Some ty, Span.default)
    | TEdge -> avalue (vedge (0, 1), Some ty, Span.default)
    | TVar {contents= Link t} ->
      default_value t
    | TVar _ | QVar _ | TArrow _ ->
      failwith "internal error (default_value)"

  let value_to_bdd (v: value) : Bdd.vt =
    let rec aux v idx =
      match v.v with
      | VUnit -> (* Encode unit as if it were a true boolean *)
        let var = B.ithvar idx in
        var, idx + 1
      | VBool b ->
        let var = B.ithvar idx in
        ((if b then var else Bdd.dnot var), idx + 1)
      | VInt i ->
        B.mk_int i idx, idx + Integer.size i
      | VTuple vs ->
        let base = Bdd.dtrue B.mgr in
        List.fold_left
          (fun (bdd_acc, idx) v ->
             let bdd, i = aux v idx in
             (Bdd.dand bdd_acc bdd, i) )
          (base, idx) vs
      | VRecord map ->
        (* Convert this to a tuple type, then encode that *)
        let tup = value @@ VTuple (get_record_entries map) in
        aux tup idx
      | VNode n ->
        (* Encode same way as we encode ints *)
        aux (value @@ VInt (Integer.create ~value:n ~size:32)) idx
      | VEdge (e1, e2) ->
        (* Encode same way as we encode tuples of nodes *)
        let tup = value @@ VTuple [value (VNode e1); value (VNode e2)] in
        aux tup idx
      | VOption None ->
        let var = B.ithvar idx in
        let tag = Bdd.eq var (Bdd.dfalse B.mgr) in
        let dv = default_value (oget v.vty) in
        let value, idx = aux dv (idx + 1) in
        (Bdd.dand tag value, idx)
      | VOption (Some dv) ->
        let var = B.ithvar idx in
        let tag = Bdd.eq var (Bdd.dtrue B.mgr) in
        let value, idx = aux dv (idx + 1) in
        (Bdd.dand tag value, idx)
      | VMap _ | VClosure _ ->
        failwith "internal error (value_to_bdd)"
    in
    let bdd, _ = aux v 0 in
    bdd

  let vars_to_value vars ty =
    let rec aux idx ty =
      let v, i =
        match get_inner_type ty with
        | TUnit -> vunit (), idx + 1 (* Same as a bool *)
        | TBool ->
          (VBool (B.tbool_to_bool vars.(idx)) |> value, idx + 1)
        | TInt size ->
          let acc = ref (Integer.create ~value:0 ~size:size) in
          for i = 0 to size-1 do
            let bit = B.tbool_to_bool vars.(idx + i) in
            if bit then
              let add = Integer.shift_left (Integer.create ~value:1 ~size:size) i in
              acc := Integer.add !acc add
          done ;
          (value (VInt !acc), idx + size)
        | TTuple ts ->
          let vs, i =
            List.fold_left
              (fun (vs, idx) ty ->
                 let v, i = aux idx ty in
                 (v :: vs, i) )
              ([], idx) ts
          in
          (value (VTuple (List.rev vs)), i)
        | TRecord map ->
          (* This will have been encoded as if it's a tuple.
             So get the tuple type and use that to decode *)
          let tup = TTuple (get_record_entries map) in
          aux idx tup
        | TNode ->
          (* Was encoded as int, so decode same way *)
          aux idx (TInt 32)
        | TEdge ->
          (* Was encoded as tuple of nodes *)
          aux idx (TTuple [TNode; TNode])
        | TOption tyo ->
          let tag = B.tbool_to_bool vars.(idx) in
          let v, i = aux (idx + 1) tyo in
          let v =
            if tag then VOption (Some v) |> value
            else value (VOption None)
          in
          (v, i)
        | TArrow _ | TMap _ | TVar _ | QVar _ ->
          failwith "internal error (bdd_to_value)"
      in
      let ty =
        match ty with
        | TRecord map -> TTuple (get_record_entries map)
        | _ -> ty
      in
      (annotv ty v, i)
    in
    fst (aux 0 ty)

  module ExpMap = Map.Make (struct
      type t = exp * value PSet.t

      let compare = Pervasives.compare
    end)

  let map_cache = ref ExpMap.empty

  let map ~op_key (f: value -> value) ((vdd, ty): t) : t =
    let cfg = Cmdline.get_cfg () in
    let g x = f (Mtbdd.get x) |> Mtbdd.unique B.tbl in
    if cfg.no_caching then (Mapleaf.mapleaf1 g vdd, ty)
    else
      let op =
        match ExpMap.find_opt op_key !map_cache with
        | None ->
          let o =
            User.make_op1 ~memo:(Memo.Cache (Cache.create1 ())) g
          in
          map_cache := ExpMap.add op_key o !map_cache ;
          o
        | Some op -> op
      in
      (User.apply_op1 op vdd, ty)

  let count_tops arr sz =
    let j = ref 0 in
    for i = 0 to sz - 1 do
      match arr.(i) with Man.Top -> incr j | _ -> ()
    done ;
    !j

  let rec size ty =
    match get_inner_type ty with
    | QVar _ | TVar _ | TArrow _ | TMap _ ->
      failwith "internal error (size)"
    | TUnit -> size (TBool) (* Encode as boolean because I don't understand this code *)
    | TBool -> 1
    | TInt _ -> 32
    | TNode -> size (TInt 32)
    | TEdge -> size (TTuple [TNode; TNode])
    | TTuple ts -> List.fold_left (fun acc t -> acc + size t) 0 ts
    | TRecord map -> size (TTuple (get_record_entries map))
    | TOption t -> 1 + size t

  let pick_default_value (map, ty) =
    let count = ref (-1) in
    let value = ref None in
    Mtbdd.iter_cube
      (fun vars v ->
         let c = count_tops vars (size ty) in
         if c > !count then count := c ;
         value := Some v )
      map ;
    oget !value

  let rec expand (vars: Man.tbool list) sz : Man.tbool list list =
    if sz = 0 then [[]]
    else
      match vars with
      | [] -> [[]]
      | Man.Top :: xs ->
        let vars = expand xs (sz - 1) in
        let trus = List.map (fun v -> Man.False :: v) vars in
        let fals = List.map (fun v -> Man.True :: v) vars in
        fals @ trus
      | x :: xs ->
        let vars = expand xs (sz - 1) in
        List.map (fun v -> x :: v) vars

  let bindings ((map, ty): t) : (value * value) list * value =
    let bs = ref [] in
    let dv = pick_default_value (map, ty) in
    Mtbdd.iter_cube
      (fun vars v ->
         let lst = Array.to_list vars in
         let sz = size ty in
         let expanded =
           if count_tops vars sz <= 5 then expand lst sz else [lst]
         in
         List.iter
           (fun vars ->
              if not (equal_values ~cmp_meta:false v dv) then
                let k = vars_to_value (Array.of_list vars) ty in
                bs := (k, v) :: !bs )
           expanded )
      map ;
    (!bs, dv)

  let mapw_op_cache = ref ExpMap.empty

  let map_when ~op_key (pred: bool Mtbdd.t) (f: value -> value)
      ((vdd, ty): t) : t =
    let cfg = Cmdline.get_cfg () in
    let g b v =
      if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique B.tbl
      else v
    in
    if cfg.no_caching then (Mapleaf.mapleaf2 g pred vdd, ty)
    else
      let op =
        match ExpMap.find_opt op_key !mapw_op_cache with
        | None ->
          let special =
            if cfg.no_cutoff then fun _ _ -> None
            else fun bdd1 bdd2 ->
              if Vdd.is_cst bdd1 && not (Mtbdd.get (Vdd.dval bdd1))
              then Some bdd2
              else None
          in
          let op =
            User.make_op2
              ~memo:(Memo.Cache (Cache.create2 ()))
              ~commutative:false ~idempotent:false ~special g
          in
          mapw_op_cache := ExpMap.add op_key op !mapw_op_cache ;
          op
        | Some op -> op
      in
      (User.apply_op2 op pred vdd, ty)

  module MergeMap = Map.Make (struct
      type t =
        (exp * value PSet.t) * (value * value * value * value) option

      let compare = Pervasives.compare
    end)

  let unwrap x =
    match x with
    | {v= VOption (Some v)} -> (true, v)
    | _ -> (false, vbool false)

  let merge_op_cache = ref MergeMap.empty

  let merge ?opt ~op_key (f: value -> value -> value) ((x, tyx): t)
      ((y, _): t) : t =
    let cfg = Cmdline.get_cfg () in
    let g x y =
      f (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique B.tbl
    in
    if cfg.no_caching then (Mapleaf.mapleaf2 g x y, tyx)
    else
      let key = (op_key, opt) in
      let op =
        match MergeMap.find_opt key !merge_op_cache with
        | None ->
          let special =
            match (opt, cfg.no_cutoff) with
            | None, _ | _, true -> fun _ _ -> None
            | Some (el0, el1, er0, er1), false ->
              let bl0, vl0 = unwrap el0 in
              let bl1, vl1 = unwrap el1 in
              let br0, vr0 = unwrap er0 in
              let br1, vr1 = unwrap er1 in
              fun left right ->
                if
                  bl0 && Vdd.is_cst left
                  && equal_values ~cmp_meta:false
                    (Mtbdd.get (Vdd.dval left))
                    vl0
                then Some right
                else if
                  bl1 && Vdd.is_cst left
                  && equal_values ~cmp_meta:false
                    (Mtbdd.get (Vdd.dval left))
                    vl1
                then Some left
                else if
                  br0 && Vdd.is_cst right
                  && equal_values ~cmp_meta:false
                    (Mtbdd.get (Vdd.dval right))
                    vr0
                then Some left
                else if
                  br1 && Vdd.is_cst right
                  && equal_values ~cmp_meta:false
                    (Mtbdd.get (Vdd.dval right))
                    vr1
                then Some right
                else None
          in
          let o =
            User.make_op2
              ~memo:(Memo.Cache (Cache.create2 ()))
              ~commutative:false ~idempotent:false ~special g
          in
          merge_op_cache := MergeMap.add key o !merge_op_cache ;
          o
        | Some op -> op
      in
      (User.apply_op2 op x y, tyx)

  let find ((map, _): t) (v: value) : value =
    let bdd = value_to_bdd v in
    let for_key = Mtbdd.constrain map bdd in
    Mtbdd.pick_leaf for_key

  let update ((map, ty): t) (k: value) (v: value) : t =
    let leaf = Mtbdd.cst B.mgr B.tbl v in
    let key = value_to_bdd k in
    (Mtbdd.ite key leaf map, ty)

  let from_bindings ~key_ty:ty
      ((bs, default): (value * value) list * value) : t =
    let map = create ~key_ty:ty default in
    List.fold_left (fun acc (k, v) -> update acc k v) map bs

  let equal (bm1, _) (bm2, _) = Mtbdd.is_equal bm1 bm2
end

module BddFunc = struct
  module B = BddUtils

  type t =
    | BBool of Bdd.vt
    | BInt of Bdd.vt array
    | BTuple of t list
    | BOption of Bdd.vt * t

  let bdd_of_bool b = if b then Bdd.dtrue B.mgr else Bdd.dfalse B.mgr

  let wrap_mtbdd bdd =
    let tru = Mtbdd.cst B.mgr B.tbl_bool true in
    let fal = Mtbdd.cst B.mgr B.tbl_bool false in
    Mtbdd.ite bdd tru fal

  let create_value (ty: ty) : t =
    let rec aux i ty =
      match get_inner_type ty with
      | TUnit -> (BBool (B.ithvar i), i + 1)
      | TBool -> (BBool (B.ithvar i), i + 1)
      | TInt size ->
        (BInt (Array.init size (fun j -> B.ithvar (i + j))), i + size)
      | TNode ->
        aux i (TInt 32)
      | TEdge ->
        aux i (TTuple [TNode; TNode])
      | TTuple ts ->
        let bs, idx =
          List.fold_left
            (fun (ls, idx) t ->
               let v, i = aux idx t in
               (v :: ls, i) )
            ([], i) ts
        in
        (BTuple (List.rev bs), idx)
      | TRecord map ->
        aux i (TTuple (get_record_entries map))
      | TOption ty ->
        let v, idx = aux (i + 1) ty in
        (BOption (B.ithvar i, v), idx)
      | TArrow _ | QVar _ | TVar _ | TMap _ ->
        failwith "internal error (create_value)"
    in
    let ret, _ = aux 0 ty in
    ret

  let rec ite (b: Bdd.vt) (x: t) (y: t) : t =
    match (x, y) with
    | BBool m, BBool n -> BBool (Bdd.ite b m n)
    | BInt ms, BInt ns ->
      let both =
        List.combine (Array.to_list ms) (Array.to_list ns)
      in
      let ite = List.map (fun (m, n) -> Bdd.ite b m n) both in
      BInt (Array.of_list ite)
    | BOption (tag1, m), BOption (tag2, n) ->
      let tag = Bdd.ite b tag1 tag2 in
      BOption (tag, ite b m n)
    | BTuple ms, BTuple ns ->
      let both = List.combine ms ns in
      let ite = List.map (fun (m, n) -> ite b m n) both in
      BTuple ite
    | _ -> failwith "internal error (ite)"

  let rec eq (x: t) (y: t) : t =
    let rec aux x y : Bdd.vt =
      match (x, y) with
      | BBool b1, BBool b2 -> Bdd.eq b1 b2
      | BInt bs1, BInt bs2 ->
        let both =
          List.combine (Array.to_list bs1) (Array.to_list bs2)
        in
        List.fold_left
          (fun acc (b1, b2) -> Bdd.dand acc (Bdd.eq b1 b2))
          (Bdd.dtrue B.mgr) both
      | BOption (tag1, b1), BOption (tag2, b2) ->
        let tags = Bdd.eq tag1 tag2 in
        let values = aux b1 b2 in
        Bdd.dand tags values
      | BTuple bs1, BTuple bs2 ->
        let both = List.combine bs1 bs2 in
        List.fold_left
          (fun acc (b1, b2) -> Bdd.dand acc (aux b1 b2))
          (Bdd.dtrue B.mgr) both
      | _ -> failwith "internal error (eq)"
    in
    BBool (aux x y)

  let add (x: t) (y: t) : t =
    let aux xs ys =
      assert ((Array.length xs) = (Array.length ys));
      let var3 = ref (Bdd.dfalse B.mgr) in
      let var4 = Array.make (Array.length xs) (Bdd.dfalse B.mgr) in
      for var5 = 0 to Array.length xs - 1 do
        var4.(var5) <- Bdd.xor xs.(var5) ys.(var5) ;
        var4.(var5) <- Bdd.xor var4.(var5) !var3 ;
        let var6 = Bdd.dor xs.(var5) ys.(var5) in
        let var6 = Bdd.dand var6 !var3 in
        let var7 = Bdd.dand xs.(var5) ys.(var5) in
        let var7 = Bdd.dor var7 var6 in
        var3 := var7
      done ;
      var4
    in
    match (x, y) with
    | BInt xs, BInt ys -> BInt (aux xs ys)
    | _ -> failwith "internal error (add)"

  (* Outdated. Compare with add above if uncommenting *)
  (* let sub (x: bdd_value) (y: bdd_value) : bdd_value =
     let aux xs ys =
      let var3 = ref (Bdd.dfalse mgr) in
      let var4 = Array.make 32 (Bdd.dfalse mgr) in
      for var5 = 0 to Array.length xs - 1 do
        var4.(var5) <- Bdd.xor xs.(var5) ys.(var5) ;
        var4.(var5) <- Bdd.xor var4.(var5) !var3 ;
        let var6 = Bdd.dor xs.(var5) !var3 in
        let var7 = Bdd.dand (Bdd.dnot xs.(var5)) var6 in
        let var6 = Bdd.dand xs.(var5) ys.(var5) in
        let var6 = Bdd.dand var6 !var3 in
        let var6 = Bdd.dor var6 var7 in
        var3 := var6
      done ;
      var4
     in
     match (x, y) with
     | BInt xs, BInt ys -> BInt (aux xs ys)
     | _ -> failwith "internal error (sub)" *)

  let leq (x: t) (y: t) : t =
    let less x y = Bdd.dand (Bdd.dnot x) y in
    let aux xs ys =
      assert ((Array.length xs) = (Array.length ys));
      let acc = ref (Bdd.dtrue B.mgr) in
      for i = 0 to Array.length xs - 1 do
        let x = xs.(i) in
        let y = ys.(i) in
        acc := Bdd.dor (less x y) (Bdd.dand !acc (Bdd.eq x y))
      done ;
      !acc
    in
    match (x, y) with
    | BInt xs, BInt ys -> BBool (aux xs ys)
    | _ -> failwith "internal error (leq)"

  let lt (x: t) (y: t) : t =
    match (leq x y, eq x y) with
    | BBool b1, BBool b2 ->
      let b = Bdd.dand b1 (Bdd.dnot b2) in
      BBool b
    | _ -> failwith "internal error (lt)"

  let rec eval (env: t Env.t) (e: exp) : t =
    match e.e with
    | ETy (e1, _) -> eval env e1
    | EVar x -> (
        match Env.lookup_opt env x with
        | None -> failwith "internal error (eval)"
        | Some v -> v )
    | EVal v -> eval_value env v
    | EOp (op, es) -> (
        match (op, es) with
        | And, [e1; e2] -> eval_bool_op2 env Bdd.dand e1 e2
        | Or, [e1; e2] -> eval_bool_op2 env Bdd.dor e1 e2
        | Not, [e1] -> eval_bool_op1 env Bdd.dnot e1
        | Eq, [e1; e2] -> eq (eval env e1) (eval env e2)
        | UAdd _, [e1; e2] -> add (eval env e1) (eval env e2)
        | ULess _, [e1; e2] -> lt (eval env e1) (eval env e2)
        | ULeq _, [e1; e2] -> leq (eval env e1) (eval env e2)
        | USub _, [e1; e2] -> failwith "subtraction not implemented"
        | NLess, [e1; e2] -> lt (eval env e1) (eval env e2)
        | NLeq, [e1; e2] -> leq (eval env e1) (eval env e2)
        | _ -> failwith "unimplemented" )
    | EIf (e1, e2, e3) -> (
        let v1 = eval env e1 in
        let v2 = eval env e2 in
        let v3 = eval env e3 in
        match v1 with
        | BBool b -> ite b v2 v3
        | _ -> failwith "internal error (eval)" )
    | ELet (x, e1, e2) ->
      (* Printf.printf "ELet e1: %s\n" (show_exp ~show_meta:false e1); *)
      let v1 = eval env e1 in
      eval (Env.update env x v1) e2
    | ETuple es ->
      let vs = List.map (eval env) es in
      BTuple vs
    | ESome e -> BOption (Bdd.dtrue B.mgr, eval env e)
    | EMatch (e1, branches) -> (
        Printf.printf "Ematch e1: %s\n" (show_exp ~show_meta:false e1);
        let bddf = eval env e1 in
        let ((p,e), bs) = popBranch branches in
        let env, _ = eval_branch env bddf p in
        let x = eval env e in
        let env, x =
          foldBranches (fun (p,e) (env, x) ->
              let env, cond = eval_branch env bddf p in
              (env, ite cond (eval env e) x))
            (env, x) bs
        in
        x )
    | EFun _ | EApp _ | ERecord _ | EProject _ -> failwith "internal error (eval)"

  and eval_branch env bddf p : t Env.t * Bdd.vt =
    match (p, bddf) with
    | PWild, _ -> (env, Bdd.dtrue B.mgr)
    | PVar v, _ -> (Env.update env v bddf, Bdd.dtrue B.mgr)
    | PBool true, BBool bdd -> (env, bdd)
    | PBool false, BBool bdd -> (env, Bdd.dnot bdd)
    | PInt i, BInt bi ->
      (* TODO: I'm pretty sure this works, but not entirely. *)
      if Integer.size i <> Array.length bi then
        (env, Bdd.dfalse B.mgr)
      else
        let cond = ref (Bdd.dtrue B.mgr) in
        for j = 0 to Integer.size i - 1 do
          let b = B.get_bit i j in
          let bdd = if b then bi.(j) else Bdd.dnot bi.(j) in
          cond := Bdd.dand !cond bdd
        done ;
        (env, !cond)
    | PTuple ps, BTuple bs ->
      let zip = List.combine ps bs in
      List.fold_left
        (fun (env, pred) (p, b) ->
           let env', pred' = eval_branch env b p in
           (env', Bdd.dand pred pred') )
        (env, Bdd.dtrue B.mgr)
        zip
    | POption None, BOption (tag, bo) -> (env, Bdd.dnot tag)
    | POption (Some p), BOption (tag, bo) ->
      let env, cond = eval_branch env bo p in
      (env, Bdd.dand tag cond)
    | _ -> failwith "internal error (eval_branch)"

  and eval_bool_op1 env f e1 =
    let v1 = eval env e1 in
    match v1 with
    | BBool b1 -> BBool (f b1)
    | _ -> failwith "internal error (eval)"

  and eval_bool_op2 env f e1 e2 =
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    match (v1, v2) with
    | BBool b1, BBool b2 -> BBool (f b1 b2)
    | _ -> failwith "internal error (eval)"

  and eval_value env (v: value) =
    match v.v with
    | VUnit -> BBool (bdd_of_bool true) (* Encode as boolean *)
    | VBool b -> BBool (bdd_of_bool b)
    | VInt i ->
      let bs =
        Array.init (Integer.size i) (fun j ->
            let bit = B.get_bit i j in
            bdd_of_bool bit )
      in
      BInt bs
    | VNode n ->
      eval_value env (value (VInt (Integer.create ~size:32 ~value:n)))
    | VEdge (n1, n2) ->
      eval_value env (value (VTuple [value (VNode n1); value (VNode n2)]))
    | VOption None ->
      let ty =
        match get_inner_type (oget v.vty) with
        | TOption ty -> ty
        | _ -> failwith "internal error (eval_value)"
      in
      let dv = BddMap.default_value ty in
      BOption (Bdd.dfalse B.mgr, eval_value env dv)
    | VOption (Some v) -> BOption (Bdd.dtrue B.mgr, eval_value env v)
    | VTuple vs -> BTuple (List.map (eval_value env) vs)
    | VMap _ | VClosure _ | VRecord _ -> failwith "internal error (eval_value)"
end

let default_value = BddMap.default_value
