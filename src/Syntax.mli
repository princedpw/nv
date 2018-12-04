open Cudd

type index = int

type bitwidth = int

type level = int

type tyname = Var.t

type ty =
  | TVoid
  | TVar of tyvar ref
  | QVar of tyname
  | TBool
  | TInt of bitwidth
  | TArrow of ty * ty
  | TTuple of ty list
  | TOption of ty
  | TMap of ty * ty

and tyvar = Unbound of tyname * level | Link of ty

type var = Var.t

type op =
  | And
  | Or
  | Not
  | UAdd of bitwidth
  | USub of bitwidth
  | UEq
  | ULess of bitwidth
  | ULeq of bitwidth
  | MCreate
  | MGet
  | MSet
  | MMap
  | MMapFilter
  | MMerge

type pattern =
  | PWild
  | PVar of var
  | PBool of bool
  | PInt of Integer.t
  | PTuple of pattern list
  | POption of pattern option

type v = private
  | VBool of bool
  | VInt of Integer.t
  | VMap of mtbdd
  | VTuple of value list
  | VOption of value option
  | VClosure of closure

and mtbdd = value Mtbdd.t * ty

and value = private
  {v: v; vty: ty option; vspan: Span.t; vtag: int; vhkey: int}

and e = private
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

and exp = private
  {e: e; ety: ty option; espan: Span.t; etag: int; ehkey: int}

and branches = (pattern * exp) list

and func = {arg: var; argty: ty option; resty: ty option; body: exp}

and closure = env * func

and env = {ty: ty Env.t; value: value Env.t}

and ty_or_exp = Ty of ty | Exp of exp

type declaration =
  | DLet of var * ty option * exp
  | DSymbolic of var * ty_or_exp
  | DATy of ty
  | DMerge of exp
  | DTrans of exp
  | DInit of exp
  | DAssert of exp
  | DRequire of exp
  | DNodes of Integer.t
  | DEdges of (Integer.t * Integer.t) list

type declarations = declaration list

(* Constructors *)

val vbool : bool -> value

val vint : Integer.t -> value

val vmap : mtbdd -> value

val vtuple : value list -> value

val voption : value option -> value

val vclosure : closure -> value

val evar : var -> exp

val e_val : value -> exp

val eop : op -> exp list -> exp

val efun : func -> exp

val eapp : exp -> exp -> exp

val eif : exp -> exp -> exp -> exp

val elet : Var.t -> exp -> exp -> exp

val etuple : exp list -> exp

val esome : exp -> exp

val ematch : exp -> branches -> exp

val ety : exp -> ty -> exp

(* Utilities *)

val arity : op -> int

val tint_of_size : int -> ty

val tint_of_value : Integer.t -> ty

val exp : e -> exp

val value : v -> value

val aexp : exp * ty option * Span.t -> exp

val avalue : value * ty option * Span.t -> value

val annot : ty -> exp -> exp

val annotv : ty -> value -> value

val wrap : exp -> exp -> exp

val exp_of_v : v -> exp

val exp_of_value : value -> exp

val func : var -> exp -> func

val lam : var -> exp -> exp

val is_value : exp -> bool

val to_value : exp -> value

val oget : 'a option -> 'a

val omap : ('a -> 'b) -> 'a option -> 'b option

val lams : var list -> exp -> exp

val apps : exp -> exp list -> exp

val apply_closure : closure -> value list -> exp

val get_attr_type : declarations -> ty option

val get_merge : declarations -> exp option

val get_trans : declarations -> exp option

val get_init : declarations -> exp option

val get_assert : declarations -> exp option

val get_edges : declarations -> (Integer.t * Integer.t) list option

val get_nodes : declarations -> Integer.t option

val get_symbolics : declarations -> (var * ty_or_exp) list

val get_requires : declarations -> exp list

val equal_values : cmp_meta:bool -> value -> value -> bool

val hash_value : hash_meta:bool -> value -> int

(* Operates only on the 'v' element of the value records, ignoring
   all other entries *)
val compare_vs : value -> value -> int

(* As above, but for exps *)
val compare_es : exp -> exp -> int

(* Operates on all entries in the value records *)
val compare_values : value -> value -> int

(* As above, but for exps *)
val compare_exps : exp -> exp -> int

(* Actual equality. For equivalence, consider using
   Typing.equiv_tys instead *)
val equal_tys : ty -> ty -> bool

val show_exp : exp -> string

val get_inner_type : ty -> ty

val free : Var.t BatSet.PSet.t -> exp -> Var.t BatSet.PSet.t

module type MEMOIZER = sig
  type t

  val memoize : size:int -> (t -> 'a) -> t -> 'a
end

module MemoizeValue : MEMOIZER with type t = value

module MemoizeExp : MEMOIZER with type t = exp

module BddMap : sig
  type t = mtbdd

  val create : key_ty:ty -> value -> t

  val map :
    op_key:exp * value BatSet.PSet.t -> (value -> value) -> t -> t

  val map_when :
    op_key:exp * value BatSet.PSet.t
    -> bool Mtbdd.t
    -> (value -> value)
    -> t
    -> t

  val merge :
    ?opt:value * value * value * value
    -> op_key:exp * value BatSet.PSet.t
    -> (value -> value -> value)
    -> t
    -> t
    -> t

  val find : t -> value -> value

  val update : t -> value -> value -> t

  val bindings : t -> (value * value) list * value

  val from_bindings : key_ty:ty -> (value * value) list * value -> t

  val equal : t -> t -> bool
end

module BddFunc : sig
  type t =
    | BBool of Bdd.vt
    | BInt of Bdd.vt array
    | BTuple of t list
    | BOption of Bdd.vt * t

  val create_value : ty -> t

  val eval : t Env.t -> exp -> t

  val eval_value : t Env.t -> value -> t

  val wrap_mtbdd : Bdd.vt -> bool Mtbdd.t
end

val default_value : ty -> value
