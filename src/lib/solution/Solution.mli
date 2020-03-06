open Nv_datastructures.AdjGraph
open Nv_lang.Collections
open Nv_lang.Syntax

type sol = {sol_val: value; mask : value option}
type t =
  { symbolics: value VarMap.t;
    solves: sol VarMap.t;
    assertions: bool list; (* One for each assert statement *)
    labels: value VertexMap.t; (* Deprecated -- included only for backwards compatibility *)
  }

type map_back = t -> t

val print_masked_type : ty -> sol -> string

val print_solution : t -> unit

val mask_type_ty : ty -> ty
(* val mask_type_sol : t -> ty *)
(* Given a value, creates a mask where every part of the value is displayed *)
val value_to_mask : value -> value
