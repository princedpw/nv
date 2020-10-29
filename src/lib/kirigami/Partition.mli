(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures
open Nv_lang
open Nv_lang.Syntax

(** Create a list of Syntax.declarations,
 * where a new set of declarations for a given network is produced
 * for each possible partition in the given declarations.
 * Also return a set identifying which asserts and requires are added as part of kirigami,
 ** and which are part of the base declarations.
*)
val divide_decls : Cmdline.t -> declarations -> base_check:bool -> (declarations * exp Set.t) list
