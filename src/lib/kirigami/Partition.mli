(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures
open Nv_lang
open Nv_lang.Syntax
open Nv_solution.Solution

(** Separation of the purposes of the declarations
 ** for a given partitioned SRP. *)
type partitioned_decls =
  { (* new DSymbolic decls *)
    (* symbolics: declaration list; *)
    (* new DRequire decls and their corresponding partition ranks *)
    lesser_hyps : declaration list
  ; greater_hyps : declaration list
  ; (* new DAssert decls for checking hypotheses *)
    guarantees : declaration list
  ; (* old DAssert decls for testing network properties *)
    properties : declaration list
  ; (* all other network decls, including those defining essential behaviour (solution, topology) *)
    network : declaration list
  ; (* number of base nodes in partition *)
    base_nodes : int
  }

val of_decls : declaration list -> partitioned_decls

(** Create a list of Syntax.declarations,
 * where a new set of declarations for a given network is produced
 * for each possible partition in the given declarations.
 * Also return a set identifying which asserts and requires are added as part of kirigami,
 ** and which are part of the base declarations.
*)
val divide_decls : Cmdline.t -> declarations -> partitioned_decls list

val lift : (declarations -> declarations) -> partitioned_decls -> partitioned_decls

val lift_mb
  :  (declarations -> declarations * map_back)
  -> partitioned_decls
  -> partitioned_decls * map_back

val partitions_to_string : ?show_types:bool -> partitioned_decls -> string
