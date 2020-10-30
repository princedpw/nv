open Nv_lang.Syntax
open Nv_datastructures.AdjGraph
open Nv_datastructures
open Nv_transformations
open Nv_solution

(* Describe how the transfer function should be decomposed.
 * Some types of networks require different settings of this,
 * depending on how they transfer routes.
 * Future work will involve providing the transcomp as part of
 * a solution (when an interface is provided) to describe how
 * to decompose the transfer function.
 *  Figuring that out is future work. *)
type transcomp =
  (* Decompose the original transfer e into two parts e1 and e2,
   * where e1 is performed on the base~output edge and e2 is
   * performed on the input~base edge. *)
  | Decomposed of exp * exp
  (* Shorthand for (Decomposed e identity). *)
  | OutputTrans
  (* Shorthand for (Decomposed identity e). *)
  | InputTrans

(* A record for managing the input node information *)
type input_exp = {
  (* the associated original edge *)
  edge: E.t;
  (* the variable associated with the input node *)
  var: Var.t;
  (* the associated predicate expression: a function over attributes *)
  (* optional: if not given, then assumed to always hold *)
  pred: exp option;
}

(** A type for transforming the declarations over the old SRP
 ** to declarations for the new partitioned SRP.
 ** The nodes and edges maps help us to remap nodes and edges.
 ** If an old node or edge is not a value in the map,
 ** then we know it has been removed and we can drop it from
 ** the SRP.
 ** The predicates help us keep track of the `interface` predicates
 ** associated with a given new edge, since both inputs and outputs
 ** have associated predicates (required on the hypotheses and
 ** asserted on the output solutions, respectively).
 **
 ** Invariants:
 ** - every value in node_map and edge_map is a valid node or edge
 **   in the new SRP
 **)
type partitioned_srp = {
  (* the number of nodes in the network *)
  nodes: int;
  (* the edges in the network *)
  edges: Edge.t list;
  (* keys are old nodes, values are Some new node or None *)
  node_map: (Vertex.t option) VertexMap.t;
  (* keys are old edges, values are Some new edge or None *)
  edge_map: (Edge.t option) EdgeMap.t;
  (* Maps from base nodes to their inputs and outputs *)
  (* the predicate applies to the input node as a `require`
   * on the hypothesis symbolic variable, and to the
   * output node as an `assert` on the solution
  *)
  inputs: (input_exp list) VertexMap.t;
  outputs: ((Edge.t * exp option) list) VertexMap.t;
  trans: transcomp;
}

val partition_edges : Vertex.t list -> Edge.t list -> (Vertex.t -> int) -> transcomp -> partitioned_srp list

val remap_declarations : partitioned_srp -> declarations -> (declarations * (Solution.t -> Solution.t))