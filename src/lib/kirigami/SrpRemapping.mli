open Nv_lang.Syntax
open Nv_datastructures.AdjGraph
open Nv_datastructures
open Nv_solution

(* A record for managing the input node information *)
type input_exp =
  { (* the associated original edge *)
    edge : E.t
  ; (* the associated base node *)
    base : Vertex.t
  ; (* the variable associated with the input node *)
    var : Var.t
  ; (* the partition rank of the associated output *)
    rank : int
  ; (* the associated predicate expression: a function over attributes *)
    (* optional: if not given, then assumed to always hold *)
    pred : exp option
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
type partitioned_srp =
  { (* the rank of the partitioned srp *)
    rank : int
  ; (* the number of nodes in the network *)
    nodes : int
  ; (* the edges in the network *)
    edges : Edge.t list
  ; (* keys are old nodes, values are Some new node or None *)
    node_map : Vertex.t option VertexMap.t
  ; (* keys are old edges, values are Some new edge or None *)
    edge_map : Edge.t option EdgeMap.t
  ; (* Maps from base nodes to their inputs and outputs *)
    (* the predicate applies to the input node as a `require`
     * on the hypothesis symbolic variable, and to the
     * output node as an `assert` on the solution
     *)
    (* map from input nodes to their base node *)
    inputs : input_exp VertexMap.t
  ; (* map from base nodes to their outputs *)
    outputs : (Edge.t * exp option) list VertexMap.t
  }

val partition_edges
  :  Vertex.t list
  -> Edge.t list
  -> (Vertex.t -> int)
  -> partitioned_srp list
