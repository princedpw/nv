open Nv_datastructures.AdjGraph
open Nv_lang.Syntax

(***
 * Functions to rewrite network declarations to include cases added by partitioning.
 ***)
(* Wrap the given init exp in a new exp of the form:
 * match x with
 * | out -> init u
 * | in -> init u
 * | _ -> init x
 * where the edge u~v has been partitioned into u~out and in~v.
*)
val transform_init : (exp) -> (SrpRemapping.interface) -> (exp EdgeMap.t) -> (Vertex.t option VertexMap.t) -> (exp)

(* Wrap the given trans exp in a new exp of the form:
 * match e with
 * | u~out -> a
 * | in~v -> trans u~v a
 * | _ -> trans e a
 * where the edge u~v has been partitioned into u~out and in~v.
 * Note that the `trans u~v a` case is pulled from the previous exp.
*)
val transform_trans : (exp) -> (SrpRemapping.interface) -> (Edge.t option EdgeMap.t) -> (exp)

(* NOTE: this function appears to be unnecessary in practice *)
(* Wrap the given merge exp in a new exp of the form:
 * match n with
 * | out -> y
 * | in -> x
 * | _ -> merge n x y
 * where the edge u~v has been partitioned into u~out and in~v.
*)
val transform_merge : (exp) -> (SrpRemapping.interface) -> (Vertex.t option VertexMap.t) -> (exp)

(* Wrap the given assert exp in a new exp that also checks the input and output nodes
 * of the partitioned network.
 * Output nodes are tested against the assumptions on the associated input nodes.
 * Input nodes do not have any associated checks (since their value is assumed).
 * The form of the new exp is:
 * let assert n x =
 * match n with
 * | out -> p x
 * | in -> true
 * | _ -> assert n x
 * where p is a predicate used in the require clause
*)
val transform_assert : (exp option) -> (SrpRemapping.interface) -> (Vertex.t option VertexMap.t) -> exp