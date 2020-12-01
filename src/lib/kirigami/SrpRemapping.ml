(* Convert all edges and nodes in the program to new values,
   after the SRP has been split *)
open Batteries
open Nv_datastructures.AdjGraph
open Nv_lang.Syntax
open Nv_transformations
open Nv_datastructures

(* Describe how the transfer function should be decomposed.
 * Some types of networks require different settings of this,
 * depending on how they transfer routes.
 * Figuring that out is future work. *)
type transcomp =
  (* Perform the original transfer on the base~output edge,
   * and set the transfer on the input~base edge to the identity. *)
  | OutputTrans
  (* Perform the original transfer on the input~base edge,
   * and set the transfer on the base~output edge to the identity. *)
  | InputTrans
  (* Decompose the original transfer into two parts e1 and e2.
   * Not yet implemented. *)
  | Decomposed of exp * exp

(** A type for keeping track of the input to base and output to base relationships. *)
type interface = {
  (* Key: input node, value: base node *)
  inputs: Vertex.t VertexMap.t;
  (* Key: output node, value: base node *)
  outputs: Vertex.t VertexMap.t;
}

let empty_interface : interface = {
  inputs = VertexMap.empty;
  outputs = VertexMap.empty;
}

(* A record for managing the input node information *)
type input_exp = {
  (* the associated base node *)
  base: V.t;
  (* the variable associated with the input node *)
  var: Var.t;
  (* the rank of the associated output *)
  rank: int;
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
  (* the rank of the partitioned SRP *)
  rank: int;
  (* the number of nodes in the network *)
  nodes: int;
  (* the edges in the network *)
  edges: Edge.t list;
  (* keys are old nodes, values are Some new node or None *)
  node_map: (Vertex.t option) VertexMap.t;
  (* keys are old edges, values are Some new edge or None *)
  edge_map: (Edge.t option) EdgeMap.t;
  (* Maps from input and output nodes to their
   * corresponding base nodes and predicates:
   * the predicate applies to the input node as a `require`
   * on the hypothesis symbolic variable, and to the
   * output node as an `assert` on the solution
  *)
  inputs: input_exp VertexMap.t;
  outputs: (Vertex.t * exp option) VertexMap.t;
  trans: transcomp;
}

(** Map each vertex in the list of vertices to a partition number.
 *  Return the map and the number of partitions.
*)
let map_vertices_to_parts vertices (partf: Vertex.t -> int) : (int VertexMap.t * int) =
  let add_vertex (m, a) v =
    let vnum = partf v in
    (* add the vertex and its partition mapping,
     * and increase the map number if it is the new largest mapping *)
    (VertexMap.add v vnum m, max vnum a)
  in
  List.fold_left add_vertex (VertexMap.empty, 0) vertices

(** Return a list of [n] maps from old vertices to new vertices,
 *  divided according to their mappings, along with the number of new vertices
 *  in each.
 *  If an old vertex u is found in a given SRP, then its value will
 *  be Some v, where v is the new name for u.
 *  If not, its value will be None.
*)
let divide_vertices vmap nlists : (int * (Vertex.t option VertexMap.t)) list =
  let initial = List.make nlists (0, VertexMap.empty) in
  (* add the vertex to the corresponding map and set it to None elsewhere *)
  let place_vertex vertex srp_ix l =
    List.mapi (fun lix (n, vmaps) ->
        (
          n + (if (lix = srp_ix) then 1 else 0),
          (* the new vertex is the old total number *)
          VertexMap.add vertex (if (lix = srp_ix) then Some n else None) vmaps
        )) l
  in
  VertexMap.fold place_vertex vmap initial


(* Type for distinguishing cross edges from internal edges *)
type srp_edge =
  (* Internal i: represents an edge internal to an SRP [i] *)
  | Internal of int
  (* Cross i j: represents an edge that crosses from SRP [i] to SRP [j] *)
  | Cross of int * int

(** Return the remapped form of the given edge along with the SRPs it belongs to.
*)
let remap_edge edge (vmaps: (int * (Vertex.t option VertexMap.t)) list) : (Edge.t * srp_edge) =
  let (u, v) = edge in
  (* For the given old vertex, find the associated new vertex *)
  let find_endpoint vertex =
    let wrap_srp j = Option.map (fun i -> (i, j)) in
    let found = (List.filteri_map (fun j (_, m) -> wrap_srp j (VertexMap.find_default None vertex m)) vmaps) in
    assert ((List.length found) = 1);  (* only one SRP should contain the endpoint *)
    List.hd found
  in
  let (newu, usrp) = find_endpoint u in
  let (newv, vsrp) = find_endpoint v in
  if (usrp != vsrp) then
    (* cross-partition case *)
    ((newu, newv), Cross (usrp, vsrp))
  else
    ((newu, newv), Internal usrp)

(** Add the edge to the relevant list(s).
 * Internal edges get added to the single list that matches their
 * srp_edge.
 * A cross edge (u,v) instead gets split and added to two lists:
 * one for the (u, y) edge and another for the (x, v) edge.
*)
let map_edges_to_parts predf partitions (old_edge, (edge, srp_edge)) =
  let add_edge j partition =
    match srp_edge with
    | Internal i' -> {
        partition with edges = if i' = j then edge :: partition.edges else partition.edges;
                       edge_map = EdgeMap.add old_edge (if i' = j then Some edge else None) partition.edge_map;
      }
    | Cross (i1, i2) -> begin
        let pred : exp option = predf old_edge in
        let (u, v) = edge in
        (* output case *)
        if i1 = j then
          (* new node number *)
          let outnode = partition.nodes in
          let new_edge = Edge.create u () outnode in
          {
            partition with nodes = partition.nodes + 1;
                           edges = new_edge :: partition.edges;
                           edge_map = EdgeMap.add old_edge (Some new_edge) partition.edge_map;
                           outputs = VertexMap.add outnode (u, pred) partition.outputs;
          }
        else
          (* input case *)
        if i2 = j then
          (* new node number *)
          let innode = partition.nodes in
          let new_edge = Edge.create innode () v in
          (* construct the record of the new input information: used when creating the
           * symbolic variable and the require predicate *)
          let input_exp = {
            base = v;
            var = Var.fresh (Printf.sprintf "hyp_%s" (Edge.to_string old_edge));
            rank = i1;
            pred;
          } in
          {
            partition with nodes = partition.nodes + 1;
                           edges = new_edge :: partition.edges;
                           edge_map = EdgeMap.add old_edge (Some new_edge) partition.edge_map;
                           inputs = VertexMap.add innode input_exp partition.inputs;
          }
          (* neither case, mark edge as absent and continue *)
        else {
          partition with edge_map = EdgeMap.add old_edge None partition.edge_map;
        }
      end
  in
  List.mapi add_edge partitions

(** Map each edge in edges to a partitioned_srp based on where its endpoints lie. *)
let divide_edges
    (edges: Edge.t list)
    (predf: Edge.t -> exp option)
    (vmaps: (int * (Vertex.t option VertexMap.t)) list)
    (trans: transcomp)
  : (partitioned_srp list)
  =
  let partitioned_srp_from_nodes rank (nodes, node_map) =
    { rank; nodes; edges = []; node_map; edge_map = EdgeMap.empty; inputs = VertexMap.empty; outputs = VertexMap.empty; trans; }
  in
  let initial = List.mapi partitioned_srp_from_nodes vmaps in
  let new_edges = List.map (fun e -> (e, remap_edge e vmaps)) edges in
  List.fold_left (map_edges_to_parts predf) initial new_edges

(** Generate a list of partitioned_srp from the given list of nodes and edges,
 * along with their partitioning function and interface function.
*)
let partition_edges (nodes: Vertex.t list) (edges: Edge.t list) (partf: Vertex.t -> int) (intf: Edge.t -> exp option) (trans: transcomp) =
  let (node_srp_map, num_srps) = map_vertices_to_parts nodes partf in
  (* add 1 to num_srps to convert from max partition # to number of SRPS *)
  let divided_nodes = divide_vertices node_srp_map (num_srps + 1) in
  divide_edges edges intf divided_nodes trans

let ty_transformer _ ty = Some ty

let pattern_transformer (part_srp: partitioned_srp) (_: Transformers.recursors) p t =
  match (p, t) with
  | (PNode n, TNode) -> begin let new_node = VertexMap.find_default None n part_srp.node_map in
      Option.map (fun n -> PNode n) new_node end
  | (PEdge (PNode n1, PNode n2), TEdge) -> begin
      let new_edge = EdgeMap.find_default None (n1, n2) part_srp.edge_map in
      Option.map (fun (n1, n2) -> PEdge (PNode n1, PNode n2)) new_edge
    end
  | _ -> None

let value_transformer (part_srp: partitioned_srp) _ v =
  let make_node n = avalue (vnode n, Some TNode, v.vspan) in
  let make_edge e = avalue (vedge e, Some TEdge, v.vspan) in
  match v.v with
  | VNode n -> let new_node = VertexMap.find_default None n part_srp.node_map in
    Option.map (fun n -> make_node n) new_node
  | VEdge e  -> let new_edge = EdgeMap.find_default None e part_srp.edge_map in
    Option.map (fun e -> make_edge e) new_edge
  | _ -> None

let exp_transformer _ _ = None

let map_back_transformer (_part_srp: partitioned_srp) _ _ v _ =
  (* TODO: not yet implemented *)
  Some v

(* not yet implemented *)
let mask_transformer _ _ v _ = Some v

let make_toplevel (part_srp: partitioned_srp) (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer ~name:"RemapSrp" ty_transformer (pattern_transformer part_srp) (value_transformer part_srp)
    exp_transformer (map_back_transformer part_srp) mask_transformer

let remap_declarations part_srp = make_toplevel part_srp Transformers.transform_declarations
let remap_net part_srp = make_toplevel part_srp Transformers.transform_network
let remap_srp part_srp = make_toplevel part_srp Transformers.transform_srp
