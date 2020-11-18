open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Nv_utils.PrimitiveCollections
open Nv_lang
open Nv_lang.Syntax
open TransformDecls
open Nv_interpreter
open Nv_utils.OCamlUtils
open SrpRemapping

(** Separation of the purposes of the declarations
 ** for a given partitioned SRP. *)
type partitioned_decls =
  { (* new DSymbolic decls *)
    (* symbolics : declaration list *)
    (* new DRequire decls and their corresponding partition ranks *)
    lesser_hyps : declaration list
  ; greater_hyps : declaration list
  ; (* new DAssert decls for checking hypotheses *)
    guarantees : declaration list
  ; (* old DAssert decls for testing network properties *)
    properties : declaration list
  ; (* all other network decls, including those defining essential behaviour (init, trans, merge) *)
    network : declaration list
  ; (* number of base nodes in partition *)
    base_nodes : int
  }

let of_decls d =
  let base_nodes = get_nodes d |> oget in
  { lesser_hyps = []
  ; greater_hyps = []
  ; guarantees = []
  ; properties = []
  ; network = d
  ; base_nodes
  }
;;

(** Helper function to extract the partition index
 *  from the partition expression.
*)
let interp_partition parte node : int =
  let value = Interp.apply empty_env (deconstructFun parte) (vnode node) in
  int_of_val value |> Option.get
;;

type transform_result =
  | Network of declaration
  | Solution of (declaration * declaration list * declaration list * declaration list)
  | Property of declaration
  | None

(* Return a transformed version of the given declaration, and optionally any new Kirigami constraints
 * that need to be added with it. *)
let transform_declaration parted_srp decl : transform_result =
  let ({ nodes; edges; rank; _ } : partitioned_srp) = parted_srp in
  match decl with
  | DNodes _ -> Network (DNodes nodes)
  | DEdges _ -> Network (DEdges edges)
  | DSolve s ->
    let solve', assert', reqs = transform_solve s parted_srp in
    let sort_hyp exp r (lt, gt) =
      if r < rank then DRequire exp :: lt, gt else lt, DRequire exp :: gt
    in
    let lesser_req_decls, greater_req_decls = Map.foldi sort_hyp reqs ([], []) in
    Solution
      ( DSolve solve'
      , List.map (fun e -> DAssert e) assert'
      , lesser_req_decls
      , greater_req_decls )
  | DPartition _ -> None
  | DAssert e -> Property (DAssert (transform_assert e parted_srp))
  | _ -> Network decl
;;

(** Create a list of lists of declarations representing a network which has been
 * opened along the edges described by the partition and interface declarations.
 * @return a new list of lists of declarations
*)
let divide_decls (cfg : Cmdline.t) (decls : declarations) : partitioned_decls list =
  let partition = get_partition decls in
  match partition with
  | Some parte ->
    let attr_type = get_attr_type decls |> Option.get in
    (* get the parameters for partition_edges *)
    let nodes = get_nodes decls |> Option.get in
    let node_list = List.range 0 `To (nodes - 1) in
    let edges = get_edges decls |> Option.get in
    (* interpret partition function *)
    let partf : Vertex.t -> int = interp_partition parte in
    let partitioned_srps = partition_edges node_list edges partf in
    let create_new_decls parted_srp =
      (* TODO: node_map and edge_map describe how to remap each node and edge in the new SRP.
       * To transform more cleanly, we can run a toplevel transformer on the SRP, replacing
       * each edge and node in the map with the new value if it's Some,
       * and removing it if it's None (where the edge/node is explicitly used).
       *)
      (* Print mapping from old nodes to new nodes *)
      if cfg.print_remap
      then (
        let remap_node v =
          match v with
          | Some v -> string_of_int v
          | None -> "cut"
        in
        print_endline @@ VertexMap.to_string remap_node parted_srp.node_map)
      else ();
      (* count the number of base nodes *)
      let base_nodes =
        VertexMap.fold
          (fun _ v acc -> acc + if Option.is_some v then 1 else 0)
          parted_srp.node_map
          0
      in
      let add_symbolics _ { var; _ } l = DSymbolic (var, Ty attr_type) :: l in
      let symbolics = VertexMap.fold add_symbolics parted_srp.inputs [] in
      (* replace relevant old declarations *)
      let transformed_decls = List.map (transform_declaration parted_srp) decls in
      (* divide up the declarations as appropriate *)
      let rec split_decls (net, guar, lt_hyp, gt_hyp, prop) l =
        match l with
        | [] -> net, guar, lt_hyp, gt_hyp, prop
        | h :: t ->
          begin
            match h with
            | Network d -> split_decls (d :: net, guar, lt_hyp, gt_hyp, prop) t
            | Solution (d, g, lh, gh) ->
              split_decls (d :: net, g @ guar, lh @ lt_hyp, gh @ gt_hyp, prop) t
            | Property p -> split_decls (net, guar, lt_hyp, gt_hyp, p :: prop) t
            | None -> split_decls (net, guar, lt_hyp, gt_hyp, prop) t
          end
      in
      let network, guarantees, lesser_hyps, greater_hyps, properties =
        split_decls ([], [], [], [], []) transformed_decls
      in
      { lesser_hyps
      ; greater_hyps
      ; guarantees
      ; properties
      ; network = symbolics @ network
      ; base_nodes
      }
    in
    List.map create_new_decls partitioned_srps
  | None -> [of_decls decls]
;;

let lift (f : declarations -> declarations) decls =
  { decls with
    lesser_hyps = f decls.lesser_hyps
  ; greater_hyps = f decls.greater_hyps
  ; guarantees = f decls.guarantees
  ; properties = f decls.properties
  ; network = f decls.network
  }
;;

let lift_mb (f : declarations -> declarations * Nv_solution.Solution.map_back) decls =
  (* TODO: drop unnecessary map back functions: possibly all but network *)
  let lh, _lhf = f decls.lesser_hyps in
  let gh, _ghf = f decls.greater_hyps in
  let g, _gf = f decls.guarantees in
  let p, _pf = f decls.properties in
  let n, nf = f decls.network in
  ( { decls with
      lesser_hyps = lh
    ; greater_hyps = gh
    ; guarantees = g
    ; properties = p
    ; network = n
    }
  , nf )
;;

let partitions_to_string ?(show_types = false) decls =
  let { lesser_hyps; greater_hyps; guarantees; properties; network; _ } = decls in
  let print = Printing.declarations_to_string ~show_types in
  print network
  ^ "\n"
  ^ print properties
  ^ "\n"
  ^ print lesser_hyps
  ^ "\n"
  ^ print greater_hyps
  ^ "\n"
  ^ print guarantees
;;
