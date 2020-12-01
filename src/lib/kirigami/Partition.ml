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


(** Helper function to extract the edge predicate
 *  from the interface expression.
*)
let interp_interface intfe e : exp option =
  let intf_app = Interp.apply empty_env (deconstructFun intfe) (vedge e) in
  (* if intf_app is not an option, or if the value it contains is not a function,
   * fail *)
  match intf_app with
  | {v = VOption o; _} -> begin match o with
      | Some {v = VClosure (_env, func); _ } -> Some (efunc func)
      | Some _ -> failwith "expected a closure, got something else instead!"
      (* infer case *)
      | None -> None
    end
  | _ -> failwith "intf value is not an option; did you type check the input?"

(** Helper function to extract the partition index
 *  from the partition expression.
*)
let interp_partition parte node : int =
  let value = Interp.apply empty_env (deconstructFun parte) (vnode node)
  in (int_of_val value) |> Option.get


(** Helper function to unwrap the predicate. *)
let unwrap_pred maybe_pred = match maybe_pred with
  | Some pred -> pred (* the interface is an efun *)
  (* Make the predicate a function that ignores its argument *)
  | None -> annot TBool (e_val (vbool true))

let transform_declaration parted_srp attr_type ~(base_check: bool) decl =
  let { nodes; edges; _ } : partitioned_srp = parted_srp in
  match decl with
  | DNodes _ -> Some (DNodes nodes)
  | DEdges _ -> Some (DEdges edges)
  | DInit init -> begin
      (* let input_exps = EdgeMap.map (fun (v, _) -> (evar v)) input_hyps in *)
      Some (DInit (transform_init init attr_type parted_srp))
    end
  | DTrans trans -> Some (DTrans (transform_trans trans attr_type parted_srp))
  (* FIXME: merge is screwy; currently an output node on the destination won't update since it
    * gets initialized with the destination's value, which is already the best *)
  | DMerge merge -> Some (DMerge (transform_merge merge attr_type parted_srp))
  | DAssert assertion -> begin
      (* let output_preds = filter_preds intf.outputs preds in *)
      (* if performing the base check, drop assertions on the base nodes *)
      if base_check then
        None
      else
        Some (DAssert (transform_assert (Some assertion) attr_type parted_srp))
    end
  | DPartition _ -> None
  | DInterface _ -> None
  | _ -> Some decl

(** Create a list of lists of declarations representing a network which has been
 * opened along the edges described by the partition and interface declarations.
 * @return a new list of lists of declarations
*)
let divide_decls (cfg: Cmdline.t) (decls: declarations) ~(base_check: bool) : declarations list =
  let partition = get_partition decls in
  match partition with
  | Some parte -> begin
      let attr_type = get_attr_type decls |> Option.get in
      (* get the parameters for partition_edges *)
      let interface = get_interface decls in
      let nodes = get_nodes decls |> Option.get in
      let node_list = List.range 0 `To (nodes - 1) in
      let edges = get_edges decls |> Option.get in
      (* interpret partition and interface functions *)
      let partf : (Vertex.t -> int) = interp_partition parte in
      let intf_opt : (Edge.t -> exp option) =
        match interface with
        | Some intfe -> (interp_interface intfe)
        | None -> fun (_: Edge.t) -> None
      in
      (* TODO: change this to a cmdline parameter *)
      let tcomp : transcomp = OutputTrans in
      let partitioned_srps = partition_edges node_list edges partf intf_opt tcomp in
      let create_new_decls (parted_srp : partitioned_srp) : declarations =
        (* TODO: node_map and edge_map describe how to remap each node and edge in the new SRP.
         * To transform more cleanly, we can run a toplevel transformer on the SRP, replacing
         * each edge and node in the map with the new value if it's Some,
         * and removing it if it's None * (where the edge/node is explicitly used).
         * We can then add code to handle adding in the new input and output nodes to the SRP.
         * (the input and output edges are handled by edge_map).
        *)
        (* Print mapping from old nodes to new nodes *)
        if cfg.print_remap then
          let remap_node v = match v with
            | Some v -> string_of_int v
            | None -> "cut"
          in
          print_endline @@ VertexMap.to_string remap_node parted_srp.node_map
        else ();
        let add_symbolic _ ({var; _} : input_exp) l =
          DSymbolic (var, Ty attr_type) :: l
        in
        let new_symbolics = VertexMap.fold add_symbolic parted_srp.inputs [] in
        (* If we are generating a base check, then do not add any requires clauses *)
        let add_require _ ({var; pred; rank; _} : input_exp) (l1, l2) =
          match pred with
          | Some p ->
            let req = DRequire (annot TBool (eapp p (annot attr_type (evar var)))) in
            if rank < parted_srp.rank then (req :: l1, l2) else (l1, req :: l2)
          | None -> (l1, l2)
        in
        let lesser_hyps, greater_hyps =
          VertexMap.fold add_require parted_srp.inputs ([], [])
        in
        (* replace relevant old declarations *)
        let transformed_decls = List.filter_map (transform_declaration parted_srp attr_type ~base_check:base_check) decls in
        (* add the assertion in at the end if there wasn't an assert in the original decls *)
        let add_assert = match get_assert transformed_decls with
          | Some _ -> []
          | None -> [DAssert (transform_assert None attr_type parted_srp)]
        in
        (* also add requires at the end so they can use any bindings earlier in the file *)
        new_symbolics @ transformed_decls @ lesser_hyps @ greater_hyps @ add_assert
      in
      List.map create_new_decls partitioned_srps
    end
  | None -> [decls]
