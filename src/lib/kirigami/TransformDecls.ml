open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax
open Nv_interpreter
open SrpRemapping

let node_to_exp n = e_val (vnode n)
let edge_to_exp e = e_val (vedge e)
let node_to_pat node = exp_to_pattern (node_to_exp node)
let edge_to_pat edge = exp_to_pattern (edge_to_exp edge)

(* Create an annotated match statement *)
let amatch v t b = annot t (ematch (aexp (evar v, Some t, Span.default)) b)

(** Add match branches using the given map of old nodes to new nodes. *)
let match_of_node_map
    (m : Vertex.t option VertexMap.t)
    (f : Vertex.t -> Vertex.t -> exp)
    b
  =
  let add_node_branch old_node new_node branches =
    match new_node with
    | Some n -> addBranch (node_to_pat n) (f n old_node) branches
    | None -> branches
    (* if there is no new node, just map the old node to itself *)
    (* addBranch (node_to_pat old_node) (node_to_exp old_node) branches *)
  in
  VertexMap.fold add_node_branch m b
;;

(* Return a Let declaration of a function that maps from old nodes to new nodes. *)
let node_map_decl fnname (m : Vertex.t option VertexMap.t) =
  let node_var = Var.create "n" in
  let branches = match_of_node_map m (fun _ -> node_to_exp) emptyBranch in
  DLet
    ( Var.create fnname
    , Some (TArrow (TNode, TNode))
    , efun
        { arg = node_var
        ; argty = Some TNode
        ; resty = Some TNode
        ; body = ematch (evar node_var) branches
        } )
;;

(** Add match branches using the given map of old edges to new edges. *)
let match_of_edge_map (m : Edge.t option EdgeMap.t) b =
  let add_edge_branch old_edge new_edge branches =
    match new_edge with
    | Some e -> addBranch (edge_to_pat e) (edge_to_exp old_edge) branches
    | None -> branches
  in
  EdgeMap.fold add_edge_branch m b
;;

(* Return a Let declaration of a function that maps from old edges to new edges. *)
let edge_map_decl fnname (m : Edge.t option EdgeMap.t) =
  let edge_var = Var.create "e" in
  let branches = match_of_edge_map m emptyBranch in
  DLet
    ( Var.create fnname
    , Some (TArrow (TEdge, TEdge))
    , efun
        { arg = edge_var
        ; argty = Some TEdge
        ; resty = Some TEdge
        ; body = ematch (evar edge_var) branches
        } )
;;

(* Apply and partially interpret the given transfer function t on the given edge e and attribute value x. *)
let apply_trans ty e t x =
  let trans_app = eapp t (annot TEdge (edge_to_exp e)) in
  let trans_curried = annot (TArrow (ty, ty)) trans_app in
  (* partially interpret the transfer function *)
  InterpPartialFull.interp_partial (annot ty (eapp trans_curried x))
;;

(* Pass in the original init Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * a single parameter of type tnode.
 *)
let transform_init (init : exp) ty parted_srp : Syntax.exp =
  let ({ node_map; inputs; _ } : SrpRemapping.partitioned_srp) = parted_srp in
  let node_var = Var.fresh "node" in
  (* function we recursively call to build up the new base node init *)
  let add_input_branch u { var; _ } =
    let exp = annot ty (evar var) in
    addBranch (node_to_pat u) exp
  in
  let map_nodes _ old_node =
    InterpPartialFull.interp_partial_fun init [node_to_exp old_node]
  in
  let branches = match_of_node_map node_map map_nodes emptyBranch in
  let input_branches = VertexMap.fold add_input_branch inputs branches in
  (* the returned expression should be a function that takes a node as input with the following body:
   * a match with node as the exp and output_branches as the branches *)
  wrap
    init
    (efunc
       (funcFull node_var (Some TNode) (Some ty) (amatch node_var TNode input_branches)))
;;

(* Pass in the original trans Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * two parameters of types tedge and attribute
 *)
let transform_trans
    (e : exp)
    (intrans : exp option)
    (attr : ty)
    (parted_srp : SrpRemapping.partitioned_srp)
    : Syntax.exp
  =
  let ({ edge_map; inputs; _ } : SrpRemapping.partitioned_srp) = parted_srp in
  (* new function argument *)
  let edge_var = Var.fresh "edge" in
  let x_var = Var.fresh "x" in
  (* Simplify the old expression to an expression just over the second variable *)
  let interp_trans edge =
    InterpPartialFull.interp_partial (annot attr (apps e [edge; annot attr (evar x_var)]))
  in
  let add_input_branch u { base; edge; _ } =
    let var = annot attr (evar x_var) in
    let apply_intrans t v =
      InterpPartialFull.interp_partial (annot attr (apps t [edge_to_exp edge; v]))
    in
    let exp = Option.apply (Option.map apply_intrans intrans) var in
    addBranch (edge_to_pat (u, base)) exp
  in
  let edge_map_match = match_of_edge_map edge_map emptyBranch in
  let branches = mapBranches (fun (pat, edge) -> pat, interp_trans edge) edge_map_match in
  let input_branches = VertexMap.fold add_input_branch inputs branches in
  let x_lambda =
    efunc
      (funcFull
         x_var
         (Some attr)
         (Some attr)
         (annot attr (amatch edge_var TEdge input_branches)))
  in
  let lambda =
    efunc (funcFull edge_var (Some TEdge) (Some (TArrow (attr, attr))) x_lambda)
  in
  wrap e lambda
;;

let transform_merge (e : exp) (ty : ty) (parted_srp : SrpRemapping.partitioned_srp) : exp =
  let ({ node_map; inputs; _ } : SrpRemapping.partitioned_srp) = parted_srp in
  (* the internal type after matching on the node *)
  let inner_ty = TArrow (ty, TArrow (ty, ty)) in
  let node_var = Var.fresh "node" in
  (* Simplify the old expression to a smaller expression *)
  let interp_old old exp =
    InterpPartialFull.interp_partial (annot inner_ty (eapp old exp))
  in
  let branches =
    match_of_node_map node_map (fun _ old -> interp_old e (node_to_exp old)) emptyBranch
  in
  let add_input_branch u { edge; _ } =
    let _, v = edge in
    let exp = interp_old e (node_to_exp v) in
    addBranch (node_to_pat u) exp
  in
  let input_branches = VertexMap.fold add_input_branch inputs branches in
  wrap
    e
    (efunc
       (funcFull
          node_var
          (Some TNode)
          (Some inner_ty)
          (amatch node_var TNode input_branches)))
;;

(* Check that the solution's value at a particular output vertex satisfies the predicate. *)
let add_output_pred
    (trans : exp option)
    (attr : ty)
    (sol : exp)
    (n : Vertex.t)
    (edge, pred)
    acc
  =
  let sol_x = annot attr (eop MGet [sol; annot TNode (node_to_exp n)]) in
  match pred with
  | Some p ->
    InterpPartialFull.interp_partial
      (annot
         TBool
         (eapp p (Option.apply (Option.map (apply_trans attr edge) trans) sol_x)))
    :: acc
  | None -> acc
;;

(* Check each output's solution in the sol variable. *)
let outputs_assert
    (trans : exp option)
    (sol : exp)
    (attr : ty)
    (parted_srp : SrpRemapping.partitioned_srp)
    : exp list
  =
  let ({ outputs; _ } : SrpRemapping.partitioned_srp) = parted_srp in
  (* re-map every output to point to its corresponding predicate *)
  let add_preds n outputs acc =
    List.fold_left
      (fun acc output -> add_output_pred trans attr sol n output acc)
      acc
      outputs
  in
  VertexMap.fold add_preds outputs []
;;

let transform_assert (e : exp) (parted_srp : SrpRemapping.partitioned_srp) : exp =
  (* TODO: drop expressions or simplify them to true if they reference nodes we don't have access to *)
  (* NOTE: this may not even be occurring in the assert itself, but in another part of the program;
   * although maybe that's fine if it's already inlined *)
  (* count the number of base nodes *)
  let base_nodes =
    VertexMap.fold
      (fun _ v acc -> acc + if Option.is_some v then 1 else 0)
      parted_srp.node_map
      0
  in
  let v_base = annot TNode (e_val (vnode base_nodes)) in
  let node_var = Var.fresh "node" in
  let skip_input_fn ty body =
    let inner_fn = deconstructFun body in
    let inner_inner_fn = deconstructFun inner_fn.body in
    let sol_ty = inner_fn.argty in
    let acc_ty = inner_inner_fn.argty in
    let sol_var = Var.fresh "x" in
    let acc_var = Var.fresh "acc" in
    (* TODO: do we need to annotate these functions? *)
    let acc_id =
      efunc (funcFull acc_var acc_ty acc_ty (annot (acc_ty |> Option.get) (evar acc_var)))
    in
    let skip_fn = efunc (funcFull sol_var sol_ty inner_fn.resty acc_id) in
    let node_cmp = annot TBool (eop NLess [annot TNode (evar node_var); v_base]) in
    let if_exp = annot (ty |> Option.get) (eif node_cmp body skip_fn) in
    efunc (funcFull node_var (Some TNode) ty if_exp), acc_ty
  in
  match e.e with
  | EOp (MFoldNode, [fn; sol; acc]) ->
    let f = deconstructFun fn in
    let new_fn, resty = skip_input_fn f.resty f.body in
    annot (resty |> Option.get) (eop MFoldNode [new_fn; sol; acc])
  | _ -> e
;;

(** Helper function to extract the edge predicate
 *  from the interface expression.
*)
let interp_interface intfe e : exp option =
  let intf_app = Interp.apply empty_env (deconstructFun intfe) (vedge e) in
  (* if intf_app is not an option, or if the value it contains is not a function,
   * fail *)
  match intf_app with
  | { v = VOption o; _ } ->
    begin
      match o with
      | Some { v = VClosure (_env, func); _ } -> Some (efunc func)
      | Some _ -> failwith "expected a closure, got something else instead!"
      (* infer case *)
      | None -> None
    end
  | _ -> failwith "intf value is not an option; did you type check the input?"
;;

(* Transform the given solve and return it along with a new expression to assert
 * and new expressions to require. *)
let transform_solve solve (partition : SrpRemapping.partitioned_srp)
    : solve * exp list * (exp, int) Map.t
  =
  let ({ aty; var_names; init; trans; merge; interface; decomp } : solve) = solve in
  let intf_opt : Edge.t -> exp option =
    match interface with
    | Some intfe -> interp_interface intfe
    | None -> fun (_ : Edge.t) -> None
  in
  (* Update the partitioned_srp instance with the interface information *)
  let partition' =
    { partition with
      inputs =
        VertexMap.map
          (fun input_exp -> { input_exp with pred = intf_opt input_exp.edge })
          partition.inputs
    ; outputs =
        VertexMap.map
          (fun outputs -> List.map (fun (edge, _) -> edge, intf_opt edge) outputs)
          partition.outputs
    }
  in
  let attr_type = aty |> Option.get in
  (* NOTE: we don't perform any kind of verification that the decomposition is sound;
   * if we've got it, we use it! *)
  let outtrans, intrans =
    match decomp with
    | Some (lt, rt) -> lt, rt
    (* default behaviour: perform the transfer on the output side *)
    | None -> Some trans, None
  in
  let init' = transform_init init attr_type partition' in
  let trans' = transform_trans trans intrans attr_type partition' in
  let merge' = transform_merge merge attr_type partition' in
  (* TODO: should we instead create separate let-bindings to refer to init, trans and merge? *)
  let assertions = outputs_assert outtrans var_names attr_type partition' in
  let add_require _ { var; rank; pred; _ } m =
    match pred with
    | Some p -> Map.add (annot TBool (eapp p (annot attr_type (evar var)))) rank m
    | None -> m
  in
  let reqs = VertexMap.fold add_require partition'.inputs Map.empty in
  ( { solve with
      init = init'
    ; trans = trans'
    ; merge = merge'
    ; (* should this be erased, or kept as reference? *)
      interface = None
    }
  , assertions
  , reqs )
;;
