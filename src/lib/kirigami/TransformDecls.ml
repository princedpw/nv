open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax
open Nv_interpreter
open SrpRemapping

let remap_value parted_srp v =
  let { node_map; edge_map; _ } = parted_srp in
  let make_node n = avalue (vnode n, Some TNode, v.vspan) in
  let make_edge e = avalue (vedge e, Some TEdge, v.vspan) in
  match v.v with
  | VNode n ->
    let new_node = VertexMap.find_default None n node_map in
    Option.map make_node new_node
  | VEdge e ->
    let new_edge = EdgeMap.find_default None e edge_map in
    Option.map make_edge new_edge
  | _ -> Some v
;;

let rec remap_exp parted_srp e =
  let f = remap_exp parted_srp in
  wrap
    e
    (match e.e with
    | EMatch (e1, bs) -> ematch (f e1) (remap_branches parted_srp bs)
    | EVal v ->
      (match remap_value parted_srp v with
      | Some v1 -> e_val v1
      | None ->
        failwith
          ("remap_value given " ^ Printing.value_to_string v ^ ", which should be cut"))
    | EOp (op, es) -> remap_exp_op parted_srp op es
    | ESome e -> esome (f e)
    | ETuple es -> etuple (List.map f es)
    | EProject (e, l) -> eproject (f e) l
    | EFun fn -> efun { fn with body = f fn.body }
    | EApp (e1, e2) -> eapp (f e1) (f e2)
    | ELet (x, e1, e2) -> elet x (f e1) (f e2)
    | EIf (test, e1, e2) -> eif (f test) (f e1) (f e2)
    | ERecord _ -> failwith "remap_exp: records should be unrolled"
    | ETy (e, t) -> ety (f e) t
    | EVar _ -> e)

and remap_branches parted_srp bs =
  let { node_map; _ } = parted_srp in
  let f = remap_exp parted_srp in
  let update_branches old_bs =
    foldBranches
      (fun (p, e) bs ->
        match p with
        | PTuple [PNode n1; PNode n2] ->
          let n1' = VertexMap.find_default None n1 node_map in
          let n2' = VertexMap.find_default None n2 node_map in
          (match n1', n2' with
          | Some u, Some v -> (PTuple [PNode u; PNode v], f e) :: bs
          | _ -> bs)
        | PNode u ->
          (match VertexMap.find_default None u node_map with
          | Some u' -> (PNode u', f e) :: bs
          | None -> bs)
        | PEdge _ -> failwith "edges should be unboxed before partitioning"
        | _ -> (p, f e) :: bs)
      []
      old_bs
  in
  let pat_exps = update_branches bs in
  (* put the branches back in the same order by going from the back *)
  List.fold_right (fun (p, e) b -> addBranch p e b) (List.rev pat_exps) emptyBranch

and remap_exp_op parted_srp op es =
  let f = remap_exp parted_srp in
  let ty = (List.hd es).ety |> Option.get in
  (* check if the operation is over nodes *)
  (* if so, if any nodes are cut, the op simplifies to false *)
  match ty with
  | TNode ->
    (match op with
    | Eq | NLess | NLeq ->
      (* NOTE: won't be able to fix expressions where both sides are non-values *)
      let remap_node_exp n =
        if is_value n
        then Option.map e_val (remap_value parted_srp (to_value n))
        else Some (f n)
      in
      let es1 = List.map remap_node_exp es in
      if List.exists Option.is_none es1
      then ebool false
      else eop op (List.map Option.get es1)
    | _ -> failwith (Printf.sprintf "unexpected operator %s over nodes" (show_op op)))
  | TEdge -> failwith "not implemented; edges should already be unboxed"
  | _ -> eop op (List.map f es)
;;

let remap_solve parted_srp solve =
  let init = remap_exp parted_srp solve.init in
  let trans = remap_exp parted_srp solve.trans in
  let merge = remap_exp parted_srp solve.merge in
  { solve with init; trans; merge }
;;

(** Remap an and expression by dropping conjuncts that refer to cut nodes.
 ** The and statement is nested as follows:
 ** And (And (And x0 x1) x2) x3
 ** so we need to recurse in until we have dropped the right number of nodes.
 **)
let rec remap_conjuncts nodes e =
  if nodes > 0
  then (
    match e.e with
    | EOp (And, [e2; _]) ->
      (* go deeper *)
      remap_conjuncts (nodes - 1) e2
    | EOp (And, _) -> failwith "and has wrong number of arguments"
    (* this case should be the last one *)
    | _ -> e)
  else e
;;

(** Assume the assert is of the form:
 ** assert foldNodes (fun u v acc -> assertNode u v && acc) sol true
 ** which simplifies after map unrolling to:
 ** assert (match (sol-proj-0, sol-proj-1, ..., sol-proj-n) with
 **  | UnrollingFoldVar-0, UnrollingFoldVar-1, ..., UnrollingFoldVar-n -> true &&
 **    (assertNode 0n UnrollingFoldVar-0) && (assertNode 1n UnrollingFoldVar-1)
 **    && ... && (assertNode n UnrollingFoldVar-n)
 ** After tuple flattening, the fold variables may be further subdivided, where
 ** for a k-tuple attribute, we have n*k variables:
 ** the 0..k projected variables will belong to node 0,
 ** the k..2k variables belong to node 1, and so on.
 **)
let transform_assert (e : exp) (parted_srp : SrpRemapping.partitioned_srp) : exp =
  let { nodes; _ } = parted_srp in
  let e =
    match e.e with
    | EMatch _ ->
      (* if there is only one branch, use interp to simplify;
       * we should be left with an EOp statement which we can prune *)
      let e1 = InterpPartialFull.interp_partial e in
      (match e1.e with
      (* we want to supply the *difference* between the current nodes and the
       * number of nodes in the original SRP, because we want to descend down
       * the chain of ands until there are only *nodes* many conjuncts left *)
      | EOp (And, _) -> remap_conjuncts (get_global_nodes parted_srp - nodes) e1
      | _ ->
        print_endline ("not an and: " ^ Printing.exp_to_string e1);
        e)
    | _ -> e
  in
  remap_exp parted_srp e
;;

(** Helper function to extract the edge predicate
 *  from the interface expression.
*)
let interp_interface edge intfe =
  let u, v = edge in
  let node_value n = avalue (vnode n, Some Typing.node_ty, Span.default) in
  let edge = [node_value u; node_value v] in
  let intf_app = InterpPartial.interp_partial_fun intfe edge in
  match intf_app.e with
  | EFun _ -> intf_app
  | EVal { v = VClosure _; _ } -> intf_app
  | _ ->
    failwith
      ("expected intf value to be a function but got " ^ Printing.exp_to_string intf_app)
;;

let update_preds interface partitioned_srp =
  let intf edge preds =
    let p = interp_interface edge interface in
    p :: preds
  in
  SrpRemapping.map_predicates intf partitioned_srp
;;

(* Transform the given solve and return it along with a new expression to assert
 * and new expressions to require. *)
let transform_solve solve (partition : partitioned_srp) : partitioned_srp * solve =
  let partition' =
    let p1 =
      match solve.interface with
      | Some interface -> update_preds interface partition
      | None -> partition
    in
    p1
  in
  let solve' = remap_solve partition' solve in
  let solve' = Measure.measure_solve solve' in
  (* erase interface information now that it's in the partition *)
  partition', { solve' with interface = None }
;;
