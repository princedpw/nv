open Graph
open AbstractionMap
open Unsigned
open Console
open Srp
open Hashtbl
open Syntax
open BatSet

let debugAbstraction = ref true
                     
(** Sets of Abstract Nodes *)
type abstractNodeSet = AbstractNode.t BatSet.t

(** Sets of Abstract Node Ids *)
type absIdSet = abstrId BatSet.t

(** transfer hash, abstract id *)
type transAbsId = int * abstrId

(** merge_hash * {(trans_hash, abstractId)}*) 
type policyAbsId = int * (transAbsId BatSet.t)
                                                               

(** ** Topological only abstraction *)
(* This does not handle a forall-forall abstraction. *)  
let refineTopological (f: abstractionMap) (g: Graph.t)
                      (us: AbstractNode.t) : abstractionMap =
  let refineOne (u : Vertex.t) (umap : (Vertex.t, absIdSet) BatMap.t) =
    List.fold_left (fun acc v ->
        let vhat = getId f v in
        BatMap.modify_opt u (fun omapu ->
                           match omapu with
                           | None -> Some (BatSet.singleton vhat)
                           | Some vs -> Some (BatSet.add vhat vs)) acc) umap
                   (neighbors g u)
  in
  let vmap = BatSet.fold (fun u acc -> refineOne u acc) us BatMap.empty in
  BatSet.fold (fun us f' -> AbstractionMap.split f' us) (Collections.groupKeysByValue vmap) f

let rec abstractionTopological (f: abstractionMap) (g: Graph.t) : abstractionMap =
  let f' = AbstractionMap.fold (fun _ us facc ->
               if (BatSet.cardinal us > 1) then
                 refineTopological facc g us 
               else
                 facc) f f in
  if (size f = size f') then normalize f' 
  else abstractionTopological f' g

(** * Proper policy+topology abstraction *)  
 
let refineAbstraction (f: abstractionMap) (g: Graph.t)
                      (transMap: (Edge.t, int * Syntax.exp) Hashtbl.t)
                      (mergeMap: (Vertex.t, int * Syntax.exp) Hashtbl.t)
                      (us: AbstractNode.t) : abstractionMap =
  let refineOne (u : Vertex.t) (umap : (Vertex.t, policyAbsId) BatMap.t) =
    List.fold_left (fun acc v ->
        let vhat = getId f v in
        let (trans_pol, _) = Hashtbl.find transMap (u,v) in
        BatMap.modify_opt u (fun omapu ->
            match omapu with
            | None ->
               let (merge_pol, _) = Hashtbl.find mergeMap u in
               Some (merge_pol, BatSet.singleton (trans_pol, vhat))
            | Some (mp, vs) ->
               Some (mp, BatSet.add (trans_pol, vhat) vs))
                         acc) umap (neighbors g u)
  in
  (* for each node u in us, find the (abstract) nodes it's connected to and their policy *)
  let vmap = BatSet.fold (fun u acc -> refineOne u acc) us BatMap.empty in
  BatSet.fold (fun us f' -> AbstractionMap.split f' us) (Collections.groupKeysByValue vmap) f

let rec abstraction (f: abstractionMap) (g: Graph.t)
                    (transMap: (Edge.t, int * Syntax.exp) Hashtbl.t)
                    (mergeMap: (Vertex.t, int * Syntax.exp) Hashtbl.t) : abstractionMap =
  let f' = AbstractionMap.fold (fun _ us facc ->
               if (BatSet.cardinal us > 1) then
                 refineAbstraction facc g transMap mergeMap us 
               else
                 facc) f f in
  if (size f = size f') then normalize f' 
  else abstraction f' g transMap mergeMap

let partialEvalTrans (graph : Graph.t)
                     (trans : Syntax.exp) : (Edge.t, int * Syntax.exp) Hashtbl.t  =
  let edge_to_val e = vtuple [vint (fst e); vint (snd e)] in
  let es = Graph.edges graph in
  let tbl = Hashtbl.create (List.length es) in
  List.iter (fun e ->
      (* Printf.printf "%s\n" *)
      (*               (Syntax.show_exp ~show_meta:false *)
      (*                                   (exp_of_value (vclosure (network.trans)))); *)
      let ptrans = Interp.interp_partial_fun trans [edge_to_val e] in
      Printf.printf "edge (%d,%d): %s\n" (UInt32.to_int (fst e)) (UInt32.to_int (snd e))
      (Syntax.show_exp ~show_meta:false ptrans);
      Hashtbl.add tbl e ((Syntax.hash_exp ~hash_meta:false ptrans), ptrans)) es;
  tbl

let partialEvalMerge (graph : Graph.t)
                     (merge : Syntax.exp) : (Vertex.t, int * Syntax.exp) Hashtbl.t =
  let node_to_val n = vint n in
  let ns = Graph.get_vertices graph in
  let tbl = Hashtbl.create (BatSet.cardinal ns) in
  BatSet.iter (fun v ->
      let pmerge = Interp.interp_partial_fun merge [node_to_val v] in
      Hashtbl.add tbl v (Syntax.hash_exp ~hash_meta:false pmerge, pmerge)) ns;
  tbl

(* Given a concrete graph g, an abstraction function f and an abstract
   node id returns its abstract edges *)
let findAbstractEdges (g: Graph.t) (f: abstractionMap) (uhat: abstrId) : Edge.t list =
  let repru = getGroupRepresentativeId f uhat in
  let ns = neighbors g repru in
  List.map (fun v -> uhat, getId f v) ns

(* Deprecated right now *)
let addAbstractEdges (g: Graph.t) (f: abstractionMap) (ag: Graph.t)
                     (uhat: abstrId) : Graph.t =
  add_edges ag (findAbstractEdges g f uhat)

(* Requires that abstract group ids are contiguous. Deprecated. *)
let buildAbstractGraph (g: Graph.t) (f: abstractionMap) : Graph.t =
  let ag = Graph.create (UInt32.of_int (size f)) in
  BatSet.fold (fun uhat acc -> addAbstractEdges g f acc uhat) (Graph.get_vertices ag) ag   

(* Given a concrete graph and an abstraction function returns the node
   and edges of the abstract graph *)
let buildAbstractGraphDecls (g: Graph.t) (f: abstractionMap) : UInt32.t * (Edge.t list) =
  let n = UInt32.of_int (size f) in
  let rec edges uhat =
    if uhat = n then []
    else (findAbstractEdges g f uhat) @ edges (UInt32.add uhat UInt32.one)
  in
  (n, edges UInt32.zero)

(* Helper function that constructs an MGet expression *)
let mget (m : exp) (i : exp) : exp =
  eop MGet [m; i]
  
let buildSymbolicFailures (edges : Edge.t list) (k : int) (failuresVar : Var.t) =
  (* symbolic map of failures *)
  let failuresMap = e_val (vmap (BddMap.create ~key_ty:tint (vbool false))) in
  let bool2int_exp arg = eif arg (e_val (vint UInt32.one)) (e_val (vint UInt32.zero)) in
  let failuresSum = List.fold_left (fun acc (uhat, vhat) ->
                     eop UAdd [(bool2int_exp (mget (evar failuresVar)
                                         (e_val (vtuple [vint uhat; vint vhat])))); acc])
                                (e_val (vint UInt32.zero)) edges in
  let failures_leq_k = eop ULeq [failuresSum; e_val (vint (UInt32.of_int k))] in
  [DRequire failures_leq_k; DSymbolic (failuresVar, Exp failuresMap)]


let deconstructFun exp =
  match exp.e with
  | EFun f ->
     (f.arg, f.body)
  | _ -> failwith "expected a function"
  
(* Given the abstract edges and a concrete transfer function, 
   synthesizes an abstract transfer function. *)
let buildAbstractTrans (aedges : Edge.t list)
                       (trans: (Edge.t, int * Syntax.exp) Hashtbl.t)
                       (failuresVar : Var.t)
                       (f: abstractionMap) : Syntax.exp =
  (* edge argument used by abstract transfer function *)
  let aedge_var = Var.create "edge" in
 
  (* code that implements check for failed edge *)
  let failCheck exp = eif (mget (evar failuresVar) (evar aedge_var))
                          (exp_of_value (voption None))
                          exp in
  
  (* inserting that code in the body of the transfer function *)
  let addFailureCheck exp = deconstructFun exp |> snd |> failCheck in
    
  (* for each abstract edge, find it's corresponding concrete
     transfer function and augment it with a check for whether it's
     failed *)
  let branches =
    List.fold_left (fun acc (uhat, vhat) ->
        let p = PTuple [PUInt32 uhat; PUInt32 vhat] in
        let (u,v) = (getGroupRepresentativeId f uhat, getGroupRepresentativeId f vhat) in
        let (_, transuv) = Hashtbl.find trans (u,v) in
        (p, addFailureCheck transuv) :: acc) [] aedges
  in
  (* partial evaluted trans functions are of the form fun m -> ..., grab m *)
  let messageArg = match aedges with
    | [] -> failwith "No edges found"
    | (uhat, vhat) :: _ ->
       let uv = (getGroupRepresentativeId f uhat, getGroupRepresentativeId f vhat) in
       let (_, transuv) = Hashtbl.find trans uv in
       match transuv.e with
       | EFun f ->
          f.arg
       | _ -> failwith "expected a function"
  in
  let match_exp = ematch (evar aedge_var) branches in
  (* create fun m -> trans_hat_body *)
  let trans_hat_msg = Syntax.lam messageArg match_exp in
  (*return fun e_hat m -> trans_hat_body *)  
  Syntax.lam aedge_var trans_hat_msg

(* Given the number of abstract nodes and a concrete merge function, 
   synthesizes an abstract merge function. *)
let buildAbstractMerge (n : UInt32.t)
                       (merge: (Vertex.t, int * Syntax.exp) Hashtbl.t)
                       (f: abstractionMap) : Syntax.exp =
  (* vertex argument used by abstract merge function *)
  let avertex_var = Var.create "node" in

  (* get attribute arguments *)
  let xvar, yvar =
    let _, merge0 = Hashtbl.find merge UInt32.zero in
    (fst (deconstructFun merge0), fst (deconstructFun (snd (deconstructFun merge0)))) in
  (* for each abstract node, find it's corresponding concrete
      merge function. *)
  let rec branches uhat =
    if uhat = n then []
    else
      let p = PUInt32 uhat in
      let u = getGroupRepresentativeId f uhat in
      let (_, mergeu) = Hashtbl.find merge u in
      let mergeubody = mergeu |> deconstructFun |> snd |> deconstructFun |> snd in
      (p, mergeubody) :: (branches (UInt32.add uhat UInt32.one))
  in
  (* create a match on the node expression *)
  let match_exp = ematch (evar avertex_var) (branches UInt32.zero) in
  (* create a function from attributes *)
  let merge_fun_msg = Syntax.lam xvar (Syntax.lam yvar match_exp) in
  (*return fun uhat x y -> merge_hat_body *)  
  Syntax.lam avertex_var merge_fun_msg

(* Constructs the init function for the abstract network. Nodes in the
   set dst have the invariant that they announce the same prefixes *)
let buildAbstractInit (dst: Vertex.t BatSet.t)
                      (initMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                      (attrTy : Syntax.ty)
                      (f: abstractionMap) : Syntax.exp =
  (* vertex argument used by abstract init function *)
  let avertex_var = Var.create "node" in

  (* Grab one of the destination nodes *)
  let (d, dst') = BatSet.pop_min dst in
  (* Grab its initial value *)
  let vinit = (Hashtbl.find initMap d) in
  let b = (PUInt32 (getId f d), vinit) in
  (* This is the default initial value for all other nodes.
     Assuming default_value computes the value we want..*)
  let default_attr = e_val (default_value attrTy) in
  let default_branch = (PWild, default_attr) in
  (* compute the branches of the initial expression *)
  let branches = BatSet.fold (fun u acc ->
                     let uhat = getId f u in
                     let p = PUInt32 uhat in
                     (p, vinit) :: acc) dst' ([b; default_branch]) in
  (*build the match expression *)
  let match_exp = ematch (evar avertex_var) branches in
  (*return the function "init node = ..." *)
  Syntax.lam avertex_var match_exp

(* Constructs the assertion function for the abstract network.*)
(* TODO: we also need to slice the assertion function to only refer to
   prefixes of the current SRP *)
(* Invariant: This assumes that nodes in the same abstract group have
   the same assertion. *)
let buildAbstractAssert (assertionMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                        (f: abstractionMap) : Syntax.exp =
  (* vertex argument used by abstract init function *)
  let avertex_var = Var.create "node" in
  
  (* get abstract nodes *)
  let n = UInt32.of_int (AbstractionMap.size f) in

  (* get the argument name of the attribute *)
  let mineu = Hashtbl.find assertionMap UInt32.zero in 
  let messageArg, _ = deconstructFun mineu in
  
  (* for each abstract node, find it's corresponding concrete
      assertion function. *)
  let rec branches uhat =
    if uhat = n then []
    else
      let p = PUInt32 uhat in
      let u = getGroupRepresentativeId f uhat in
      let assertu = Hashtbl.find assertionMap u in
      (p, assertu) :: (branches (UInt32.add uhat UInt32.one))
  in
  
  (* create a match on the node expression *)
  let match_exp = ematch (evar avertex_var) (branches UInt32.zero) in
  let assert_msg = Syntax.lam messageArg match_exp in
  
  (*return fun uhat m -> assert_hat_body *)  
  Syntax.lam avertex_var assert_msg
  
(* Given an abstraction function, a concrete graph, transfer and merge
   function, and the number of maximum link failures builds an
   abstract network *)
let buildAbstractNetwork (f: abstractionMap) (graph: Graph.t)
                         (mergeMap: (Vertex.t, int * Syntax.exp) Hashtbl.t)
                         (transMap: (Edge.t, int * Syntax.exp) Hashtbl.t)
                         (initMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                         (assertMap: (Vertex.t, Syntax.exp) Hashtbl.t)
                         (dst : Vertex.t BatSet.t)
                         (attrTy: Syntax.ty)
                         (k: int) : declarations =
  (* build the abstract graph based on the abstraction function *)
  let (n, edgeshat) = buildAbstractGraphDecls graph f in
  (* create a variable to point to a failures map *)
  let failuresVar = Var.create "fail" in
  (* build the abstract merge function *)
  let mergehat = buildAbstractMerge n mergeMap f in
  (* build the abstract transfer function *)
  let transhat = buildAbstractTrans edgeshat transMap failuresVar f in
  (* build the abstract init function *)
  let inithat = buildAbstractInit dst initMap attrTy f in
  (* build the abstract assert function *)
  let asserthat = buildAbstractAssert assertMap f in
  (* build the symbolic representation of failures *) 
  let symbolics = buildSymbolicFailures edgeshat k failuresVar in
  (DNodes n) :: (DEdges edgeshat) :: (DMerge mergehat)
  :: (DTrans transhat) :: (DInit inithat) :: (DAssert asserthat) :: symbolics
  
(* Given a concrete graph, transfer, merge functions a destinations
   computes an abstract network *)
let findAbstraction (graph: Graph.t)
                    (transMap : (Edge.t, int * Syntax.exp) Hashtbl.t)
                    (mergeMap : (Vertex.t, int * Syntax.exp) Hashtbl.t)
                    (ds: Vertex.t BatSet.t) : abstractionMap =
  (* Separate destination nodes from the rest *)
  let f =
    BatSet.fold (fun d facc -> AbstractionMap.split facc (BatSet.singleton d))
                ds (createAbstractionMap graph) in
  
  (* compute the abstraction function *)
  let f = abstraction f graph transMap mergeMap in
  f
  
let abstractToConcreteEdge (g: Graph.t) (f: abstractionMap) (ehat: Edge.t) : EdgeSet.t =
  let (uhat, vhat) = ehat in
  let us = getGroupById f uhat in (* get nodes represented by uhat *)
  let getNeighborsInVhat u =
    BatList.filter_map (fun v ->
        if (getId f v = vhat) then Some (u,v) else None) (neighbors g u)
    |> EdgeSet.of_list
  in
  BatSet.fold
    (fun u acc -> EdgeSet.union (getNeighborsInVhat u) acc) us EdgeSet.empty
  
let getEdgeMultiplicity (g: Graph.t) (f: abstractionMap) (ehat: Edge.t) : int =
  EdgeSet.cardinal (abstractToConcreteEdge g f ehat)
  
(* For failures we don't really need to care about the policies when
   computing a new abstraction as those have already been factored in
   and we are only splitting things. We just have to ensure a
   topological abstraction (forall-exists). *)
module FailuresAbstraction =
  struct
    type splittings = Mesh | Groups of abstractNodeSet

    (* For each abstract node [uhat] and [vhat], partitions the concrete
       nodes in uhat into subsets s.t. that nodes in the same subset have
       edges to the same concrete nodes in [vhat] *)                              
    let splitForFailures (uhat : AbstractNode.t) (vhat : AbstractNode.t)
                         (g: Graph.t) : splittings = 
      let addNeighbor u =
        let neighborsOfu = neighbors g u in
        let neighborsOfUinV = List.filter (fun v -> BatSet.mem v vhat) neighborsOfu in
        BatSet.of_list neighborsOfUinV
      in
      let connectivityMap = BatSet.fold (fun u acc ->
                                BatMap.add u (addNeighbor u) acc) uhat BatMap.empty in
      let us = Collections.groupKeysByValue connectivityMap in
      if ((BatSet.cardinal us) = 1) then
        Mesh
      else
        Groups us

    (* using the abstract group id on path for efficiency reasons *)
    (* - assumes uid can be split
       - returns a random split with maximum ratio if the path was empty
       - returns a random split with ratio 1.0 if you immediately get to a full mesh.
       TODO: no need to return a ratio of 1.0, do max_int. Also avoid enforcing invariants
       with the ratio *)
    let bestSplitForFailures (g : Graph.t) (f: abstractionMap)
                             (uid: abstrId) (path: abstrId list) =
      let rec loop path current best =
        match path with
        | [] -> best
        | vid :: path ->
           let curGroup = getGroupById f current in
           match splitForFailures curGroup (getGroupById f vid) g with
           | Groups us when BatSet.cardinal us = 2 ->
              (us, 0.0)
           | Groups us ->
              let szNew = BatSet.cardinal us in
              let szCur = BatSet.cardinal curGroup in
              let ratio = (float_of_int szNew) /. (float_of_int szCur) in
              (* heuristic *)
              if (ratio < snd best) then
                loop path vid (us, ratio)
              else
                loop path vid best
           | Mesh ->
              (* do a randomSplit if necessary, but maybe there are better options*)
              if (snd best) > 1.0 then
                let u1, u2 = AbstractNode.randomSplit curGroup in
                (BatSet.of_list [u1;u2], 1.0)
              else
                best
      in
      let u1, u2 = AbstractNode.randomSplit (getGroupById f uid) in
      loop path uid (BatSet.of_list [u1;u2], float_of_int max_int)

    let splitSet_debug us =
      if !debugAbstraction then
        show_message (AbstractNode.printAbstractNode us) T.Blue "splitting set"
      
    (* Repeatedly split to create the abstract nodes in [uss] *)
    let splitSet f (uss : abstractNodeSet) : abstractionMap =
      BatSet.fold
        (fun us f' -> splitSet_debug us; AbstractionMap.split f' us) uss f

    let refineForFailures_debug (f: abstractionMap) =
      if !debugAbstraction then
        show_message (printAbstractGroups f "\n") T.Blue
                     "Abstract groups after refine for failures "
      
    let refineForFailures (g: Graph.t) (f: abstractionMap)
                          (uid: abstrId) (path: abstrId list) : abstractionMap =
      let (uss, _) = bestSplitForFailures g f uid path in
      let f' = splitSet f uss in
      let f'' =  abstractionTopological f' g in
      refineForFailures_debug f'';
      f''      
  end

  (* 1. find the abstraction.
     2. build abstract network.
     3. check assertions.
     3a. if they succeed, we are done.
     3b. if not, decide whether it's game over or we can refine. *)
(* let abstractionLoop (graph: Graph.t) (trans : Syntax.exp) *)
(*                     (merge : Syntax.exp) (init : Syntax.exp) *)
(*                     (assertion : Syntax.exp) (ds: VertexSet.t) (k : int) = *)
(*   let f = findAbstraction graph trans merge init assertion ds in *)
(*   let transMap = partialEvalTrans graph trans in *)
(*   let mergeMap = partialEvalMerge graph merge in *)
  
    
