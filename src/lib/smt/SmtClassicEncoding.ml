open Nv_datastructures
open Nv_lang
open Syntax
open Collections
open SmtUtils
open SmtLang
open Nv_interpreter
open Nv_utils.OCamlUtils
open Nv_kirigami
open Batteries
open SrpRemapping
open AdjGraph

module type ClassicEncodingSig =
  SmtEncodingSigs.Encoding with type network_type = Syntax.declarations

module ClassicEncoding (E : SmtEncodingSigs.ExprEncoding) : ClassicEncodingSig = struct
  open E

  type network_type = Syntax.declarations

  let add_symbolic_constraints env requires sym_vars =
    (* Declare the symbolic variables: ignore the expression in case of SMT *)
    VarMap.iter
      (fun v e ->
        let names = create_vars env "" v in
        let sort = SmtUtils.ty_to_sort (Syntax.get_ty_from_tyexp e) in
        let symb = mk_constant env names sort ~cdescr:"Symbolic variable decl" in
        (* integers are set to be non-negative *)
        match sort with
        | IntSort -> SmtUtils.add_constraint env (mk_term (mk_leq (mk_int 0) symb.t))
        | _ -> ())
      sym_vars;
    (* add the require clauses *)
    BatList.iter
      (fun e ->
        (* print_endline ("Encoding symbolic exp: " ^ Printing.exp_to_string e); *)
        let es = encode_exp_z3 "" env e in
        ignore (lift1 (fun e -> SmtUtils.add_constraint env e) es))
      requires
  ;;

  let encode_z3_merge str env merge =
    let rec loop merge acc =
      match merge.e with
      | EFun { arg = x; argty = Some xty; body = exp; _ } ->
        (match exp.e with
        | EFun _ -> loop exp ((x, xty) :: acc)
        | _ ->
          let xstr =
            BatList.rev_map
              (fun (x, xty) ->
                mk_constant
                  env
                  (create_vars env str x)
                  (SmtUtils.ty_to_sort xty)
                  ~cdescr:""
                  ~cloc:merge.espan)
              ((x, xty) :: acc)
          in
          let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
          let results = lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
          let es = encode_exp_z3 str env exp in
          ignore
            (lift2
               (fun e result ->
                 SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
               es
               results);
          results, xstr)
      | _ -> failwith "internal error"
    in
    loop merge []
  ;;

  let rec encode_z3_trans_aux trans acc =
    match trans.e with
    | EFun { arg = x; argty = Some xty; body = exp; _ } ->
      (match exp.e with
      | EFun _ -> encode_z3_trans_aux exp ((x, xty) :: acc)
      | _ ->
        ( BatList.rev_map (fun (x, xty) -> x, SmtUtils.ty_to_sort xty) ((x, xty) :: acc)
        , exp ))
    | _ -> failwith "internal error"
  ;;

  let encode_z3_trans trans =
    (* get edge argument*)
    let ex1, ex2, ex1ty, ex2ty, trans =
      match trans.e with
      | EFun { arg = ex1; argty = Some ex1ty; body = exp; _ } ->
        (match exp.e with
        | EFun { arg = ex2; argty = Some ex2ty; body = exp; _ } ->
          ex1, ex2, ex1ty, ex2ty, exp
        | _ -> failwith "Expected a function")
      | _ -> failwith "Expected a function"
    in
    let xs, exp = encode_z3_trans_aux trans [] in
    let expty = oget exp.ety in
    let expsorts = ty_to_sorts expty in
    (* construct new transfer function as a partial function of the edge*)
    let exp =
      aexp
        ( efun (funcFull ex2 (Some ex2ty) (Some ex2ty) exp)
        , Some (TArrow (ex2ty, expty))
        , exp.espan )
    in
    let exp =
      aexp
        ( efun (funcFull ex1 (Some ex1ty) (Some ex1ty) exp)
        , Some (TArrow (ex1ty, expty))
        , exp.espan )
    in
    fun edge str env ->
      let exp = InterpPartial.interp_partial_fun exp edge in
      (* Printf.printf "%s\n" (Printing.exp_to_string exp);
       * failwith "bla"; *)
      let xstr =
        BatList.map
          (fun (x, xsort) ->
            mk_constant
              env
              (create_vars env str x)
              xsort
              ~cdescr:"transfer x argument"
              ~cloc:trans.espan)
          xs
      in
      let names = create_strings (Printf.sprintf "%s-result" str) expty in
      let results = lift2 (mk_constant env) names expsorts in
      let es = encode_exp_z3 str env exp in
      ignore
        (lift2
           (fun e result -> SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
           es
           results);
      results, xstr
  ;;

  let encode_z3_init str env e =
    (* Printf.printf "%s\n" (Printing.exp_to_string e); *)
    (* Printf.printf "%s\n" (Syntax.show_exp ~show_meta:false e); *)
    let names = create_strings (Printf.sprintf "%s-result" str) (oget e.ety) in
    let results = lift2 (mk_constant env) names (oget e.ety |> ty_to_sorts) in
    let es = encode_exp_z3 str env e in
    ignore
      (lift2
         (fun e result -> SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
         es
         results);
    results
  ;;

  (* Currently unused, but might be if we split up assertions *)
  let encode_z3_assert str env _node assertion =
    let rec loop assertion acc =
      match assertion.e with
      | EFun { arg = x; argty = Some xty; body = exp; _ } ->
        (match exp.e with
        | EFun _ -> loop exp ((x, xty) :: acc)
        | _ ->
          let xstr =
            BatList.rev_map
              (fun (x, xty) ->
                mk_constant
                  env
                  (create_vars env str x)
                  (SmtUtils.ty_to_sort xty)
                  ~cdescr:"assert x argument"
                  ~cloc:assertion.espan)
              ((x, xty) :: acc)
          in
          let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
          let results = lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
          let es = encode_exp_z3 str env exp in
          ignore
            (lift2
               (fun e result ->
                 SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
               es
               results);
          results, xstr)
      | _ -> failwith "internal error"
    in
    loop assertion []
  ;;

  (* get the arguments and internal expression for a given hypothesis predicate *)
  let rec encode_predicate_aux hyp acc =
    match hyp.e with
    | EFun { arg = x; argty = Some xty; body = exp; _ } ->
      (match exp.e with
      | EFun _ -> encode_predicate_aux exp ((x, xty) :: acc)
      | _ ->
        ( BatList.rev_map (fun (x, xty) -> x, SmtUtils.ty_to_sort xty) ((x, xty) :: acc)
        , exp ))
    | _ -> failwith "internal error"
  ;;

  let encode_predicate pred =
    let xs, exp = encode_predicate_aux pred [] in
    let expty = oget exp.ety in
    let expsorts = ty_to_sorts expty in
    fun str env args ->
      let xstr =
        BatList.map
          (fun (x, xsort) ->
            mk_constant
              env
              (create_vars env str x)
              xsort
              ~cdescr:"predicate x argument"
              ~cloc:pred.espan)
          xs
      in
      let names = create_strings (Printf.sprintf "%s-result" str) expty in
      let results = lift2 (mk_constant env) names expsorts in
      let es = encode_exp_z3 str env exp in
      (* print_endline (SmtLang.term_to_smt () () (List.hd (to_list es))); *)
      (* sanity check that assertions evaluate to bools *)
      assert (List.length (to_list es) = 1);
      ignore
        (lift2
           (fun e result -> SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
           es
           results);
      BatList.iter2
        (fun y x -> SmtUtils.add_constraint env (mk_term (mk_eq y.t x.t)))
        xstr
        (to_list args);
      results
  ;;

  (* Encode the transfer of the given variable across the input/output
   * decomposed transfer function. *)
  let encode_kirigami_decomp str env optrans edge var =
    match optrans with
    | Some exp ->
      let i, j = edge in
      let node_value n = avalue (vnode n, Some TNode, Span.default) in
      let edge = [node_value i; node_value j] in
      let trans, tx = encode_z3_trans exp edge (Printf.sprintf "trans-%s" str) env in
      BatList.iter2
        (fun y x -> SmtUtils.add_constraint env (mk_term (mk_eq y.t x.t)))
        tx
        (to_list var);
      trans
    | None -> var
  ;;

  let find_input_symbolics env (hyp_var : Var.t) =
    let prefix = "symbolic-" ^ Var.name hyp_var in
    (* add an extra little character after to avoid matching
     * "hyp_0~10" when looking for "hyp_0~1" *)
    (* TODO: use a more robust approach like a regular expression *)
    let matches_format name =
      String.starts_with name (prefix ^ "~") || String.starts_with name (prefix ^ "-")
    in
    let names =
      ConstantSet.fold
        (fun { cname; _ } l ->
          if matches_format cname
          then mk_term (mk_var cname) :: l
          else l (* (print_endline cname; l) *))
        env.const_decls
        []
    in
    (* sanity check: *)
    if List.length names = 0
    then failwith "couldn't find the corresponding constant for hyp in smt_env"
    else ();
    (* order of names is reversed by fold, so flip them around *)
    of_list (List.rev names)
  ;;

  type 'a hyp_order =
    | Lesser of 'a
    | Greater of 'a

  (* map from base nodes to a list of inputs,
   * where each input is a 2-tuple of
   * 1. transfer encoding
   * 2. predicate encoding
   *)
  let encode_kirigami_inputs env r inputs eintrans count =
    let encode_input { edge; rank; var; preds } =
      let u, v = edge in
      let xs = find_input_symbolics env var in
      (* get the relevant predicate *)
      let pred_to_hyp i p =
        let pred =
          encode_predicate p (Printf.sprintf "input-pred%d-%d-%d-%d" count i u v) env
        in
        pred, xs
      in
      let hyps = List.mapi pred_to_hyp preds in
      ( encode_kirigami_decomp
          (Printf.sprintf "input%d-%d-%d" count u v)
          env
          eintrans
          edge
          xs
      , if rank < r then Lesser hyps else Greater hyps )
    in
    VertexMap.map (fun inputs -> List.map encode_input inputs) inputs
  ;;

  (* Return a list of output SMT terms to assert. *)
  let encode_kirigami_outputs env outputs eouttrans labelling count =
    let encode_output vtx (edge, preds) =
      let u, v = edge in
      let pred_to_guar i p =
        let trans =
          encode_kirigami_decomp
            (Printf.sprintf "output%d-%d-%d" count u v)
            env
            eouttrans
            edge
            labelling.(vtx)
        in
        let pred =
          encode_predicate p (Printf.sprintf "output-pred%d-%d-%d-%d" count i u v) env
        in
        pred, trans
      in
      List.mapi pred_to_guar preds
    in
    VertexMap.fold
      (fun v outputs l -> List.flatten (List.map (encode_output v) outputs) @ l)
      outputs
      []
  ;;

  (* Extract variable names from var_names, and split them up based on which node they
   *  belong to. In the end, label_vars.(i) is the list of attribute variables
   *  for node i.
   * NOTE: as we don't modify var_names as part of Kirigami,
   * label_vars has a length proportional to the number of nodes in the original network,
   * but not the number of nodes in the Kirigami networks. *)
  let encode_label_vars aty var_names : var E.t array =
    let aty_len =
      match aty with
      | TTuple tys -> List.length tys
      | _ -> 1
    in
    match var_names.e with
    | ETuple es ->
      let varnames =
        List.map
          (fun e ->
            match e.e with
            | EVar x -> x
            | _ -> failwith "")
          es
      in
      varnames |> List.ntake aty_len |> Array.of_list |> Array.map of_list
    | EVar x ->
      (* Not sure if this can happen, but if it does it's in networks with only one node *)
      Array.map of_list @@ Array.make 1 [x]
    | _ -> failwith "internal error (encode_algebra)"
  ;;

  (* Map each edge to transfer function result *)
  let encode_edge_transfers env count mapping nodes etrans graph =
    (* incoming_map is a map from vertices to list of incoming edges *)
    let incoming_map = Array.make nodes [] in
    (* trans_map maps each edge to the variable that holds the result *)
    let trans_map = ref EdgeMap.empty in
    (* trans_input_map maps each edge to the incoming message variable *)
    let trans_input_map = ref EdgeMap.empty in
    let enc_z3_trans = encode_z3_trans etrans in
    iter_edges_e
      (fun (i, j) ->
        incoming_map.(j) <- (i, j) :: incoming_map.(j);
        let node_value n = avalue (vnode n, Some Typing.node_ty, Span.default) in
        let edge =
          if SmtUtils.smt_config.unboxing
          then [node_value i; node_value j]
          else
            [ avalue
                ( vtuple [node_value i; node_value j]
                , Some (TTuple [TNode; TNode])
                , Span.default ) ]
        in
        let trans, x =
          enc_z3_trans
            edge
            (Printf.sprintf "trans%d-%d-%d" count mapping.(i) mapping.(j))
            env
        in
        trans_input_map := EdgeMap.add (i, j) x !trans_input_map;
        trans_map := EdgeMap.add (i, j) trans !trans_map)
      graph;
    incoming_map, trans_map, trans_input_map
  ;;

  (* Propagate labels across edges outputs *)
  let encode_propagate_labels env trans_input_map labelling =
    EdgeMap.iter
      (fun (i, _) x ->
        let label = labelling.(i) in
        BatList.iter2
          (fun label x -> SmtUtils.add_constraint env (mk_term (mk_eq label.t x.t)))
          (to_list label)
          x)
      trans_input_map
  ;;

  (* Encode the series of merges at this node. *)
  let encode_node_merges env count einit emerge in_trans node name =
    (* compute each init attribute *)
    let node = avalue (vnode node, Some Typing.node_ty, Span.default) in
    let einit_i = InterpPartial.interp_partial_fun einit [node] in
    let init = encode_z3_init (Printf.sprintf "init%d-%d" count name) env einit_i in
    let emerge_i = InterpPartial.interp_partial_fun emerge [node] in
    let merged =
      BatList.fold_lefti
        (fun prev_result idx trans ->
          let str = Printf.sprintf "merge%d-%d-%d" count name idx in
          let merge_result, x = encode_z3_merge str env emerge_i in
          let trans_list = to_list trans in
          let prev_result_list = to_list prev_result in
          BatList.iter2
            (fun y x -> SmtUtils.add_constraint env (mk_term (mk_eq y.t x.t)))
            (prev_result_list @ trans_list)
            x;
          merge_result)
        init
        in_trans
    in
    merged
  ;;

  let encode_kirigami_solve
      env
      graph
      parted_srp
      count
      { aty; var_names; init; trans; merge; part; _ }
    =
    let aty = oget aty in
    let einit, etrans, emerge = init, trans, merge in
    let { rank; inputs; outputs } = parted_srp in
    (* save the number of nodes in the global network *)
    let old_nodes = SrpRemapping.get_global_nodes parted_srp in
    let remapping = Array.of_list (SrpRemapping.get_old_nodes parted_srp) in
    let nodes = nb_vertex graph in
    let label_vars : var E.t array = encode_label_vars aty var_names in
    let incoming_map, trans_map, trans_input_map =
      encode_edge_transfers env count remapping nodes etrans graph
    in
    (* Setup labelling functions *)
    let attr_sort = ty_to_sorts aty in
    (* Compute the labelling as the merge of all inputs *)
    let labelling = Array.make nodes (of_list []) in
    let eouttrans, eintrans =
      match part with
      | Some { decomp = lt, rt; _ } -> lt, rt
      | None -> Some etrans, None
    in
    (* construct the input constants *)
    let input_map = encode_kirigami_inputs env rank inputs eintrans count in
    for i = 0 to nodes - 1 do
      let in_trans = List.map (fun e -> EdgeMap.find e !trans_map) incoming_map.(i) in
      (* Kirigami: get any input transfers from the input_map *)
      let inputs = List.map fst (VertexMap.find_default [] i input_map) in
      let merged =
        encode_node_merges env count einit emerge (in_trans @ inputs) i remapping.(i)
      in
      let lbl_iv = label_vars.(i) in
      add_symbolic env lbl_iv (Ty aty);
      let l =
        lift2 (fun lbl s -> mk_constant env (create_vars env "" lbl) s) lbl_iv attr_sort
      in
      ignore
        (lift2
           (fun l merged -> SmtUtils.add_constraint env (mk_term (mk_eq l.t merged.t)))
           l
           merged);
      labelling.(i) <- l
    done;
    (* Kirigami: add dummy labels for cut nodes; just need to make sure there's as many as before.
     * This ensures the SMT query processes normally and can return counterexamples correctly. *)
    for i = nodes to old_nodes - 1 do
      let lbl_iv = label_vars.(i) in
      add_symbolic env lbl_iv (Ty aty);
      ignore
        (lift2 (fun lbl s -> mk_constant env (create_vars env "" lbl) s) lbl_iv attr_sort)
    done;
    encode_propagate_labels env !trans_input_map labelling;
    (* construct the output constants *)
    let guarantees = encode_kirigami_outputs env outputs eouttrans labelling count in
    (* divide up the hypotheses *)
    let lesser, greater =
      VertexMap.fold
        (fun _ inputs hyps ->
          List.fold_left
            (fun (lh, gh) (_, preds) ->
              match preds with
              | Lesser p -> p @ lh, gh
              | Greater p -> lh, p @ gh)
            hyps
            inputs)
        input_map
        ([], [])
    in
    lesser, greater, guarantees
  ;;

  let encode_solve env graph count { aty; var_names; init; trans; merge } =
    let aty = oget aty in
    let einit, etrans, emerge = init, trans, merge in
    let nodes = nb_vertex graph in
    let label_vars = encode_label_vars aty var_names in
    let incoming_map, trans_map, trans_input_map =
      encode_edge_transfers env count (Array.of_list (list_seq nodes)) nodes etrans graph
    in
    (* Setup labelling functions *)
    let attr_sort = ty_to_sorts aty in
    (* Compute the labelling as the merge of all inputs *)
    let labelling = Array.make nodes (of_list []) in
    for i = 0 to nodes - 1 do
      let in_trans = List.map (fun e -> EdgeMap.find e !trans_map) incoming_map.(i) in
      let merged = encode_node_merges env count einit emerge in_trans i i in
      let lbl_iv = label_vars.(i) in
      add_symbolic env lbl_iv (Ty aty);
      let l =
        lift2 (fun lbl s -> mk_constant env (create_vars env "" lbl) s) lbl_iv attr_sort
      in
      ignore
        (lift2
           (fun l merged -> SmtUtils.add_constraint env (mk_term (mk_eq l.t merged.t)))
           l
           merged);
      labelling.(i) <- l
    done;
    encode_propagate_labels env !trans_input_map labelling
  ;;

  let encode_assertions str env (f : 'a -> term E.t) (assertions : 'a list) =
    List.mapi
      (fun i eassert ->
        let z3_assert = f eassert |> to_list |> List.hd in
        let assert_var =
          mk_constant env (Printf.sprintf "%s-%d" str i) (ty_to_sort TBool)
        in
        SmtUtils.add_constraint env (mk_term (mk_eq assert_var.t z3_assert.t));
        assert_var)
      assertions
  ;;

  let conjoin_terms env terms ~(negate : bool) =
    match terms with
    | [] -> ()
    | _ ->
      (* Tim: could this just start with true and then use the whole list, instead of needing hd and tl?
       * on the other hand, we certainly don't want to have negate be set and accidentally
       * (add_constraint env false), so maybe this is fine for now *)
      let all_good =
        List.fold_left (fun acc v -> mk_and acc v.t) (List.hd terms).t (List.tl terms)
      in
      let term = if negate then mk_not all_good else all_good in
      SmtUtils.add_constraint env (mk_term term)
  ;;

  let encode_z3 (decls : Syntax.declarations) : SmtUtils.smt_env =
    let symbolics = get_symbolics decls in
    let graph = get_graph decls |> oget in
    let solves = get_solves decls in
    let assertions = get_asserts decls |> List.map InterpPartial.interp_partial in
    let requires = get_requires decls in
    let env = init_solver symbolics ~labels:[] in
    List.iteri (encode_solve env graph) solves;
    (* add assertions at the end *)
    let asserts =
      encode_assertions "assert" env (fun e -> encode_exp_z3 "" env e) assertions
    in
    conjoin_terms env asserts ~negate:true;
    (* add any require clauses constraints *)
    add_symbolic_constraints env requires env.symbolics;
    env
  ;;

  let kirigami_encode_z3 ?(check_ranked = false) part ds : SmtUtils.smt_env =
    let symbolics = get_symbolics ds in
    let graph = get_graph ds |> oget in
    let solves = get_solves ds in
    let assertions = get_asserts ds |> List.map InterpPartialFull.interp_partial in
    let requires = get_requires ds in
    let env = init_solver symbolics ~labels:[] in
    (* encode the symbolics first, so we can find them when we do the kirigami_solve
     * NOTE: could instead pass in the list of symbolics to encode_kirigami_solve *)
    add_symbolic_constraints env [] env.symbolics;
    let lesser_hyps, greater_hyps, guarantees =
      List.fold_lefti
        (fun (lhs, ghs, gs) i s ->
          let lh, gh, g = encode_kirigami_solve env graph part i s in
          lh @ lhs, gh @ ghs, g @ gs)
        ([], [], [])
        solves
    in
    (* helper for applying tuples of constraints *)
    let apply (f, v) = f v in
    (* helper for scoping separate checks *)
    let scope_checks env (f : smt_env -> unit) =
      add_command env ~comdescr:"push" SmtLang.Push;
      f env;
      (* marker to break up encoding *)
      add_command env ~comdescr:"" (SmtLang.mk_echo "\"#END_OF_SCOPE#\"");
      add_command env ~comdescr:"pop" SmtLang.Pop
    in
    (* these constraints are included in all scopes *)
    add_symbolic_constraints env requires VarMap.empty;
    (* ranked initial checks *)
    conjoin_terms env (encode_assertions "lesser-hyp" env apply lesser_hyps) ~negate:false;
    let add_guarantees env =
      encode_assertions "guarantee" env apply guarantees
    in
    (* if performing ranked check, scope the guarantees separately *)
    let gs =
      if check_ranked
      then (scope_checks env (fun e -> add_guarantees e |> conjoin_terms e ~negate:true); [])
      else add_guarantees env
    in
    (* FIXME: when guarantees are not scoped, they need to be coupled with the asserts,
     * in an (assert (not (and (and assert-0 ... assert-n) (and guarantee-0 ... guarantee-m)))) statement *)
    (* safety checks: add other hypotheses, test original assertions *)
    conjoin_terms
      env
      (encode_assertions "greater-hyp" env apply greater_hyps)
      ~negate:false;
    let asserts = encode_assertions
      "assert"
      env
      (fun e -> encode_exp_z3 "" env e)
      assertions in
    conjoin_terms env (gs @ asserts) ~negate:true;
    env
  ;;
end
