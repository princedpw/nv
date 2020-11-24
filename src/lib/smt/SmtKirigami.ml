open Nv_utils.Profile
open Nv_utils.OCamlUtils
open SmtUtils
open SolverUtil
open SmtEncodingSigs
open Smt
open Nv_lang

(* Solver for Kirigami *)
let solveKirigami info query chan ~decls =
  let open Nv_lang.Syntax in
  let module ExprEnc = (val expr_encoding smt_config) in
  let module Enc = (val (module SmtClassicEncoding.ClassicEncoding (ExprEnc))
                      : SmtClassicEncoding.ClassicEncodingSig)
  in
  let nodes = Nv_datastructures.AdjGraph.nb_vertex (get_graph decls.base |> oget) in
  let assertions = get_asserts decls.prop @ get_asserts decls.guar in
  solve
    info
    query
    chan
    (fun () -> Enc.kirigami_encode_z3 decls)
    nodes
    assertions
    (decls.lth @ decls.gth)
;;