open Batteries
open Nv_lang
open Syntax
open Nv_datastructures
open AdjGraph

let width = 32
let e_num n = e_val (vint (Integer.of_int n))

(* add an additional argument for the measure to the attribute
 * increment the measure in the output tuple *)
let measure_trans e =
  let incr_body m = eop (UAdd width) [m; annot (TInt width) (e_num 1)] in
  e
;;

(* return a tuple of the original init plus 0 *)
let measure_init e =
  let zero = annot (TInt width) (e_num 0) in
  (* FIXME: do we need to flatten the tuple if e returns one? *)
  let ety = Option.map (fun t -> TTuple [t; TInt width]) e.ety in
  (* FIXME: instead of an etuple, we want a function *)
  aexp (etuple [e; zero], ety, e.espan)
;;

(* add additional arguments for the measure of the attributes
 * compare the attributes, return the measure associated with the one returned;
 * fail if the merge is not selective? *)
let measure_merge e = e

let measure_solve s =
  (* add a measure *)
  let aty = s.aty in
  (* add a variable for the measure *)
  let var_names = s.var_names in
  { s with
    aty
  ; var_names
  ; init = measure_init s.init
  ; trans = measure_trans s.trans
  ; merge = measure_merge s.merge
  }
;;
