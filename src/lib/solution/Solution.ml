open ANSITerminal
open Nv_datastructures
open Nv_lang
open Collections
open AdjGraph (* For VertexMap *)
open Syntax
open Nv_utils
open OCamlUtils

(* The mask field is used for AttributeSlicing -- it is a syntax.value with the
   same structure as the attribute (e.g. both tuples of the same size), but
   with a boolean in place of each base value. A value of false indicates that
   the value at that location in each attribute is bogus -- i.e. it was not
   needed to produce the counterexample *)
type sol = {sol_val: value; mask : value option}
type t =
  { symbolics: (var * value) list;
    solves: (var * value) list;
    assertions: bool list; (* One for each assert statement *)
    labels: value VertexMap.t; (* Deprecated -- included only for backwards compatibility *)
  }

type map_back = t -> t

let sol_to_string sol =
  Printf.sprintf "{sol_val = %s; mask = %s}"
    (Printing.value_to_string sol.sol_val)
    (match sol.mask with | None -> "None" | Some m -> Printing.value_to_string m)

let rec value_to_mask v =
  let true_val = avalue (vbool true, Some TBool, v.vspan) in
  match v.v with
  | VBool _ | VInt _ | VNode _ | VUnit -> true_val
  | VEdge _ -> avalue (vtuple [true_val; true_val], Some (TTuple [TBool; TBool]), v.vspan)
  | VOption None -> avalue (voption (Some true_val), Some (TOption TBool), v.vspan)
  | VOption Some v' ->
    let rec_val = value_to_mask v' in
    let rec_val_ty = rec_val.vty |> oget in
    avalue (voption (Some (value_to_mask v')), Some (TOption rec_val_ty), v.vspan)
  | VTuple vs ->
    let rec_vals = List.map value_to_mask vs in
    let rec_val_tys = List.map (fun v -> v.vty |> oget) rec_vals in
    avalue (vtuple rec_vals, Some (TTuple (rec_val_tys)), v.vspan)
  | VRecord map ->
    let rec_val = StringMap.map value_to_mask map in
    let rec_val_map = StringMap.map (fun v -> v.vty |> oget) rec_val in
    avalue (vrecord rec_val, Some (TRecord rec_val_map), v.vspan)
  | VMap _ -> failwith "Not yet implemented"
  | VClosure _ -> failwith "Closures not allowed as attributes"
;;

let rec mask_type_ty ty =
  match ty with
  | TBool | TInt _ | TNode | TUnit -> TBool
  | TEdge -> TTuple [TBool; TBool]
  | TOption ty -> TOption (mask_type_ty ty)
  | TRecord map -> TRecord (StringMap.map mask_type_ty map)
  | TTuple tys -> TTuple (List.map mask_type_ty tys)
  | TMap (kty, vty) -> TMap (kty, mask_type_ty vty)
  | TVar {contents = Link ty} -> mask_type_ty ty
  | TVar _ | QVar _ | TArrow _ -> failwith "internal error (mask_ty)"

(* This function works correctly, but I think it's almost always a
   mistake to use it. Use mask_type_ty instead. *)
(* let mask_type_sol sol =
   let one_attr = VertexMap.choose sol.labels |> snd in
   (value_to_mask one_attr).vty |> oget *)

(* Prints the mask itself; useful for seeing which parts of a value are hidden *)
let print_masked_type unmasked_ty sol =
  let print_if_true ty m =
    if m then Printing.ty_to_string ty else "_"
  in
  let rec construct_string ty mask =
    match ty, mask.v with
    | (TBool| TInt _ | TUnit | TNode), VBool m1 ->
      print_if_true ty m1
    | TEdge, VTuple [{v=VBool b1}; {v=VBool b2}] ->
      Printf.sprintf "%s~%s" (print_if_true TNode b1) (print_if_true TNode b2)
    | TOption _, VOption None ->
      (* If mask if None then the entire option value is masked *)
      print_if_true ty false
    | TOption ty', VOption Some m ->
      (* If mask is Some then the option value is relevant *)
      Printf.sprintf "(option[%s])" @@ construct_string ty' m
    | TTuple tys, VTuple ms ->
      Printf.sprintf "(%s)" @@ BatString.concat "," @@
      List.map2 construct_string tys ms
    | TRecord vmap, VRecord bmap ->
      let zipped =
        StringMap.fold
          (fun k v acc -> StringMap.add k (StringMap.find k bmap, v) acc)
          vmap StringMap.empty
      in
      RecordUtils.print_record ~sep:"=" (fun (m, ty) -> construct_string ty m) zipped
    | TMap (_, vty), VMap mbdd ->
      (* Maps are tricky since we can hypothetically hide different parts of
         different keys *)
      let mbindings, _ = BddMap.bindings mbdd in
      (* Maps the possible map values (that appear in mbindings) to the keys which
         use that binding *)
      let maskMap : Syntax.value list ValueMap.t =
        List.fold_left
          (fun acc (k, v) -> ValueMap.modify_def [] v (fun lst -> k::lst) acc)
          ValueMap.empty mbindings
      in
      Printf.sprintf "map{%s}" @@
      ValueMap.fold
        (fun v ks acc ->
           Printf.sprintf
             "%s %s->%s;"
             acc
             (OCamlUtils.list_to_string Printing.value_to_string ks)
             (construct_string vty v))
        maskMap ""
    | (TBool | TInt _ | TUnit | TNode | TEdge
      | TOption _ | TTuple _ | TRecord _ | TMap _), _ ->
      failwith "print_masked_type: Mask did not match value!"
    | (TVar _ | QVar _ | TArrow _), _ ->
      failwith "print_masked_type: Nonsense type"
  in
  match sol.mask with
  | None -> Printing.ty_to_string unmasked_ty
  | Some mask -> construct_string unmasked_ty mask
;;

(* Print a value with only the parts where the mask is true. *)
let rec print_masked mask v =
  let print_if_true b v =
    if b then Printing.value_to_string v else "_"
  in
  match v.v, mask.v with
  | (VBool _ | VInt _ | VUnit | VNode _ ), VBool m1 ->
    print_if_true m1 v
  | VEdge (n1,n2), VTuple [{v=VBool b1}; {v=VBool b2}] ->
    Printf.sprintf "%s~%s" (print_if_true b1 (vnode n1)) (print_if_true b2 (vnode n2))
  | VOption _, VOption None ->
    (* If mask if None then the entire option value is masked *)
    print_if_true false v
  | VOption None, VOption Some _ ->
    (* If mask is Some then the option value is relevant *)
    print_if_true true v
  | VOption Some v, VOption Some m ->
    Printf.sprintf "(Some %s)" @@ print_masked m v
  | VTuple vs, VTuple bs ->
    Printf.sprintf "(%s)" @@ BatString.concat "," @@
    List.map2 print_masked bs vs
  | VRecord vmap, VRecord bmap ->
    let zipped =
      StringMap.fold
        (fun k v acc -> StringMap.add k (StringMap.find k bmap, v) acc)
        vmap StringMap.empty
    in
    RecordUtils.print_record ~sep:"=" (fun (m, v) -> print_masked m v) zipped
  | VMap vbdd, VMap mbdd ->
    let vbindings, _ = BddMap.bindings vbdd in
    let mbindings, _ = BddMap.bindings mbdd in
    let combined =
      List.fold_left
        (fun acc (k,v) ->
           StringMap.add (Printing.value_to_string k) (List.assoc k mbindings, v) acc)
        StringMap.empty vbindings
    in
    RecordUtils.print_record ~sep:":=" (fun (m,v) -> print_masked m v) combined
  | (VBool _ | VInt _ | VUnit | VNode _ | VEdge _
    | VOption _ | VTuple _ | VRecord _ | VMap _), _ ->
    failwith "Mask did not match value!"
  | VClosure _, _ -> failwith "print_masked: tried to print VClosure"
;;

let print_fun {sol_val; mask} =
  match mask with
    | None -> Printing.value_to_string ~show_types:false sol_val
    | Some m -> print_masked m sol_val

let print_solution (solution : t) =
  let cfg = Nv_lang.Cmdline.get_cfg () in
  print_newline () ;
  if cfg.verbose then
    begin
      (* Print symbolics*)
      List.iter
        (fun (k,v) ->
           Printf.printf "%s:%s\n" (Nv_datastructures.Var.name k) (Nv_lang.Printing.value_to_string v) )
        solution.symbolics ;
      (* Print solutions*)
      List.iter (fun (k,v) ->
          Printf.printf "Printing solutions for %s\n" (Var.to_string k);
          print_endline (Printing.value_to_string ~show_types:false v)) solution.solves
    end;
  ( match solution.assertions with
    | [] ->
      print_string [green; Bold] "Success: " ;
      Printf.printf "No assertions provided, so none failed\n"
    | asns ->
      let all_pass = List.for_all (fun x -> x) asns in
      if all_pass then (
        print_string [green; Bold] "Success: " ;
        Printf.printf "all assertions passed\n" )
      else
        (print_string [red; Bold] "Failed: " ;
         asns
         |> BatList.mapi (fun i b -> Printf.sprintf "Assertion %d" i, b)
         |> BatList.filter_map (fun (s, b) -> if not b then Some s else None)
         |> BatString.concat ", "
         |> print_endline))
      ;
      print_newline ()
