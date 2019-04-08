open Batteries

module StringMap = BatMap.Make (struct
    type t = string

    let compare = String.compare
  end)

(* It's probably that most of this module is unnecessary.
   These utility functions primarily make sure that everything is
   properly ordered. If we're optimizing, we just need to make
   sure that the builtin functions always return things in the
   proper order *)

(* Returns record entries in their canonical order.
   I'm using StringMap.bindings since its return is
   guaranteed to be ordered *)
let get_record_labels map =
  List.map fst (StringMap.bindings map)

let get_record_entries map =
  List.map snd (StringMap.bindings map)

let same_labels map1 map2 =
  let cmp = List.compare (String.compare)
      (get_record_labels map1) (get_record_labels map2)
  in
  cmp = 0

let get_type_with_label record_types (ferr : string -> 'a) label =
  let has_label map = StringMap.mem label map in
  match List.find_opt has_label record_types with
  | None ->
    let msg =
      Printf.sprintf
        "Label %s does not appear in any declared record type!"
        label
    in
    ferr msg; failwith "Bad Label"
  | Some map -> map
