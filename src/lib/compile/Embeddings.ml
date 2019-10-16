(** * OCaml to NV Embeddings*)
open Nv_lang
open Nv_utils
open Nv_datastructures
open PrimitiveCollections
open Syntax
open CompileBDDs
(* open Fix
 * open Memoize *)


(** Given an NV type and an OCaml value constructs an NV value*)
let rec embed_value (record_fns: string -> 'a -> 'b) (typ: Syntax.ty) : 'v -> Syntax.value =
  match typ with
    | TUnit ->
      fun _ -> Syntax.vunit ()
    | TBool ->
      fun v -> Syntax.vbool (Obj.magic v)
    | TInt _ ->
      fun v -> Syntax.vint ((Obj.magic v) |> Integer.of_int)
    | TOption ty ->
      let f = embed_value record_fns ty in
        (fun v ->
            (match Obj.magic v with
              | None -> Syntax.voption None
              | Some v' -> Syntax.voption (Some (f v'))))
    | TTuple ts ->
      let n = BatList.length ts in
      let fs = BatList.mapi (fun i ty ->
          let proj_fun = Printf.sprintf "p%d__%d" i n in
          let f_rec = embed_value record_fns ty in
          let proj_val = record_fns proj_fun in
            fun v ->
              let vrec = v in
                f_rec (Obj.magic (proj_val vrec))) ts
      in
        fun v -> Syntax.vtuple (BatList.map (fun f -> f v) fs)
    | TMap _ -> (* trivial as we represent maps with the same mtbdd + value type*)
      fun v -> Syntax.vmap (fst (Obj.magic v))
    | TArrow _ -> failwith "Function computed as value"
    | TRecord _ -> failwith "Trecord"
    | TNode ->
      fun v -> Syntax.vint ((Obj.magic v) |> Integer.of_int)
    | TEdge -> failwith "Tedge"
    | TVar {contents = Link ty} -> embed_value record_fns ty
    | TVar _ | QVar _ -> failwith ("TVars and QVars should not show up here: " ^ (PrintingRaw.show_ty typ))

(** Takes an NV value of type typ and returns an OCaml value.*)
let rec unembed_value (record_cnstrs : string -> 'c) (record_proj : string -> 'a -> 'b)
    (typ: Syntax.ty) : Syntax.value -> 'v =
  match typ with
    | TUnit ->
      fun _ -> Obj.magic ()
    | TBool ->
      fun v ->
        (match v.v with
          | VBool b -> Obj.magic b
          | _ -> failwith "mistyped value")
    | TInt _ ->
      fun v ->
        (match v.v with
          | VInt i -> Obj.magic (Integer.to_int i) (*NOTE: We translate UInts to ints but we need to change that *)
          | _ -> failwith "mistyped value")
    | TOption ty ->
      let f = unembed_value record_cnstrs record_proj ty in
        fun v ->
          (match v.v with
            | VOption None -> Obj.magic None
            | VOption (Some v') -> Obj.magic (Some (f v'))
            | _ -> failwith "mistyped value")
    | TTuple ts ->
      (*TODO: this case is wrong? fix it*)
      let n = BatList.length ts in
      let f_cnstr = record_cnstrs (string_of_int n) in (*function that constructs the record*)
      let fs = (*functions that unembed each value of a tuple *)
        BatList.map (fun ty -> unembed_value record_cnstrs record_proj ty) ts
      in
        fun v ->
          (match v.v with
            | VTuple vs ->
              BatList.fold_left2 (fun acc f v -> Obj.magic (acc (f v))) f_cnstr fs vs
              |> Obj.magic
            | _ -> failwith "mistyped value")
    | TMap (_, vty) ->
      (* this is trivial as OCaml maps are NV maps plus a value type*)
      fun v ->
        (match v.v with
          | VMap vdd -> Obj.magic (vdd, vty)
          | _ -> failwith "mistyped value")
    | TArrow _ -> failwith "Function computed as value"
    | TRecord _ -> failwith "Trecord"
    | TNode ->
      fun v ->
        (match v.v with
          | VNode n -> Obj.magic n
          | _ -> failwith "mistyped value")
    | TEdge -> failwith "Tedge"
    | TVar {contents = Link ty} -> unembed_value record_cnstrs record_proj ty
    | TVar _ | QVar _ -> failwith ("TVars and QVars should not show up here: " ^ (PrintingRaw.show_ty typ))

(* Only memoizing outermost call on type. There is probably little merit to
   memoize the recursive calls. TODO: memoize based on values too?*)

(* NOTE: Using hashing memoization degrades performance probably because hashing
   the type takes time.
   NOTE: Using ordered (i.e. a tree) comparison is much
   faster but still slightly degrades performance.
   TODO: Instead we should assign each type an integer/tag and then look that up in a
   memoized table.
*)

let embed_cache : ((int*int -> int) array) ref = ref (Array.create 100 (fun _ -> 0))

let build_embed_cache record_fns =
  embed_cache := Array.map (fun ty -> Obj.magic (embed_value record_fns ty)) !type_array

let unembed_cache : (int*int ->int) array ref = ref (Array.create 100 (fun _ -> 0))

let build_unembed_cache record_cnstrs record_fns =
  unembed_cache := Array.map (fun ty -> Obj.magic (unembed_value record_cnstrs record_fns ty)) !type_array

let embed_value_id ty_id (v: 'v) : Syntax.value =
  let embedding : 'v -> value= !embed_cache.(ty_id) |> Obj.magic in
  embedding v

let unembed_value_id ty_id (v: Syntax.value) : 'v =
  let unembedding : value -> 'v = !unembed_cache.(ty_id) |> Obj.magic in
  unembedding v

(* let embed_value_id ty_id (v: 'v) : Syntax.value =
 *   Printf.printf "em get ty_id:%d\n" ty_id;
 *   let embedding : 'v -> value= !embed_cache.(ty_id) |> Obj.magic in
 *   embedding v
 *
 * let unembed_value_id ty_id (v: Syntax.value) : 'v =
 *   Printf.printf "un get ty_id:%d\n" ty_id;
 *   let unembedding : value -> 'v = !unembed_cache.(ty_id) |> Obj.magic in
 *   unembedding v *)

(* let cache_default_size = 10
 * let embed_cache : int BatDynArray.t = BatDynArray.make cache_default_size
 *
 * let build_embed_cache record_fns =
 *   Array.iter (fun ty -> BatDynArray.add embed_cache (Obj.magic (embed_value record_fns ty))) !type_array
 *
 * let unembed_cache : int BatDynArray.t = BatDynArray.make cache_default_size
 *
 * let build_unembed_cache record_cnstrs record_fns =
 *   Array.iter (fun ty -> BatDynArray.add unembed_cache (unembed_value record_cnstrs record_fns ty)) !type_array
 *
 * let total_time = ref 0.0
 *
 * let embed_value_id ty_id (v: 'v) : Syntax.value =
 *   let embedding = Obj.magic (BatDynArray.get embed_cache ty_id) in
 *   embedding v
 *
 * let unembed_value_id ty_id (v: Syntax.value) : 'v =
 *   let unembedding = BatDynArray.get unembed_cache ty_id in
 *   unembedding v *)