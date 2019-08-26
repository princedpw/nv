(*** Option utilities ***)
let oget (x: 'a option) : 'a = (* BatOption.get_exn x (failwith "internal error (oget)") *)
  match x with
  | None -> failwith "internal error (oget)"
  | Some y -> y

let omap (f : 'a -> 'b) (x: 'a option): 'b option = (* BatOption.map f x *)
  match x with
  | None -> None
  | Some y -> Some(f y)

(*** Lazy utilities ***)
let lmap (f : 'a -> 'b) (x : 'a Lazy.t) : 'b Lazy.t =
  lazy(f (Lazy.force x))

(*** List Utilities ***)
let rec list_to_string f lst =
  Printf.sprintf "[%s]" @@ BatString.concat ";" @@ List.map f lst

let map2i f lst1 lst2 =
  let rec aux count lst1 lst2 =
    match lst1, lst2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (f count hd1 hd2)::aux (count+1) tl1 tl2
    | _ -> raise (Invalid_argument "map3i: lists have different lengths")
  in aux 0 lst1 lst2

let rec map3 f lst1 lst2 lst3 =
  match lst1, lst2, lst3 with
  | [], [], [] -> []
  | hd1::tl1, hd2::tl2, hd3::tl3 -> (f hd1 hd2 hd3)::map3 f tl1 tl2 tl3
  | _ -> raise (Invalid_argument "map3: lists have different lengths")

let map3i f lst1 lst2 lst3 =
  let rec aux count lst1 lst2 lst3 =
    match lst1, lst2, lst3 with
    | [], [], [] -> []
    | hd1::tl1, hd2::tl2, hd3::tl3 -> (f count hd1 hd2 hd3)::aux (count+1) tl1 tl2 tl3
    | _ -> raise (Invalid_argument "map3i: lists have different lengths")
  in aux 0 lst1 lst2 lst3

let rec combine3 lst1 lst2 lst3 =
  match lst1, lst2, lst3 with
  | [], [], [] -> []
  | hd1::tl1, hd2::tl2, hd3::tl3 -> (hd1,hd2,hd3)::combine3 tl1 tl2 tl3
  | _ -> raise (Invalid_argument "combine3: lists have different lengths")
