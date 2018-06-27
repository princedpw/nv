(* type of environments *)
type 'a t

(* empty environment *)
val empty : 'a t

(* bind k v is the environment with just the entry k v *)
val bind : Var.t -> 'a -> 'a t

(* look up binding, raising Unbound_var if the key is not found *)
exception Unbound_var of Var.t
val lookup : 'a t -> Var.t -> 'a 

(* add a binding, possibly shadowing preexisting bindings *)
val update : 'a t -> Var.t -> 'a -> 'a t

(* update env1 with the bindings of env2.  If both environments have the same key, env2 shadows env1 *)
val updates : 'a t -> 'a t -> 'a t

(* convert environment to a string *)
val to_string : ('a -> string) -> 'a t -> string 

(* return bindings as a list *)
val to_list : 'a t -> (Var.t * 'a) list
