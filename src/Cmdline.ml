
type t =
  { debug: bool       [@short "-d"]    (** enable a debugging backtrace for nv     *)
  ; verbose: bool     [@short "-v"]    (** print out the srp solution              *)
  ; simulate: bool    [@short "-s"]    (** simulate the network on given inputs    *)
  ; bound: int option                  (** bound the number of simulation steps    *)
  ; random_test: bool [@short "-r"]    (** perform randomized network testing      *)
  ; ntests: int                        (** number of random test cases to try      *)
  ; smart_gen: bool   [@short "-g"]    (** generate relevant randomized inputs     *)
  ; smt: bool         [@short "-m"]    (** search for bugs using an smt solver     *)
  ; query: bool                        (** emit the query used by the smt solver   *)
  ; hashcons: bool    [@short "-c"]    (** enables hashconsing of all ast terms    *)
  ; memoize: bool     [@short "-z"]    (** memoizes the interpreter for reuse      *)
  ; no_caching: bool                   (** disables mtbdd operation caching        *)
  ; no_cutoff: bool                    (** disables mtbdd early termination        *)
  ; inline: bool      [@short "-i"]    (** inline the policy before simulation     *)
  ; compile: bool                      (** compile network to OCaml code before simulation *)
  ; compress: int                      (** compress the network for n failures     *)
  ; unroll: bool                       (** whether to unroll maps or not           *)
  ; unbox: bool                        (** unboxes options and flattens tuples     *)
  ; func: bool                         (** use to enable functional smt encoding   *)
  (* ; draw: bool                         (\** emits a .jpg file of the graph          *\) *)
  ; depth: int                         (** search depth for refinement procedure   *)
  ; check_monotonicity: bool           (** checks monotonicity of trans function   *)
  ; link_failures: int                 (** adds at most k link failures to the network  *)
  ; hiding: bool                       (** Use the hiding abstraction during SMT solving *)
  }
[@@deriving
  show
  , argparse
      { positional= [("file", "nv policy file")]
      ; description= "nv: a network verification framework" }]

let default =
  { debug= false
  ; verbose= false
  ; simulate= false
  ; bound= None
  ; random_test= false
  ; ntests = 100
  ; smart_gen= false
  ; smt= false
  ; query= false
  ; hashcons=false
  ; memoize = false
  ; no_caching=false
  ; no_cutoff=false
  ; inline=false
  ; compile=false
  ; compress= -1
  ; unroll= false
  ; unbox = false
  ; func = false
  (* ; draw=false *)
  ; depth=20
  ; check_monotonicity=false
  ; link_failures=0
  ; hiding=false
  }

let cfg = ref default

let get_cfg () = !cfg

let set_cfg c = cfg := c
