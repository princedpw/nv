# An intermediate language for network verification

NV is a functional language that can be used to express the semantics of
routing protocols, such as BGP, OSPF, etc. The language is designed to be
minimal (based on lambda calculus), yet expressive (one
can easily express new protocols or customizations of existing ones).

See [examples](https://github.com/princedpw/nv/tree/master/examples) and the
[wiki](https://github.com/princedpw/nv/wiki) for some more information.

Please note that NV is still at an early development stage.

## Building nv

To start with, make sure you have all of these dependencies: `gcc, make, m4` for `ocaml`, `g++` for `mlcuddidl` and `z3` (which needs `python2.7` and `libgmp`).
Use `opam` to install the `ocaml` dependencies.

If you don't have `opam` yet, see the [OPAM install instructions](https://opam.ocaml.org/doc/Install.html).
This is the best way to set up `ocaml`.

You can see which `ocaml` packages you're missing to run `nv` using `dune`:

```
dune external-lib-deps --missing @all
```

Alternatively, execute the following to install required packages once `opam` is up:

```
opam install -y \
  integers \
  batteries \
  ounit \
  ansiterminal \
  menhir \
  mlcuddidl \
  ppx_deriving \
  ppx_deriving_argparse \
  lru-cache \
  zarith \
  ocamlgraph \
  fileutils \
  parmap \
  fix \
  jupyter \
  dune
```

You may install z3 via opam as well (`opam install -y z3`), but this is not recommended
as it takes a long time, and may be out of date. It is recommended that you install
z3 yourself, separately. 
Z3 version >= 4.8.7 is recommended to avoid a bug that our constraints sometimes trigger on earlier versions of z3.

You will need Batteries version >= 3.0.0.
You will also need `mlcuddidl` version <= 3.0.4.

Then clone the repo and run `dune build src/exe/main.exe`.

### MacOS

You may encounter issues installing `mlcuddidl.3.0.4`. Per issue [#7](https://github.com/princedpw/nv/issues/7),
we recommend you try building `mlcuddidl` from source:

```
opam source mlcuddidl.3.0.4 --dir "$YOUR_SRC_DIR"
cd "$YOUR_SRC_DIR/mlcuddidl.3.0.4"
make distclean # just to be safe
./configure --disable-profiling
make
make install
```

This has been tested for ocaml 4.05.0 and 4.07.1.

### Ubuntu (16.04+)

```
sudo apt update
sudo apt install gcc g++ make m4 libgmp-dev python2.7 libz3-dev z3 libzmq3-dev zlib1g-dev
```

## Getting started with NV

To get started with NV, we recommend taking a look at some of the [examples](https://github.com/princedpw/nv/tree/master/examples). For instance, consider [this](https://github.com/NetworkVerification/nv/blob/master/examples/simple_protocol.nv) example network running a simple protocol. To compute the stable state of this network using networking simulation execute the following command in your shell:

```
./nv -simulate -verbose examples/simple_protocol.nv 
```

The `-verbose` option prints the stable state (solutions) for each node.

Alternatively, you can use SMT verification to check that the assertions given in the file are true of the network's stable state.

```
./nv -smt -verbose examples/simple_protocol.nv 
```

Note that in order to use the SMT backend, you must have the z3 executable on your PATH. It should have the name "z3".

## Translating Router Configs to NV.

See the [wiki](https://github.com/NetworkVerification/nv/wiki/Translating-Configurations).

## Troubleshooting

### "symbol lookup error: Z3_get_full_version"

Add the ocaml z3 lib to your `LD_LIBRARY_PATH`:

```
eval $(opam env)
export LD_LIBRARY_PATH="$OPAM_SWITCH_PREFIX/lib/z3"
```
