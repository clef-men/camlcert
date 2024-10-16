## Synopsis

This project is part of the [Iris Masterplan](https://julesjacobs.com/slides/iris-masterplan.pdf).
It aims at verifying program transformations from the OCaml compiler.

## Building

First, you need to install [opam](https://opam.ocaml.org/) (>= 2.0).

To make sure it is up-to-date, run:

```
opam update --all --repositories
```

To compile Coq proofs, run the following commands:

```
opam switch create . --deps-only --repos default,coq-released=https://coq.inria.fr/opam/released,iris-dev=git+https://gitlab.mpi-sws.org/iris/opam.git --yes
eval $(opam env --switch=. --set-switch)
make
```
