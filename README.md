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

## Architecture

Coq files are in the `theories/` directory.

They are organized as follows:

* `prelude/`: basic setup.
* `common/`: common utilities.
* `iris/`
  * `base_logic/`: Iris utilities.
  * `program_logic/`: abstract language and simulation definition.
* `data_lang/`: definition of the DataLang language.
* `data_human_lang/`: definition of a name-based variant of DataLang used in the examples.
* `tmc_1/`: TMC transformation without constructor compression.
* `tmc_2/`: TMC transformation with constructor compression.
* `aps_plus/`: APS transformation for the addition.
* `inline/`: inlining transformation.
* `compose/`: composition transformation.

For each transformation, the corresponding directory is itself organized as follows:

* `definition.v`: definition of the transformation relation.
* `metatheory.v`: lemmas about substitution and well-formedness.
* `soundness.v`: proof of the transformation soundness.
* `compile.v`: implementation of the transformation relation.
* `examples/`: concrete examples (pairs of source and transformed programs)
