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


## Link to the POPL'25 publication

This repository serves as an artifact for the publication

  Tail Modulo Cons, OCaml, and Relational Separation Logic
  Clément Allain, Frédéric Bour, Basile Clément, François Pottier, Gabriel Scherer
  POPL 2025

a preprint of this submission is available at
  https://zenodo.org/records/13744624

### Scope

The present artifact only covers the formal claim in the article
related to the correctness of the TMC transformation in an idealized
setting, mechanized using Coq and Iris.

Notably, we did not include the OCaml compiler changes themselves or
the List.map microbenchmarks in the artifact submission. Our
implementation of TMC within OCaml is open-source and available at

  https://github.com/ocaml/ocaml/blob/trunk/lambda/tmc.ml
  permalink: https://github.com/ocaml/ocaml/blob/42adb2793657f4ef4f72eb9fc362c73e8eb2eb9f/lambda/tmc.ml

but we felt that evaluating it, or the micro-benchmarks, would have
unclear scientific benefits; the OCaml compiler is already
well-packaged and widely available, and the content we want to ensure
that reviewers can access and build upon in 10 years (or at least
access and compare to their own work) are the mechanized proofs. It
would also make it harder to find artifact reviewers, who would have
to review the OCaml implementation, benchmarking, and Coq+Iris
developments, all at the same time.

### Mapping from the article to the Coq development

In the following we include an exhaustive list of all formal claims in
the article, and their counterpart in the Coq development, if
available.

#### Section 1: introduction

The specification of the variants of map shown in the article are not
in the Coq development. They are specific instances, given for
exposition purposes, of the general correctness result of the
transformation:
- the statement "map >= map" (the first one) is an instance of
    `tmc_expr_dir_specification'` in theories/tmc_2/soundness.v
- the statement "map >= map_dps" (the second one) is an instance of
    `tmc_expr_dps_specification'`, same file

(Checking the relation at this point may be non-trivial, reading the
rest of the article will make this clearer.)


#### Section 2: TMC on an idealized language

The definition of Datalang (figures 1 and 2) is given in

- `theories/data_lang/syntax.v` (`data_expr`, `data_definition`, `data_program`)
- `theories/data_lang/notations.v` (notations, including the syntactic sugar of Figure 2)

The operational semantics (figure 3) is mostly given in
`theories/data_lang/semantics.v` . This file contains the head-reduction rules (`data_head_step`) and the evaluation contexts (`data_excti`). There is a generic machinery to define the small-step semantics in `theories/iris/program_logics`, which is instantiated for DataLang in `theories/data_lang/language.v`.

The example of List.map in DataLang (figure 4) is included in `theories/tmc_1/examples/list_map.v`.

The definition of the TMC transformations, as relations, are in `theories/tmc_1/definition.v`:
- the whole-program transformation (Figure 5) is the `tmc` Record at the end
- the direct-style transformation (Figure 6) is `tmc_expr_dir`
- the DPS transformation (Figure 7) is `tmc_expr_dps`


##### 2.3 Realizing the relation as a function

We prove that the transformation relations are effective by defining
a function from an input program to a related output program. The
proof is in `theories/tmc_1/compile.v`. The meat of the definition is
in `tmc_compile_expr'`, and the fact that it realizes the relation is
stated in `tmc_compile_sound`.


#### Section 3: OCaml implementation

For the most part, Section 3 does not contain formal claims and is not
covered in our Coq development.

One notable exception is the "Constructor Compression" optimization
described in Section 3.4. This is a refinement of the TMC
transformation that we also included in our formal development. It is
developed in `theories/tmc_2`, which is mostly a copy and extension of
`theories/tmc_1` with constructor compression (it lacks some minor
aspects, for example it does not currently have
a `compile.v` function).

To see that `tmc_2/` supports constructor compression, look at:
- the extra `tmc_ctx` parameter in the DPS transformation relation `tmc_expr_dps`
- its use in the rules `tmc_expr_dps_block_{1,2}`, which push a new frame in this context
- its use in `tmc_expr_dps_reify`, which adds a context list back in the transformed expression


#### Section 4: Specifying TMC

The specification of the direct-style transformation (Section 4.1) is
`tmc_expr_dir_specification'` in `theories/tmc_1/soundness.v`

The specification of the DPS transformation (Section 4.2) is
`tmc_expr_dps_specification'` in `theories/tmc_1/soundness.v`

The heap bijection is defined in ... . The BijInsert rule in the paper
corresponds to the lemma `sim_state_interp_heap_bij_insert` in
`theories/data_lang/sim/basic_rules.v`. The relation with the paper
deserves an explanation:

```coq
  Lemma sim_state_interp_heap_bij_insert lₛ lₜ :
    lₛ ⋈ lₜ ⊢ |++>
    lₛ ≈ lₜ.
```

The bowtie symbol (the two locations have similar values) is a generic notation defined by a typeclass in `theories/common/typeclasses.v`, which is instantiated in `theories/iris/base_logic/sim/heap_bij.v` as follows:

```coq
    Definition sim_heap_bij_tie lₛ lₜ : iProp Σ :=
      ∃ vₛ vₜ,
      lₛ ↦ₛ vₛ ∗ lₜ ↦ₜ vₜ ∗ vₛ ≈ vₜ.
    #[global] Instance sim_heap_bij_bi_tie : BiTie (iProp Σ) locₛ locₜ :=
      Build_BiTie sim_heap_bij_tie.
```

where you can recognize the precondition from the paper. This definition in `iris/base_logic` is itself parametrized over a syntactic class of value with a similarity relation, and its use in `data_lang` comes from an instantiation found in `theories/data_lang/sim/definition.v` (`Instance data_val_bi_similar`). The definition of value similarity (Figure 10) is precisely given in this instance, as the argument to `Build_BiSimilar`.


#### Section 5: Relational Separation Logic

The definition of the relation {P} eₛ ≳ eₜ <X> {Phi} from the relation
eₛ ≳ eₜ <X> {Phi} is given in `data_lang/sim/notations.v`; it is
slightly generalized from the one shown in the paper, in a way that is
standard in the Iris community (an extra monotonicity property is baked in) – compare for example with the definition in
  https://gitlab.mpi-sws.org/iris/iris/-/blob/6dece4170850ea78e38b6b6c12fe3a5494966ab4/iris/bi/weakestpre.v#L82-85

The rules of the relational program logic in Figure 11 are defined as lemmas in the Coq development.
The language-independent rules are in `theories/iris/program_logic/sim/rules.v`
and the DataLang-specific rules are in `theories/data_lang/sim/{basic,derived}_rules.v`.

In more details:
- RelPost, RelStuck, RelBind: `sim_post`, `sim_strongly_stuck`, `sim_bind` (in `program_logic/sim/rules.v`)
- RelSrcPure, RelTgtPure: `sim_pure_stepₛ`, `sim_pure_stepₜ`
- RelSrcBlock{1,2}: `sim_blockₛ{1,2}` (in `data_lang/sim/basic_rules.v`)
- RelTgtBlock: `sim_blockₜ`
- all following rules until RelProtocol: below at the same place (in the `sim` section)
- RelProtocol: the corresponding rule `sim_apply_protocol` is slightly
  more general, as it is allowed to inspect the states σₛ,σₜ and the
  proof that they are related. Technically the rule shown in the paper
  is a corollary of this result.


#### Section 6: Abstract protocols

The X{TMC} protocol in Figure 12 is defined in `tmc_1/soundness.v`: `tmc_protocol_dir` and `tmc_protocol_dps`.

##### Other examples of protocols

Our Coq development also contains correctness proofs for related
program transformations, such as inlining and accumulator-passing
style. Their development are in `theories/inline` and
`theories/aps_plus`, they follow the same structure, including
a `compile.v` function deciding a particular transformation
strategy -- for `inline`, we inline function calls that carry an
inlining annotation.


#### Section 7

TODO
