From simuliris Require Import
  prelude.
From simuliris.tmc_lang Require Export
  refinement.
From simuliris.tmc_lang Require Import
  notations.
From simuliris.tmc Require Import
  soundness.

Definition list_appendₛ : program := {[
  "list_append" := (
    match: ![𝟙] $0 with
      NIL =>
        NIL
    | CONS =>
        CONS $0 ("list_append" ($1, ![𝟚] $2))
    end
  )%E
]}.

Definition list_appendₜ : program := {[
  "list_append" := (
    match: ![𝟙] $0 with
      NIL =>
        NIL
    | CONS =>
        let: CONS $0 #() in
        ( let: ($2, ![𝟚] $3) in
          "list_append_dps" (($1, 𝟚), $0)
        ) ;;
        $0
    end
  )%E ;
  "list_append_dps" := (
    let: ![𝟙] $0 in
    let: ![𝟚] $0 in
    let: ![𝟙] $1 in
    let: ![𝟚] $3 in
    match: ![𝟙] $0 with
      NIL =>
        $1 <-[$2]- NIL
    | CONS =>
        let: CONS $0 #() in
        $4 <-[$5]- $0 ;;
        let: ($2, ![𝟚] $3) in
        "list_append_dps" (($1, 𝟚), $0)
    end
  )%E
]}.

Lemma list_append_valid :
  program_valid list_appendₛ.
Proof.
  split; apply map_Forall_singleton; naive_solver lia.
Qed.

Lemma list_append_tmc :
  tmc list_appendₛ list_appendₜ.
Proof.
  exists {["list_append" := "list_append_dps"]};
    try set_solver;
    rewrite /list_appendₛ /list_appendₜ.
  - intros * (<- & <-)%lookup_singleton_Some (<- & _)%lookup_singleton_Some. done.
  - intros * (<- & <-)%lookup_singleton_Some.
    rewrite lookup_insert.
    eexists. split; last done. repeat econstructor.
  - intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
    eexists. split; last done.
    repeat constructor. eapply tmc_dps_constr_1; first constructor.
    + eapply tmc_dps_call; repeat constructor.
    + done.
Qed.

Lemma list_append_sound :
  program_refinement list_appendₛ list_appendₜ.
Proof.
  apply tmc_sound, list_append_tmc. apply list_append_valid.
Qed.
