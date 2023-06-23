From simuliris Require Import
  prelude.
From simuliris.tmc_lang Require Export
  refinement.
From simuliris.tmc_lang Require Import
  notations.
From simuliris.tmc Require Import
  soundness.

Definition list_mapₛ : program := {[
  "list_map" := (
    match: ![𝟚] $0 with
      NIL =>
        NIL
    | CONS =>
        let: ![𝟙] $2 in
        let: $0 $1 in
        CONS $0 ("list_map" ($1, $3))
    end
  )%E
]}.

Definition list_mapₜ : program := {[
  "list_map" := (
    match: ![𝟚] $0 with
      NIL =>
        NIL
    | CONS =>
        let: ![𝟙] $2 in
        let: $0 $1 in
        let: CONS $0 #() in
        ( let: ($2, $4) in
          "list_map_dps" (($1, 𝟚), $0)
        ) ;;
        $0
    end
  )%E ;
  "list_map_dps" := (
    let: ![𝟙] $0 in
    let: ![𝟚] $0 in
    let: ![𝟙] $1 in
    let: ![𝟚] $3 in
    match: ![𝟚] $0 with
      NIL =>
        $1 <-[$2]- NIL
    | CONS =>
        let: ![𝟙] $2 in
        let: $0 $1 in
        let: CONS $0 #() in
        $6 <-[$7]- $0 ;;
        let: ($2, $4) in
        "list_map_dps" (($1, 𝟚), $0)
    end
  )%E
]}.

Lemma list_map_valid :
  program_valid list_mapₛ.
Proof.
  split; apply map_Forall_singleton; naive_solver lia.
Qed.

Lemma list_map_tmc :
  tmc list_mapₛ list_mapₜ.
Proof.
  exists {["list_map" := "list_map_dps"]};
    try set_solver;
    rewrite /list_mapₛ /list_mapₜ.
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

Lemma list_map_sound :
  program_refinement list_mapₛ list_mapₜ.
Proof.
  apply tmc_sound, list_map_tmc. apply list_map_valid.
Qed.
