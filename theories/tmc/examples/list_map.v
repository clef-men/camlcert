From simuliris Require Import
  prelude.
From simuliris.language Require Import
  notations.
From simuliris.tmc Require Import
  definition.

Definition list_mapₛ : program := {[
  "list_map" := (
    match: SND $0 with
      NIL =>
        NIL
    | CONS =>
        let: FST $2 in
        let: $0 $1 in
        CONS $0 ("list_map" ($1, $3))
    end
  )%E
]}.

Definition list_mapₜ : program := {[
  "list_map" := (
    match: SND $0 with
      NIL =>
        NIL
    | CONS =>
        let: FST $2 in
        let: $0 $1 in
        let: CONS $0 #() in
        "list_map_dps" ($0.(2), ($2, $4)) ;;
        $0
    end
  )%E ;
  "list_map_dps" := (
    let: FST $0 in
    let: SND $1 in
    match: SND $0 with
      NIL =>
        $1 <- NIL
    | CONS =>
        let: FST $2 in
        let: $0 $1 in
        let: CONS $0 #() in
        $8 <- $0 ;;
        "list_map_dps" ($0.(2), ($2, $4))
    end
  )%E
]}.

Lemma list_map_tmc :
  tmc list_mapₛ list_mapₜ.
Proof.
  exists {["list_map" := "list_map_dps"]}.
  - apply map_Forall_singleton. done.
  - intros * (<- & <-)%lookup_singleton_Some (<- & _)%lookup_singleton_Some. done.
  - rewrite /list_mapₛ /list_mapₜ.
    intros * (<- & <-)%lookup_singleton_Some.
    eexists. split; first done. repeat constructor.
  - rewrite /list_mapₛ /list_mapₜ.
    intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
    eexists. split; first done.
    do 6 constructor; [repeat constructor.. |].
    eapply tmc_dps_constr_1; first repeat constructor.
    + asimpl. eapply tmc_dps_call; repeat constructor.
    + done.
Qed.
