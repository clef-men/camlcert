From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  refinement.
From simuliris.data_human_lang Require Export
  compilation.
From simuliris.data_human_lang Require Import
  notations.
From simuliris.aps_plus_2 Require Import
  definition.

Definition list_length : data_human_program := {[
  "list_length" := (BNamed "arg", (
    match: ![𝟙] "arg" with
      NIL =>
        0
    | CONS <>, "xs" =>
        1 + $"list_length" "xs"
    end
  )%data_human_expr)
]}.

Definition list_length_aps_plus : data_human_program := {[
  "list_length" := (BNamed "arg", (
    match: ![𝟙] "arg" with
      NIL =>
        0
    | CONS "<>", "xs" =>
        let: "acc" := 1 in
        let: "arg" := "xs" in
        $"list_length_aps" ("acc", "arg")
    end
  )%data_human_expr) ;
  "list_length_aps" := (BNamed "arg", (
    let: "acc" := ![𝟙] "arg" in
    let: "arg" := ![𝟚] "arg" in
    match: ![𝟙] "arg" with
      NIL =>
        0 + "acc"
    | CONS "<>", "xs" =>
        let: "acc" := 1 + "acc" in
        let: "arg" := "xs" in
        $"list_length_aps" ("acc", "arg")
    end
  )%data_human_expr)
]}.

Section list_length_aps_plus_sound.
  Variable aps_plus_sound : ∀ progₛ progₜ,
    data_program_valid progₛ →
    aps_plus progₛ progₜ →
    data_program_refinement progₛ progₜ.

  Lemma list_length_aps_plus_sound :
    data_program_refinement
      (data_human_program_compile list_length)
      (data_human_program_compile list_length_aps_plus).
  Proof using aps_plus_sound.
    rewrite /list_length /list_length_aps_plus. apply aps_plus_sound.
    - split.
      + apply data_human_program_compile_well_formed.
        rewrite /data_human_program_well_formed map_Forall_singleton //.
      + apply data_human_program_compile_scope.
    - rewrite /data_human_program_compile map_fmap_singleton fmap_insert map_fmap_singleton /=.
      exists {["list_length" := "list_length_aps"]}; try set_solver.
      + intros * (<- & <-)%lookup_singleton_Some.
        rewrite lookup_insert.
        eexists. split; last done. repeat econstructor.
      + intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
        eexists. split; last done. repeat econstructor.
  Qed.
End list_length_aps_plus_sound.
