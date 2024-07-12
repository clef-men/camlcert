From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  refinement.
From camlcert.data_human_lang Require Export
  compile.
From camlcert.data_human_lang Require Import
  notations.
From camlcert.aps_plus Require Import
  soundness.
From camlcert Require Import
  options.

Definition list_length : data_human_program := {[
  "list_length" := rec: "arg" :=
    match: ![𝟙] "arg" with
      NIL =>
        0
    | CONS <>, "xs" =>
        1 + $"list_length" "xs"
    end
]}%data_human_def.

Definition list_length_aps_plus : data_human_program := {[
  "list_length" := rec: "arg" :=
    match: ![𝟙] "arg" with
      NIL =>
        0
    | CONS "<>", "xs" =>
        let: "acc" := 1 in
        let: "arg" := "xs" in
        $"list_length_aps" ("acc", "arg")
    end ;
  "list_length_aps" := rec: "arg" :=
    let: "acc" := ![𝟙] "arg" in
    let: "arg" := ![𝟚] "arg" in
    match: ![𝟙] "arg" with
      NIL =>
        "acc" + 0
    | CONS "<>", "xs" =>
        let: "acc" := "acc" + 1 in
        let: "arg" := "xs" in
        $"list_length_aps" ("acc", "arg")
    end
]}%data_human_def.

Lemma list_length_aps_plus_sound :
  data_program_refinement
    (data_human_program_compile list_length)
    (data_human_program_compile list_length_aps_plus).
Proof.
  rewrite /list_length /list_length_aps_plus. apply aps_plus_sound.
  - split.
    + apply data_human_program_compile_well_formed.
      rewrite /data_human_program_well_formed map_Forall_singleton //.
    + apply data_human_program_compile_scoped.
  - rewrite /data_human_program_compile map_fmap_singleton fmap_insert map_fmap_singleton /=.
    exists {["list_length" := "list_length_aps"]}; try set_solver.
    + intros * (<- & <-)%lookup_singleton_Some.
      rewrite lookup_insert.
      eexists. split; last done. eauto 10 with aps_plus.
    + intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
      eexists. split; last done. eauto 10 with aps_plus.
Qed.
