From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  refinement.
From camlcert.data_human_lang Require Export
  compile.
From camlcert.data_human_lang Require Import
  notations.
From camlcert.tmc_2 Require Import
  soundness.
From camlcert Require Import
  options.

Definition list_double : data_human_program := {[
  "list_double" := rec: "xs" :=
    match: "xs" with
      NIL =>
        NILₕ
    | CONS "x", "xs" =>
        CONSₕ "x" (CONSₕ "x" ($"list_double" "xs"))
    end
]}%data_human_def.

Definition list_double_tmc : data_human_program := {[
  "list_double" := rec: "xs" :=
    match: "xs" with
      NIL =>
        NILₕ
    | CONS "x", "xs" =>
        let: "dst" := CONSₕ "x" #ₕ() in
        ( let: "x" := "x" in
          let: "dst'" := CONSₕ "x" #ₕ() in
          "dst" <-[𝟚] "dst'" ;;
          let: "arg" := "xs" in
          $"list_double_dps" ("dst'", 𝟚, "arg")
        ) ;;
        "dst"
    end ;
  "list_double_dps" := rec: "arg" :=
    let: "dst_idx" := ![𝟙] "arg" in
    let: "idx" := ![𝟚] "dst_idx" in
    let: "dst" := ![𝟙] "dst_idx" in
    let: "xs" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
        "dst" <-["idx"] NILₕ
    | CONS "x", "xs" =>
        let: "x1" := "x" in
        let: "x2" := "x" in
        let: "dst'" := CONSₕ "x2" #ₕ() in
        "dst" <-["idx"] CONSₕ "x1" "dst'" ;;
        let: "arg" := "xs" in
        $"list_double_dps" ("dst'", 𝟚, "arg")
    end
]}%data_human_def.

Lemma list_double_tmc_sound :
  data_program_refinement
    (data_human_program_compile list_double)
    (data_human_program_compile list_double_tmc).
Proof.
  rewrite /list_double /list_double_tmc. apply tmc_sound.
  - split.
    + apply data_human_program_compile_well_formed.
      rewrite /data_human_program_well_formed map_Forall_singleton //.
    + apply data_human_program_compile_scoped.
  - rewrite /data_human_program_compile map_fmap_singleton fmap_insert map_fmap_singleton /=.
    exists {["list_double" := "list_double_dps"]}; try set_solver.
    + intros * (<- & <-)%lookup_singleton_Some.
      rewrite lookup_insert.
      eexists. split; last done. repeat econstructor; done.
    + intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
      eexists. split; last done. repeat econstructor; done.
Qed.
