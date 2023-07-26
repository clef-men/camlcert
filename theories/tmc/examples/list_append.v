From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  refinement.
From simuliris.data_human_lang Require Export
  compilation.
From simuliris.data_human_lang Require Import
  notations.
From simuliris.tmc Require Import
  soundness.

Definition list_append : data_human_program := {[
  "list_append" := (BNamed "arg", (
    let: "xs" := ![𝟙] "arg" in
    let: "ys" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
        NILₕ
    | CONS "x", "xs" =>
        CONSₕ "x" ($"list_append" ("xs", "ys"))
    end
  )%data_human_expr)
]}.

Definition list_append_tmc : data_human_program := {[
  "list_append" := (BNamed "arg", (
    let: "xs" := ![𝟙] "arg" in
    let: "ys" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
        NILₕ
    | CONS "x", "xs" =>
        let: "dst" := CONSₕ "x" #ₕ() in
        ( let: "arg" := ("xs", "ys") in
          $"list_append_dps" ("dst", 𝟚, "arg")
        ) ;;
        "dst"
    end
  )%data_human_expr) ;
  "list_append_dps" := (BNamed "arg", (
    let: "dst_idx" := ![𝟙] "arg" in
    let: "idx" := ![𝟚] "dst_idx" in
    let: "dst" := ![𝟙] "dst_idx" in
    let: "arg" := ![𝟚] "arg" in
    let: "xs" := ![𝟙] "arg" in
    let: "ys" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
      "dst" <-["idx"]- NILₕ
    | CONS "x", "xs" =>
        let: "dst'" := CONSₕ "x" #ₕ() in
        "dst" <-["idx"]- "dst'" ;;
        let: "arg" := ("xs", "ys") in
        $"list_append_dps" ("dst'", 𝟚, "arg")
    end
  )%data_human_expr)
]}.

Lemma list_append_tmc_sound :
  data_program_refinement
    (data_human_program_compile list_append)
    (data_human_program_compile list_append_tmc).
Proof.
  rewrite /list_append /list_append_tmc. apply tmc_sound.
  - split.
    + apply data_human_program_compile_well_formed.
      rewrite /data_human_program_well_formed map_Forall_singleton //.
    + apply data_human_program_compile_scope.
  - rewrite /data_human_program_compile map_fmap_singleton fmap_insert map_fmap_singleton /=.
    exists {["list_append" := "list_append_dps"]}; try set_solver.
    + intros * (<- & <-)%lookup_singleton_Some.
      rewrite lookup_insert.
      eexists. split; last done. repeat econstructor.
    + intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
      eexists. split; last done.
      repeat constructor. eapply tmc_dps_constr_1; first constructor.
      * eapply tmc_dps_call; repeat constructor.
      * done.
Qed.
