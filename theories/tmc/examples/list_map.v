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

Definition list_map : data_human_program := {[
  "list_map" := (BNamed "arg", (
    let: "fn" := ![𝟙] "arg" in
    let: "xs" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
        NILₕ
    | CONS "x", "xs" =>
        let: "y" := DataHumanCall "fn" "x" in
        CONSₕ "y" ($"list_map" ("fn", "xs"))
    end
  )%data_human_expr)
]}.

Definition list_map_tmc : data_human_program := {[
  "list_map" := (BNamed "arg", (
    let: "fn" := ![𝟙] "arg" in
    let: "xs" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
        NILₕ
    | CONS "x", "xs" =>
        let: "y" := DataHumanCall "fn" "x" in
        let: "dst" := CONSₕ "y" #ₕ() in
        ( let: "arg" := ("fn", "xs") in
          $"list_map_dps" ("dst", 𝟚, "arg")
        ) ;;
        "dst"
    end
  )%data_human_expr) ;
  "list_map_dps" := (BNamed "arg", (
    let: "dst_idx" := ![𝟙] "arg" in
    let: "idx" := ![𝟚] "dst_idx" in
    let: "dst" := ![𝟙] "dst_idx" in
    let: "arg" := ![𝟚] "arg" in
    let: "fn" := ![𝟙] "arg" in
    let: "xs" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
        "dst" <-["idx"]- NILₕ
    | CONS "x", "xs" =>
        let: "y" := DataHumanCall "fn" "x" in
        let: "dst'" := CONSₕ "y" #ₕ() in
        "dst" <-["idx"]- "dst'" ;;
        let: "arg" := ("fn", "xs") in
        $"list_map_dps" ("dst'", 𝟚, "arg")
    end
  )%data_human_expr)
]}.

Lemma list_map_tmc_sound :
  data_program_refinement
    (data_human_program_compile list_map)
    (data_human_program_compile list_map_tmc).
Proof.
  rewrite /list_map /list_map_tmc. apply tmc_sound.
  - split.
    + apply data_human_program_compile_well_formed.
      rewrite /data_human_program_well_formed map_Forall_singleton //.
    + apply data_human_program_compile_scoped.
  - rewrite /data_human_program_compile map_fmap_singleton fmap_insert map_fmap_singleton /=.
    exists {["list_map" := "list_map_dps"]}; try set_solver.
    + intros * (<- & <-)%lookup_singleton_Some.
      rewrite lookup_insert.
      eexists. split; last done. repeat econstructor.
    + intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
      eexists. split; last done. repeat constructor.
      eapply tmc_dps_constr_1; first constructor.
      * eapply tmc_dps_call; repeat constructor.
      * done.
Qed.
