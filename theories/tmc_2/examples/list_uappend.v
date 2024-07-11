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

Definition list_uappend : data_human_program := {[
  "list_uappend" := rec: "arg" :=
    let: "xs" := ![𝟙] "arg" in
    let: "ys" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
        NILₕ
    | CONS "x1", "xs" =>
        match: "xs" with
          NIL =>
            CONSₕ "x1" NILₕ
        | CONS "x2", "xs" =>
            CONSₕ "x1" (CONSₕ "x2" ($"list_uappend" ("xs", "ys")))
        end
    end
]}%data_human_def.

Definition list_uappend_tmc : data_human_program := {[
  "list_uappend" := rec: "arg" :=
    let: "xs" := ![𝟙] "arg" in
    let: "ys" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
        NILₕ
    | CONS "x1", "xs" =>
        match: "xs" with
          NIL =>
            CONSₕ "x1" NILₕ
        | CONS "x2", "xs" =>
            let: "dst" := CONSₕ "x1" #ₕ() in
            ( let: "x2" := "x2" in
              let: "dst'" := CONSₕ "x2" #ₕ() in
              "dst" <-[𝟚] "dst'" ;;
              let: "arg" := ("xs", "ys") in
              $"list_uappend_dps" ("dst'", 𝟚, "arg")
            ) ;;
            "dst"
        end
    end ;
  "list_uappend_dps" := rec: "arg" :=
    let: "dst_idx" := ![𝟙] "arg" in
    let: "idx" := ![𝟚] "dst_idx" in
    let: "dst" := ![𝟙] "dst_idx" in
    let: "arg" := ![𝟚] "arg" in
    let: "xs" := ![𝟙] "arg" in
    let: "ys" := ![𝟚] "arg" in
    match: "xs" with
      NIL =>
        "dst" <-["idx"] NILₕ
    | CONS "x1", "xs" =>
        match: "xs" with
          NIL =>
            "dst" <-["idx"] CONSₕ "x1" NILₕ
        | CONS "x2", "xs" =>
            let: "x1" := "x1" in
            let: "x2" := "x2" in
            let: "dst'" := CONSₕ "x2" #ₕ() in
            "dst" <-["idx"] CONSₕ "x1" "dst'" ;;
            let: "arg" := ("xs", "ys") in
            $"list_uappend_dps" ("dst'", 𝟚, "arg")
        end
    end
]}%data_human_def.

Lemma list_uappend_tmc_sound :
  data_program_refinement
    (data_human_program_compile list_uappend)
    (data_human_program_compile list_uappend_tmc).
Proof.
  rewrite /list_uappend /list_uappend_tmc. apply tmc_sound.
  - split.
    + apply data_human_program_compile_well_formed.
      rewrite /data_human_program_well_formed map_Forall_singleton //.
    + apply data_human_program_compile_scoped.
  - rewrite /data_human_program_compile map_fmap_singleton fmap_insert map_fmap_singleton /=.
    exists {["list_uappend" := "list_uappend_dps"]}; try set_solver.
    + intros * (<- & <-)%lookup_singleton_Some.
      rewrite lookup_insert.
      eexists. split; last done. repeat econstructor; done.
    + intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
      eexists. split; last done. repeat econstructor; done.
Qed.
