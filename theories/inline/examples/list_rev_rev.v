From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  refinement.
From camlcert.data_human_lang Require Export
  compile.
From camlcert.data_human_lang Require Import
  notations.
From camlcert.inline Require Import
  soundness.
Bind Scope data_human_def_scope with data_human_definition.

Definition list_rev_rev : data_human_program := {[
  "list_rev_append" :=
    rec: "arg" :=
      let: "xs" := ![𝟙] "arg" in
      let: "ys" := ![𝟚] "arg" in
      match: "xs" with
        NIL =>
          "ys"
      | CONS "x", "xs" =>
          $"list_rev_append" ("xs", CONSₕ "x" "ys")
      end ;
  "list_rev" :=
    rec: "xs" :=
      $"list_rev_append" ("xs", NILₕ) ;
  "list_rev_rev" :=
    rec: "xs" :=
      $"list_rev" ((DataHumanFunc "list_rev" ["inline"]) "xs")
]}%data_human_def.

Definition list_rev_rev_inline : data_human_program := {[
  "list_rev_append" :=
    rec: "arg" :=
      let: "xs" := ![𝟙] "arg" in
      let: "ys" := ![𝟚] "arg" in
      match: "xs" with
        NIL =>
          "ys"
      | CONS "x", "xs" =>
          $"list_rev_append" ("xs", CONSₕ "x" "ys")
      end ;
  "list_rev" :=
    rec: "xs" :=
      $"list_rev_append" ("xs", NILₕ) ;
  "list_rev_rev" :=
    rec: "xs" :=
      $"list_rev" (
        let: "arg" := "xs" in
        $"list_rev_append" ("arg", NILₕ)
      )
]}%data_human_def.

Lemma list_rev_rev_inline_sound :
  data_program_refinement
    (data_human_program_compile list_rev_rev)
    (data_human_program_compile list_rev_rev_inline).
Proof.
  rewrite /list_rev_rev /list_rev_rev_inline. apply inline_sound.
  - split.
    + apply data_human_program_compile_well_formed.
      rewrite /data_human_program_well_formed !map_Forall_insert //.
    + apply data_human_program_compile_scoped.
  - rewrite /data_human_program_compile !fmap_insert /=.
    split; first set_solver.
    intros *. rewrite !lookup_insert_Some. intros. simplify;
      eauto with inline.
Qed.
