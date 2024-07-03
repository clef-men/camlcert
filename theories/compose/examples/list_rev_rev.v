From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  refinement.
From camlcert.data_human_lang Require Export
  compile.
From camlcert.data_human_lang Require Import
  notations.
From camlcert.compose Require Import
  soundness.
From camlcert Require Import
  options.

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
      (* First call to [list_rev] has been inlined, see inline/examples/list_rev_rev. *)
      $"list_rev" ($"list_rev_append" ("xs", NILₕ))
]}%data_human_def.

Definition list_rev_rev_compose : data_human_program := {[
  "list_rev_list_rev_append" :=
    rec: "arg" :=
      let: "xs" := ![𝟙] "arg" in
      let: "ys" := ![𝟚] "arg" in
      match: "xs" with
        NIL =>
          $"list_rev" "ys"
      | CONS "x", "xs" =>
          $"list_rev_list_rev_append" ("xs", CONSₕ "x" "ys")
      end ;
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
      $"list_rev_list_rev_append" ("xs", NILₕ)
]}%data_human_def.

Lemma list_rev_rev_compose_sound :
  data_program_refinement
    (data_human_program_compile list_rev_rev)
    (data_human_program_compile list_rev_rev_compose).
Proof.
  rewrite /list_rev_rev /list_rev_rev_compose.
  eapply compose_sound with "list_rev_append" "list_rev".
  - split.
    + apply data_human_program_compile_well_formed.
      rewrite /data_human_program_well_formed !map_Forall_insert //.
    + apply data_human_program_compile_scoped.
  - rewrite /data_human_program_compile !fmap_insert /=.
    exists "list_rev_list_rev_append"; [set_solver.. | |].
    + intros *. rewrite !lookup_insert_Some. intros. simplify;
        eauto with compose.
    + repeat esplit. eauto 10 with compose.
Qed.
