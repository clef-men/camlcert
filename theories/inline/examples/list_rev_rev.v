From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  refinement.
From simuliris.data_human_lang Require Export
  compile.
From simuliris.data_human_lang Require Import
  notations.
From simuliris.inline Require Import
  soundness.

Definition list_rev_rev : data_human_program := {[
  "list_rev_append" :=
    {|data_human_definition_annot :=
        [] ;
      data_human_definition_param :=
        BNamed "arg" ;
      data_human_definition_body :=
        let: "xs" := ![𝟙] "arg" in
        let: "ys" := ![𝟚] "arg" in
        match: "xs" with
          NIL =>
            "ys"
        | CONS "x", "xs" =>
            $"list_rev_append" ("xs", CONSₕ "x" "ys")
        end
    |} ;
  "list_rev" :=
    {|data_human_definition_annot :=
        [] ;
      data_human_definition_param :=
        BNamed "xs" ;
      data_human_definition_body := (
        $"list_rev_append" ("xs", NILₕ)
      )%data_human_expr
    |} ;
  "list_rev_rev" :=
    {|data_human_definition_annot :=
        [] ;
      data_human_definition_param :=
        BNamed "xs" ;
      data_human_definition_body := (
        $"list_rev" ((DataHumanFunc "list_rev" ["inline"]) "xs")
      )%data_human_expr
    |}
]}.

Definition list_rev_rev_inline : data_human_program := {[
  "list_rev_append" :=
    {|data_human_definition_annot :=
        [] ;
      data_human_definition_param :=
        BNamed "arg" ;
      data_human_definition_body :=
        let: "xs" := ![𝟙] "arg" in
        let: "ys" := ![𝟚] "arg" in
        match: "xs" with
          NIL =>
            "ys"
        | CONS "x", "xs" =>
            $"list_rev_append" ("xs", CONSₕ "x" "ys")
        end
    |} ;
  "list_rev" :=
    {|data_human_definition_annot :=
        [] ;
      data_human_definition_param :=
        BNamed "xs" ;
      data_human_definition_body := (
        $"list_rev_append" ("xs", NILₕ)
      )%data_human_expr
    |} ;
  "list_rev_rev" :=
    {|data_human_definition_annot :=
        [] ;
      data_human_definition_param :=
        BNamed "xs" ;
      data_human_definition_body := (
        $"list_rev" (
          let: "arg" := "xs" in
          $"list_rev_append" ("arg", NILₕ)
        )
      )%data_human_expr
    |}
]}.

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
