From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  metatheory.
From camlcert.compose Require Export
  definition.
From camlcert Require Import
  options.

Section compose_expr.
  Context (func1 func2 func : data_function).

  Lemma compose_expr_dir_refl e :
    compose_expr_dir func1 func2 func e e.
  Proof.
    induction e; auto with compose.
  Qed.

  Lemma compose_expr_dir_subst ς eₛ eₛ' eₜ eₜ' :
    compose_expr_dir func1 func2 func eₛ eₜ →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    compose_expr_dir func1 func2 func eₛ' eₜ'.
  Proof.
    intros Hdir. move: ς eₛ' eₜ'. induction Hdir; intros ς eₛ' eₜ' -> ->;
      eauto using compose_expr_dir_refl with compose.
  Qed.
  Lemma compose_expr_comp_subst ς eₛ eₛ' eₜ eₜ' :
    compose_expr_comp func1 func2 func eₛ eₜ →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    compose_expr_comp func1 func2 func eₛ' eₜ'.
  Proof.
    intros Hcomp. move: ς eₛ' eₜ'. induction Hcomp; intros ς eₛ' eₜ' -> ->;
      eauto using compose_expr_dir_subst with compose.
  Qed.

  Lemma data_expr_scoped_compose_expr_dir scope eₛ eₜ :
    compose_expr_dir func1 func2 func eₛ eₜ →
    data_expr_scoped scope eₛ →
    data_expr_scoped scope eₜ.
  Proof.
    intros Hdir. move: scope. induction Hdir; intros scope;
      naive_solver.
  Qed.
  Lemma data_expr_scoped_compose_expr_comp scope eₛ eₜ :
    compose_expr_comp func1 func2 func eₛ eₜ →
    data_expr_scoped scope eₛ →
    data_expr_scoped scope eₜ.
  Proof.
    intros Hcomp. move: scope. induction Hcomp; intros scope;
      naive_solver eauto using data_expr_scoped_compose_expr_dir.
  Qed.
End compose_expr.

#[global] Hint Resolve compose_expr_dir_refl : compose.

Lemma data_program_scoped_compose func1 func2 progₛ progₜ :
  compose func1 func2 progₛ progₜ →
  data_program_scoped progₛ →
  data_program_scoped progₜ.
Proof.
  intros compose. rewrite /data_program_scoped !map_Forall_lookup => Hscoped func defₜ Hfuncₜ.
  apply elem_of_dom_2 in Hfuncₜ as Hfuncₜ'. rewrite compose.(compose_dom) elem_of_union in Hfuncₜ'.
  destruct Hfuncₜ' as [->%elem_of_singleton | Hfuncₛ%lookup_lookup_total_dom].
  - edestruct compose.(compose_comp) as (defₛ & eₜ & Hfunc1ₛ & Hcomp & Heq).
    rewrite Hfuncₜ in Heq. simplify.
    eapply data_expr_scoped_compose_expr_comp; naive_solver.
  - edestruct compose.(compose_dir) as (eₜ & Hdir & Heq); first done.
    eapply data_expr_scoped_compose_expr_dir; last naive_solver.
    rewrite Heq in Hfuncₜ. naive_solver.
Qed.
