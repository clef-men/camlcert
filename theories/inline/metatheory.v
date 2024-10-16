From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  metatheory.
From camlcert.inline Require Export
  definition.
From camlcert Require Import
  options.

Section inline_expr.
  Context (prog : data_program).

  Lemma inline_expr_refl e :
    inline_expr prog e e.
  Proof.
    induction e; auto with inline.
  Qed.

  Lemma inline_expr_subst ς eₛ eₛ' eₜ eₜ' :
    data_program_valid prog →
    inline_expr prog eₛ eₜ →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    inline_expr prog eₛ' eₜ'.
  Proof.
    intros (Hprog_wf & Hprog_scoped) Hinline.
    move: ς eₛ' eₜ'. induction Hinline; intros ς eₛ' eₜ' -> ->;
      eauto using inline_expr_refl with inline.
    eapply inline_expr_call_inline with (e_funcₛ := e_funcₛ.[up ς]); try naive_solver.
    erewrite (subst_data_program_scoped _ ids); asimpl; done.
  Qed.

  Lemma data_expr_scoped_inline_expr eₛ eₜ scope :
    data_program_scoped prog →
    inline_expr prog eₛ eₜ →
    data_expr_scoped scope eₛ →
    data_expr_scoped scope eₜ.
  Proof.
    intros Hprog_scoped Hinline.
    move: scope. induction Hinline; intros scope Hscoped;
      try naive_solver.
    split; first naive_solver.
    apply (data_expr_scoped_le 1); [lia | naive_solver].
  Qed.
End inline_expr.

#[global] Hint Resolve inline_expr_refl : inline.

Lemma data_program_scoped_inline progₛ progₜ :
  inline progₛ progₜ →
  data_program_scoped progₛ →
  data_program_scoped progₜ.
Proof.
  intros inline. rewrite /data_program_scoped !map_Forall_lookup => Hscoped func defₜ Hfuncₜ.
  apply elem_of_dom_2 in Hfuncₜ as Hfuncₜ'.
  rewrite inline.(inline_dom) in Hfuncₜ'. apply lookup_lookup_total_dom in Hfuncₜ'.
  edestruct inline.(inline_transform) as (eₜ & Hinline & Heq); first done.
  rewrite Heq in Hfuncₜ. eapply data_expr_scoped_inline_expr; naive_solver.
Qed.
