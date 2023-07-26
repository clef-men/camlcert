From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.lambda_lang Require Export
  well_formed.
From simuliris.lambda_lang Require Import
  notations.
From simuliris.aps_plus Require Export
  definition.

Section aps_plus.
  Context (ξ : gmap lambda_function lambda_function).

  Lemma aps_plus_dir_refl e :
    aps_plus_dir ξ e e.
  Proof.
    induction e; eauto with aps_plus.
  Qed.

  Lemma aps_plus_subst :
    ( ∀ eₛ eₜ,
      aps_plus_dir ξ eₛ eₜ →
      ∀ eₛ' eₜ' ς,
      eₛ' = eₛ.[ς] →
      eₜ' = eₜ.[ς] →
      aps_plus_dir ξ eₛ' eₜ'
    ) ∧ (
      ∀ acc eₛ eₜ,
      aps_plus_aps ξ acc eₛ eₜ →
      ∀ acc' eₛ' eₜ' ς,
      acc' = acc.[ς] →
      eₛ' = eₛ.[ς] →
      eₜ' = eₜ.[ς] →
      aps_plus_aps ξ acc' eₛ' eₜ'
    ).
  Proof.
    apply aps_plus_ind; solve
    [ intros; simplify; eauto using aps_plus_dir_refl
    | intros * ? ? ? IHaps **; simplify;
      econstructor; try naive_solver; try eapply IHaps with (up ς); autosubst
    ].
  Qed.
  Lemma aps_plus_dir_subst ς eₛ eₛ' eₜ eₜ' :
    aps_plus_dir ξ eₛ eₜ →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    aps_plus_dir ξ eₛ' eₜ'.
  Proof.
    eauto using (proj1 aps_plus_subst).
  Qed.
  Lemma aps_plus_aps_subst ς acc acc' eₛ eₛ' eₜ eₜ' :
    aps_plus_aps ξ acc eₛ eₜ →
    acc' = acc.[ς] →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    aps_plus_aps ξ acc' eₛ' eₜ'.
  Proof.
    eauto using (proj2 aps_plus_subst).
  Qed.

  Lemma lambda_expr_scope_aps_plus :
    ( ∀ eₛ eₜ,
      aps_plus_dir ξ eₛ eₜ →
      ∀ scope,
      lambda_expr_scope scope eₛ →
      lambda_expr_scope scope eₜ
    ) ∧ (
      ∀ acc eₛ eₜ,
      aps_plus_aps ξ acc eₛ eₜ →
      ∀ scope,
      lambda_expr_scope scope acc →
      lambda_expr_scope scope eₛ →
      lambda_expr_scope scope eₜ
    ).
  Proof.
    apply aps_plus_ind; try naive_solver.
    - intros * Hdir1 IH1 Haps2 IH2 scope (Hscope1 & Hscope2).
      simpl. split_and!; try naive_solver lia.
      apply IH2; try naive_solver lia.
      apply lambda_expr_scope_lift1. done.
    - intros * Hdir2 IH2 Haps1 IH1 scope (Hscope1 & Hscope2).
      simpl. split_and!; try naive_solver lia.
      apply IH1; try naive_solver lia.
      apply lambda_expr_scope_lift1. done.
    - intros * Hdir1 IH1 Haps2 IH2 scope Hacc (Hscope1 & Hscope2).
      split; first auto.
      apply IH2; try done; apply lambda_expr_scope_lift1; done.
    - intros * Hξ Hdir IH -> scope Hacc (_ & Hwf).
      simpl. split_and!; [eauto using lambda_expr_scope_lift1.. | lia].
    - intros * Hdir1 IH1 Haps2 IH2 -> scope Hacc (Hwf1 & Hwf2).
      simpl. split_and!; try naive_solver lia.
      apply IH2.
      + split; first naive_solver lia.
        apply lambda_expr_scope_lift1. done.
      + apply lambda_expr_scope_lift1. done.
    - intros * Hdir2 IH2 Haps1 IH1 -> scope Hacc (Hwf1 & Hwf2).
      simpl. split_and!; try naive_solver lia.
      apply IH1.
      + split; first naive_solver lia.
        apply lambda_expr_scope_lift1. done.
      + apply lambda_expr_scope_lift1. done.
  Qed.
  Lemma lambda_expr_scope_aps_plus_dir scope eₛ eₜ :
    aps_plus_dir ξ eₛ eₜ →
    lambda_expr_scope scope eₛ →
    lambda_expr_scope scope eₜ.
  Proof.
    eauto using (proj1 lambda_expr_scope_aps_plus).
  Qed.
  Lemma lambda_expr_scope_aps_plus_aps scope acc eₛ eₜ :
    aps_plus_aps ξ acc eₛ eₜ →
    lambda_expr_scope scope acc →
    lambda_expr_scope scope eₛ →
    lambda_expr_scope scope eₜ.
  Proof.
    eauto using (proj2 lambda_expr_scope_aps_plus).
  Qed.
End aps_plus.

#[export] Hint Resolve aps_plus_dir_refl : aps_plus.

Lemma lambda_program_scope_aps_plus progₛ progₜ :
  aps_plus progₛ progₜ →
  lambda_program_scope progₛ →
  lambda_program_scope progₜ.
Proof.
  intros aps_plus. rewrite /lambda_program_scope !map_Forall_lookup => Hscope func eₜ Hfuncₜ.
  apply elem_of_dom_2 in Hfuncₜ as Hfuncₜ'. rewrite aps_plus.(aps_plus_dom) elem_of_union in Hfuncₜ'.
  destruct Hfuncₜ' as [Hfuncₛ%lookup_lookup_total_dom | (func_dir & Hξ)%elem_of_map_img].
  - edestruct aps_plus.(aps_plus_dirs) as (_eₜ & Hdir & Heq); first done.
    eapply lambda_expr_scope_aps_plus_dir; last naive_solver.
    rewrite Heq in Hfuncₜ. naive_solver.
  - pose proof Hξ as Hfunc_dirₛ%elem_of_dom_2%(aps_plus.(aps_plus_ξ_dom))%lookup_lookup_total_dom.
    edestruct aps_plus.(aps_plus_apss) as (eₜ' & Haps & Heq); [done.. |].
    rewrite Hfuncₜ in Heq. injection Heq as ->.
    repeat constructor. eapply lambda_expr_scope_aps_plus_aps; [naive_solver.. |].
    apply (lambda_expr_scope_le 1); naive_solver lia.
Qed.
