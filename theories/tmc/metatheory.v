From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.data_lang Require Export
  metatheory.
From simuliris.data_lang Require Import
  notations.
From simuliris.tmc Require Export
  definition.

Section tmc.
  Context (ξ : gmap data_function data_function).

  Lemma tmc_dir_refl e :
    tmc_dir ξ e e.
  Proof.
    induction e; eauto with tmc.
  Qed.

  Lemma tmc_subst :
    ( ∀ eₛ eₜ,
      tmc_dir ξ eₛ eₜ →
      ∀ eₛ' eₜ' ς,
      eₛ' = eₛ.[ς] →
      eₜ' = eₜ.[ς] →
      tmc_dir ξ eₛ' eₜ'
    ) ∧ (
      ∀ dst idx eₛ eₜ,
      tmc_dps ξ dst idx eₛ eₜ →
      ∀ dst' idx' eₛ' eₜ' ς,
      dst' = dst.[ς] →
      idx' = idx.[ς] →
      eₛ' = eₛ.[ς] →
      eₜ' = eₜ.[ς] →
      tmc_dps ξ dst' idx' eₛ' eₜ'
    ).
  Proof.
    apply tmc_ind; solve
    [ intros; simplify;
      auto using tmc_dir_refl
    | intros * ? ? ? IHdps **; simplify;
      econstructor; try naive_solver; try apply IHdps with (up ς); autosubst
    ].
  Qed.
  Lemma tmc_dir_subst ς eₛ eₛ' eₜ eₜ' :
    tmc_dir ξ eₛ eₜ →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    tmc_dir ξ eₛ' eₜ'.
  Proof.
    eauto using (proj1 tmc_subst).
  Qed.
  Lemma tmc_dps_subst ς dst dst' idx idx' eₛ eₛ' eₜ eₜ' :
    tmc_dps ξ dst idx eₛ eₜ →
    dst' = dst.[ς] →
    idx' = idx.[ς] →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    tmc_dps ξ dst' idx' eₛ' eₜ'.
  Proof.
    eauto using (proj2 tmc_subst).
  Qed.

  Lemma data_expr_scope_tmc :
    ( ∀ eₛ eₜ,
      tmc_dir ξ eₛ eₜ →
      ∀ scope,
      data_expr_scope scope eₛ →
      data_expr_scope scope eₜ
    ) ∧ (
      ∀ dst idx eₛ eₜ,
      tmc_dps ξ dst idx eₛ eₜ →
      ∀ scope,
      data_expr_scope scope dst →
      data_expr_scope scope idx →
      data_expr_scope scope eₛ →
      data_expr_scope scope eₜ
    ).
  Proof.
    apply tmc_ind; try naive_solver.
    - intros * Hdir1 IH1 Hdps2 IH2 scope (Hscope1 & Hscope2).
      simpl. split_and!; try naive_solver lia.
      apply IH2; try naive_solver lia.
      apply data_expr_scope_lift1. done.
    - intros * Hdir2 IH2 Hdps1 IH1 scope (Hscope1 & Hscope2).
      simpl. split_and!; try naive_solver lia.
      apply IH1; try naive_solver lia.
      apply data_expr_scope_lift1. done.
    - intros * Hdir1 IH1 Hdps2 IH2 scope Hdst Hidx (Hscope1 & Hscope2).
      split; first auto.
      apply IH2; try done; apply data_expr_scope_lift1; done.
    - intros * Hξ Hdir IH -> scope Hdst Hidx (_ & Hscope).
      simpl. split_and!; [eauto using data_expr_scope_lift1.. | lia].
    - intros * Hdir1 IH1 Hdps2 IH2 -> scope Hdst Hidx (Hscope1 & Hscope2).
      simpl. split_and!; try naive_solver lia.
      + apply data_expr_scope_lift1. done.
      + apply data_expr_scope_lift1. done.
      + apply (data_expr_scope_le (S (S scope))); first lia.
        apply data_expr_scope_lift1, IH2; try naive_solver lia.
        apply data_expr_scope_lift1. done.
    - intros * Hdir2 IH2 Hdps1 IH1 -> scope Hdst Hidx (Hscope1 & Hscope2).
      simpl. split_and!; try naive_solver lia.
      + apply data_expr_scope_lift1. done.
      + apply data_expr_scope_lift1. done.
      + apply (data_expr_scope_le (S (S scope))); first lia.
        apply data_expr_scope_lift1, IH1; try naive_solver lia.
        apply data_expr_scope_lift1. done.
  Qed.
  Lemma data_expr_scope_tmc_dir scope eₛ eₜ :
    tmc_dir ξ eₛ eₜ →
    data_expr_scope scope eₛ →
    data_expr_scope scope eₜ.
  Proof.
    eauto using (proj1 data_expr_scope_tmc).
  Qed.
  Lemma data_expr_scope_tmc_dps scope dst idx eₛ eₜ :
    tmc_dps ξ dst idx eₛ eₜ →
    data_expr_scope scope dst →
    data_expr_scope scope idx →
    data_expr_scope scope eₛ →
    data_expr_scope scope eₜ.
  Proof.
    eauto using (proj2 data_expr_scope_tmc).
  Qed.
End tmc.

#[export] Hint Resolve tmc_dir_refl : tmc.

Lemma data_program_scope_tmc progₛ progₜ :
  tmc progₛ progₜ →
  data_program_scope progₛ →
  data_program_scope progₜ.
Proof.
  intros tmc. rewrite /data_program_scope !map_Forall_lookup => Hscope func eₜ Hfuncₜ.
  apply elem_of_dom_2 in Hfuncₜ as Hfuncₜ'. rewrite tmc.(tmc_dom) elem_of_union in Hfuncₜ'.
  destruct Hfuncₜ' as [Hfuncₛ%lookup_lookup_total_dom | (func_dir & Hξ)%elem_of_map_img].
  - edestruct tmc.(tmc_dirs) as (_eₜ & Hdir & Heq); first done.
    eapply data_expr_scope_tmc_dir; last naive_solver.
    rewrite Heq in Hfuncₜ. naive_solver.
  - pose proof Hξ as Hfunc_dirₛ%elem_of_dom_2%(tmc.(tmc_ξ_dom))%lookup_lookup_total_dom.
    edestruct tmc.(tmc_dpss) as (eₜ' & Hdps & Heq); [done.. |].
    rewrite Hfuncₜ in Heq. injection Heq as ->.
    repeat constructor. eapply data_expr_scope_tmc_dps; [naive_solver.. |].
    apply (data_expr_scope_le 1); naive_solver lia.
Qed.
