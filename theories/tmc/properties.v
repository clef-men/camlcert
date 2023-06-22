From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.language Require Export
  well_formed.
From simuliris.language Require Import
  notations.
From simuliris.tmc Require Export
  definition.

Lemma tmc_dir_refl ξ e :
  tmc_dir ξ e e.
Proof.
  induction e; eauto with tmc.
Qed.
#[export] Hint Resolve tmc_dir_refl : tmc.

Lemma tmc_subst ξ :
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
  [ intros; simplify; eauto with tmc
  | intros * ? ? ? IHdps **; simplify;
    econstructor; try naive_solver; try eapply IHdps with (up ς); autosubst
  ].
Qed.
Lemma tmc_dir_subst ξ ς eₛ eₛ' eₜ eₜ' :
  tmc_dir ξ eₛ eₜ →
  eₛ' = eₛ.[ς] →
  eₜ' = eₜ.[ς] →
  tmc_dir ξ eₛ' eₜ'.
Proof.
  eauto using (proj1 (tmc_subst ξ)).
Qed.
Lemma tmc_dps_subst ξ ς dst dst' idx idx' eₛ eₛ' eₜ eₜ' :
  tmc_dps ξ dst idx eₛ eₜ →
  dst' = dst.[ς] →
  idx' = idx.[ς] →
  eₛ' = eₛ.[ς] →
  eₜ' = eₜ.[ς] →
  tmc_dps ξ dst' idx' eₛ' eₜ'.
Proof.
  eauto using (proj2 (tmc_subst ξ)).
Qed.

Section well_formed.
  Context {progₛ progₜ} (tmc : tmc progₛ progₜ).

  Lemma expr_well_formed_tmc :
    ( ∀ eₛ eₜ,
      tmc_dir tmc.(tmc_ξ) eₛ eₜ →
      ∀ lvl,
      expr_well_formed progₛ lvl eₛ →
      expr_well_formed progₜ lvl eₜ
    ) ∧ (
      ∀ dst idx eₛ eₜ,
      tmc_dps tmc.(tmc_ξ) dst idx eₛ eₜ →
      ∀ lvl,
      expr_well_formed progₜ lvl dst →
      expr_well_formed progₜ lvl idx →
      expr_well_formed progₛ lvl eₛ →
      expr_well_formed progₜ lvl eₜ
    ).
  Proof.
    apply tmc_ind; try naive_solver.
    - intros []; try done. intros lvl Hfuncₛ.
      rewrite /= tmc.(tmc_dom). apply elem_of_union_l. done.
    - intros * Hdir1 IH1 Hdps2 IH2 lvl (Hwf1 & Hwf2).
      simpl. split_and!; try naive_solver lia.
      apply IH2; try naive_solver lia. apply expr_well_formed_lift1. done.
    - intros * Hdir2 IH2 Hdps1 IH1 lvl (Hwf1 & Hwf2).
      simpl. split_and!; try naive_solver lia.
      apply IH1; try naive_solver lia. apply expr_well_formed_lift1. done.
    - intros * Hdir1 IH1 Hdps2 IH2 lvl Hdst_wf Hidx_wf (Hwf1 & Hwf2).
      split; first auto. apply IH2; try done; apply expr_well_formed_lift1; done.
    - intros * Hξ Hdir IH -> lvl Hdst_wf Hidx_wf (Hfuncₛ%lookup_lookup_total_dom & Hwf).
      eapply (tmc.(tmc_dpss)) in Hfuncₛ as (eₜ' & Hfunc_dpsₜ & ?); last done.
      simpl. split_and!; try naive_solver lia.
      + eapply elem_of_dom_2. done.
      + apply expr_well_formed_lift1. done.
      + apply expr_well_formed_lift1. done.
    - intros * Hdir1 IH1 Hdps2 IH2 -> lvl Hdst_wf Hidx_wf (Hwf1 & Hwf2).
      simpl. split_and!; try naive_solver lia.
      + apply expr_well_formed_lift1. done.
      + apply expr_well_formed_lift1. done.
      + apply (expr_well_formed_le _ (S (S lvl))); first lia.
        apply expr_well_formed_lift1, IH2; try naive_solver lia.
        apply expr_well_formed_lift1. done.
    - intros * Hdir2 IH2 Hdps1 IH1 -> lvl Hdst_wf Hidx_wf (Hwf1 & Hwf2).
      simpl. split_and!; try naive_solver lia.
      + apply expr_well_formed_lift1. done.
      + apply expr_well_formed_lift1. done.
      + apply (expr_well_formed_le _ (S (S lvl))); first lia.
        apply expr_well_formed_lift1, IH1; try naive_solver lia.
        apply expr_well_formed_lift1. done.
  Qed.
  Lemma expr_well_formed_tmc_dir lvl eₛ eₜ :
    tmc_dir tmc.(tmc_ξ) eₛ eₜ →
    expr_well_formed progₛ lvl eₛ →
    expr_well_formed progₜ lvl eₜ.
  Proof.
    eauto using (proj1 (expr_well_formed_tmc)).
  Qed.
  Lemma expr_well_formed_tmc_dps lvl dst idx eₛ eₜ :
    tmc_dps tmc.(tmc_ξ) dst idx eₛ eₜ →
    expr_well_formed progₜ lvl dst →
    expr_well_formed progₜ lvl idx →
    expr_well_formed progₛ lvl eₛ →
    expr_well_formed progₜ lvl eₜ.
  Proof.
    eauto using (proj2 (expr_well_formed_tmc)).
  Qed.

  Lemma program_well_formed_tmc :
    program_well_formed progₛ →
    program_well_formed progₜ.
  Proof.
    rewrite /program_well_formed !map_Forall_lookup => Hwf func eₜ Hfuncₜ.
    apply elem_of_dom_2 in Hfuncₜ as Hfuncₜ'. rewrite tmc.(tmc_dom) elem_of_union in Hfuncₜ'.
    destruct Hfuncₜ' as [Hfuncₛ%lookup_lookup_total_dom | (func_dir & Hξ)%elem_of_map_img].
    - edestruct tmc.(tmc_dirs) as (_eₜ & Hdir & Heq); first done.
      eapply expr_well_formed_tmc_dir; last naive_solver.
      rewrite Heq in Hfuncₜ. naive_solver.
    - pose proof Hξ as Hfunc_dirₛ%elem_of_dom_2%(tmc.(tmc_ξ_dom))%lookup_lookup_total_dom.
      edestruct tmc.(tmc_dpss) as (eₜ' & Hdps & Heq); [done.. |].
      rewrite Hfuncₜ in Heq. injection Heq as ->.
      repeat constructor. eapply expr_well_formed_tmc_dps; [naive_solver.. |].
      apply (expr_well_formed_le _ 1); naive_solver lia.
  Qed.
End well_formed.
