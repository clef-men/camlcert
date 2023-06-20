From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
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
