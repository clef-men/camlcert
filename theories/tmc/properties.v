From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.tmc_lang Require Export
  well_formed.
From simuliris.tmc_lang Require Import
  notations.
From simuliris.tmc Require Export
  definition.

Section tmc.
  Context (ξ : gmap function function).

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
    [ intros; simplify; eauto using tmc_dir_refl
    | intros * ? ? ? IHdps **; simplify;
      econstructor; try naive_solver; try eapply IHdps with (up ς); autosubst
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

  Lemma expr_closed_tmc :
    ( ∀ eₛ eₜ,
      tmc_dir ξ eₛ eₜ →
      ∀ lvl,
      expr_closed lvl eₛ →
      expr_closed lvl eₜ
    ) ∧ (
      ∀ dst idx eₛ eₜ,
      tmc_dps ξ dst idx eₛ eₜ →
      ∀ lvl,
      expr_closed lvl dst →
      expr_closed lvl idx →
      expr_closed lvl eₛ →
      expr_closed lvl eₜ
    ).
  Proof.
    apply tmc_ind; try naive_solver.
    - intros * Hdir1 IH1 Hdps2 IH2 lvl (Hclosed1 & Hclosed2).
      simpl. split_and!; try naive_solver lia.
      apply IH2; try naive_solver lia. apply expr_closed_lift1. done.
    - intros * Hdir2 IH2 Hdps1 IH1 lvl (Hclosed1 & Hclosed2).
      simpl. split_and!; try naive_solver lia.
      apply IH1; try naive_solver lia. apply expr_closed_lift1. done.
    - intros * Hdir1 IH1 Hdps2 IH2 lvl Hdst Hidx (Hclosed1 & Hclosed2).
      split; first auto. apply IH2; try done; apply expr_closed_lift1; done.
    - intros * Hξ Hdir IH -> lvl Hdst Hidx (_ & Hwf).
      simpl. split_and!; [eauto using expr_closed_lift1.. | lia].
    - intros * Hdir1 IH1 Hdps2 IH2 -> lvl Hdst Hidx (Hwf1 & Hwf2).
      simpl. split_and!; try naive_solver lia.
      + apply expr_closed_lift1. done.
      + apply expr_closed_lift1. done.
      + apply (expr_closed_le (S (S lvl))); first lia.
        apply expr_closed_lift1, IH2; try naive_solver lia.
        apply expr_closed_lift1. done.
    - intros * Hdir2 IH2 Hdps1 IH1 -> lvl Hdst Hidx (Hwf1 & Hwf2).
      simpl. split_and!; try naive_solver lia.
      + apply expr_closed_lift1. done.
      + apply expr_closed_lift1. done.
      + apply (expr_closed_le (S (S lvl))); first lia.
        apply expr_closed_lift1, IH1; try naive_solver lia.
        apply expr_closed_lift1. done.
  Qed.
  Lemma expr_closed_tmc_dir lvl eₛ eₜ :
    tmc_dir ξ eₛ eₜ →
    expr_closed lvl eₛ →
    expr_closed lvl eₜ.
  Proof.
    eauto using (proj1 expr_closed_tmc).
  Qed.
  Lemma expr_closed_tmc_dps lvl dst idx eₛ eₜ :
    tmc_dps ξ dst idx eₛ eₜ →
    expr_closed lvl dst →
    expr_closed lvl idx →
    expr_closed lvl eₛ →
    expr_closed lvl eₜ.
  Proof.
    eauto using (proj2 expr_closed_tmc).
  Qed.
End tmc.

#[export] Hint Resolve tmc_dir_refl : tmc.

Lemma program_closed_tmc progₛ progₜ :
  tmc progₛ progₜ →
  program_closed progₛ →
  program_closed progₜ.
Proof.
  intros tmc. rewrite /program_closed !map_Forall_lookup => Hclosed func eₜ Hfuncₜ.
  apply elem_of_dom_2 in Hfuncₜ as Hfuncₜ'. rewrite tmc.(tmc_dom) elem_of_union in Hfuncₜ'.
  destruct Hfuncₜ' as [Hfuncₛ%lookup_lookup_total_dom | (func_dir & Hξ)%elem_of_map_img].
  - edestruct tmc.(tmc_dirs) as (_eₜ & Hdir & Heq); first done.
    eapply expr_closed_tmc_dir; last naive_solver.
    rewrite Heq in Hfuncₜ. naive_solver.
  - pose proof Hξ as Hfunc_dirₛ%elem_of_dom_2%(tmc.(tmc_ξ_dom))%lookup_lookup_total_dom.
    edestruct tmc.(tmc_dpss) as (eₜ' & Hdps & Heq); [done.. |].
    rewrite Hfuncₜ in Heq. injection Heq as ->.
    repeat constructor. eapply expr_closed_tmc_dps; [naive_solver.. |].
    apply (expr_closed_le 1); naive_solver lia.
Qed.
