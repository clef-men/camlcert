From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  metatheory.
From camlcert.tmc_1 Require Export
  definition.
From camlcert Require Import
  options.

Section tmc_expr.
  Context (ξ : tmc_mapping).

  Lemma tmc_expr_dir_refl e :
    tmc_expr_dir ξ e e.
  Proof.
    induction e; auto with tmc.
  Qed.

  Lemma tmc_expr_subst :
    ( ∀ eₛ eₜ,
      tmc_expr_dir ξ eₛ eₜ →
      ∀ eₛ' eₜ' ς,
      eₛ' = eₛ.[ς] →
      eₜ' = eₜ.[ς] →
      tmc_expr_dir ξ eₛ' eₜ'
    ) ∧ (
      ∀ dst idx eₛ eₜ,
      tmc_expr_dps ξ dst idx eₛ eₜ →
      ∀ dst' idx' eₛ' eₜ' ς,
      dst' = dst.[ς] →
      idx' = idx.[ς] →
      eₛ' = eₛ.[ς] →
      eₜ' = eₜ.[ς] →
      tmc_expr_dps ξ dst' idx' eₛ' eₜ'
    ).
  Proof.
    apply tmc_expr_ind; solve
    [ intros; simplify;
      eauto using tmc_expr_dir_refl with tmc
    | intros * ? ? ? IHdps **; simplify;
      econstructor; try naive_solver; try apply IHdps with (up ς); autosubst
    | intros * ? IHdps1 ? IHdps2 **; simplify;
      econstructor;
      [ apply IHdps1 with (up ς); autosubst
      | apply IHdps2 with (up ς); autosubst
      | autosubst
      ]
    ].
  Qed.
  Lemma tmc_expr_dir_subst ς eₛ eₛ' eₜ eₜ' :
    tmc_expr_dir ξ eₛ eₜ →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    tmc_expr_dir ξ eₛ' eₜ'.
  Proof.
    eauto using (proj1 tmc_expr_subst).
  Qed.
  Lemma tmc_expr_dps_subst ς dst dst' idx idx' eₛ eₛ' eₜ eₜ' :
    tmc_expr_dps ξ dst idx eₛ eₜ →
    dst' = dst.[ς] →
    idx' = idx.[ς] →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    tmc_expr_dps ξ dst' idx' eₛ' eₜ'.
  Proof.
    eauto using (proj2 tmc_expr_subst).
  Qed.

  Lemma data_expr_scoped_tmc_expr :
    ( ∀ eₛ eₜ,
      tmc_expr_dir ξ eₛ eₜ →
      ∀ scope,
      data_expr_scoped scope eₛ →
      data_expr_scoped scope eₜ
    ) ∧ (
      ∀ dst idx eₛ eₜ,
      tmc_expr_dps ξ dst idx eₛ eₜ →
      ∀ scope,
      data_expr_scoped scope dst →
      data_expr_scoped scope idx →
      data_expr_scoped scope eₛ →
      data_expr_scoped scope eₜ
    ).
  Proof.
    apply tmc_expr_ind; try naive_solver.
    - intros * Hdir2 IH2 Hdps1 IH1 scope (Hscoped1 & Hscoped2).
      simpl. split_and!; try naive_solver lia.
      apply IH1; try naive_solver lia.
      apply data_expr_scoped_lift1. done.
    - intros * Hdir1 IH1 Hdps2 IH2 scope (Hscoped1 & Hscoped2).
      simpl. split_and!; try naive_solver lia.
      apply IH2; try naive_solver lia.
      apply data_expr_scoped_lift1. done.
    - intros * Hdps1 IH1 Hdps2 IH2 -> scope (Hscoped1 & Hscoped2).
      simpl. split_and!; try lia.
      + apply IH1; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1.
        apply IH2; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
    - intros * Hdps1 IH1 Hdps2 IH2 -> scope (Hscoped1 & Hscoped2).
      simpl. split_and!; try lia.
      + apply IH2; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1.
        apply IH1; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
    - intros * Hdir1 IH1 Hdps2 IH2 scope Hdst Hidx (Hscoped1 & Hscoped2).
      split; first auto.
      apply IH2; try done; apply data_expr_scoped_lift1; done.
    - intros * Hξ Hdir IH -> scope Hdst Hidx (_ & Hscoped).
      simpl. split_and!; [eauto using data_expr_scoped_lift1.. | lia].
    - intros * Hdir2 IH2 Hdps1 IH1 -> scope Hdst Hidx (Hscoped1 & Hscoped2).
      simpl. split_and!; try naive_solver lia.
      + apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
      + apply (data_expr_scoped_le (S (S scope))); first lia.
        apply data_expr_scoped_lift1, IH1; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
    - intros * Hdir1 IH1 Hdps2 IH2 -> scope Hdst Hidx (Hscoped1 & Hscoped2).
      simpl. split_and!; try naive_solver lia.
      + apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
      + apply (data_expr_scoped_le (S (S scope))); first lia.
        apply data_expr_scoped_lift1, IH2; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
    - intros * Hdps1 IH1 Hdps2 IH2 -> scope Hdst Hidx (Hscoped1 & Hscoped2).
      simpl. split_and!; try lia.
      + apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
      + apply (data_expr_scoped_le (S (S scope))); first lia.
        apply data_expr_scoped_lift1, IH1; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
      + asimpl.
        apply (data_expr_scoped_lift 2), IH2; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
    - intros * Hdps1 IH1 Hdps2 IH2 -> scope Hdst Hidx (Hscoped1 & Hscoped2).
      simpl. split_and!; try lia.
      + apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
      + apply (data_expr_scoped_le (S (S scope))); first lia.
        apply data_expr_scoped_lift1, IH2; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
      + asimpl.
        apply (data_expr_scoped_lift 2), IH1; try naive_solver lia.
        apply data_expr_scoped_lift1. done.
  Qed.
  Lemma data_expr_scoped_tmc_expr_dir scope eₛ eₜ :
    tmc_expr_dir ξ eₛ eₜ →
    data_expr_scoped scope eₛ →
    data_expr_scoped scope eₜ.
  Proof.
    eauto using (proj1 data_expr_scoped_tmc_expr).
  Qed.
  Lemma data_expr_scoped_tmc_expr_dps scope dst idx eₛ eₜ :
    tmc_expr_dps ξ dst idx eₛ eₜ →
    data_expr_scoped scope dst →
    data_expr_scoped scope idx →
    data_expr_scoped scope eₛ →
    data_expr_scoped scope eₜ.
  Proof.
    eauto using (proj2 data_expr_scoped_tmc_expr).
  Qed.
End tmc_expr.

#[global] Hint Resolve tmc_expr_dir_refl : tmc.

Lemma data_program_scoped_tmc progₛ progₜ :
  tmc progₛ progₜ →
  data_program_scoped progₛ →
  data_program_scoped progₜ.
Proof.
  intros tmc. rewrite /data_program_scoped !map_Forall_lookup. intros Hscoped func defₜ Hfuncₜ.
  apply elem_of_dom_2 in Hfuncₜ as Hfuncₜ'. rewrite tmc.(tmc_dom) elem_of_union in Hfuncₜ'.
  destruct Hfuncₜ' as [Hfuncₛ%lookup_lookup_total_dom | (func_dir & Hξ)%elem_of_map_img].
  - edestruct tmc.(tmc_dir) as (eₜ & Hdir & Heq); first done.
    eapply data_expr_scoped_tmc_expr_dir; last naive_solver.
    rewrite Heq in Hfuncₜ. naive_solver.
  - pose proof Hξ as Hfunc_dirₛ%elem_of_dom_2%(tmc.(tmc_ξ_dom))%lookup_lookup_total_dom.
    edestruct tmc.(tmc_dps) as (eₜ & Hdps & Heq); [done.. |].
    rewrite Hfuncₜ in Heq. simplify.
    repeat constructor. eapply data_expr_scoped_tmc_expr_dps; [naive_solver.. |].
    apply (data_expr_scoped_le 1); naive_solver lia.
Qed.
