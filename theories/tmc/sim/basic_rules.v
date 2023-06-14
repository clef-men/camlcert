From simuliris Require Import
  prelude.
From simuliris.base_logic Require Import
  lib.cupd.proofmode.
From simuliris.program_logic Require Export
  sim.rules.
From simuliris.language Require Export
  tactics.
From simuliris.tmc Require Export
  sim.definition.
From simuliris.tmc Require Import
  sim.notations.

Section sim_GS.
  Context `{sim_GS : !SimGS Σ}.
  Implicit Types constr : constructor.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types e eₛ eₜ : expr.
  Implicit Types v vₛ vₜ w : val.

  Lemma sim_state_interp_allocₛ l v σₛ σₜ :
    σₛ !! l = None →
    sim_state_interp σₛ σₜ ==∗
      sim_state_interp (<[l := v]> σₛ) σₜ ∗
      l ↦ₛ v ∗
      meta_tokenₛ l ⊤.
  Proof.
    iIntros "% (Hheapₛ & Hheapₜ & Hbij)".
    iMod (sim_heap_allocₛ with "Hheapₛ") as "(Hheapₛ & $)"; first done.
    iFrame. done.
  Qed.
  Lemma sim_state_interp_allocₜ l v σₛ σₜ :
    σₜ !! l = None →
    sim_state_interp σₛ σₜ ==∗
      sim_state_interp σₛ (<[l := v]> σₜ) ∗
      l ↦ₜ v ∗
      meta_tokenₜ l ⊤.
  Proof.
    iIntros "% (Hheapₛ & Hheapₜ & Hbij)".
    iMod (sim_heap_allocₜ with "Hheapₜ") as "(Hheapₜ & $)"; first done.
    iFrame. done.
  Qed.

  Lemma sim_state_interp_alloc_bigₛ σₛ' σₛ σₜ :
    σₛ' ##ₘ σₛ →
    sim_state_interp σₛ σₜ ==∗
      sim_state_interp (σₛ' ∪ σₛ) σₜ ∗
      ([∗ map] l ↦ v ∈ σₛ', l ↦ₛ v) ∗
      ([∗ map] l ↦ _ ∈ σₛ', meta_tokenₛ l ⊤).
  Proof.
    iIntros "% (Hheapₛ & Hheapₜ & Hbij)".
    iMod (sim_heap_alloc_bigₛ with "Hheapₛ") as "(Hheapₛ & $)"; first done.
    iFrame. done.
  Qed.
  Lemma sim_state_interp_alloc_bigₜ σₜ' σₛ σₜ :
    σₜ' ##ₘ σₜ →
    sim_state_interp σₛ σₜ ==∗
      sim_state_interp σₛ (σₜ' ∪ σₜ) ∗
      ([∗ map] l ↦ v ∈ σₜ', l ↦ₜ v) ∗
      ([∗ map] l ↦ _ ∈ σₜ', meta_tokenₜ l ⊤).
  Proof.
    iIntros "% (Hheapₛ & Hheapₜ & Hbij)".
    iMod (sim_heap_alloc_bigₜ with "Hheapₜ") as "(Hheapₜ & $)"; first done.
    iFrame. done.
  Qed.

  Lemma sim_state_interp_validₛ l dq v σₛ σₜ :
    sim_state_interp σₛ σₜ -∗
    l ↦ₛ{dq} v -∗
    ⌜σₛ !! l = Some v⌝.
  Proof.
    iIntros "(Hheapₛ & Hheapₜ & Hbij) Hl".
    iApply (sim_heap_validₛ with "Hheapₛ Hl").
  Qed.
  Lemma sim_state_interp_validₜ l dq v σₛ σₜ :
    sim_state_interp σₛ σₜ -∗
    l ↦ₜ{dq} v -∗
    ⌜σₜ !! l = Some v⌝.
  Proof.
    iIntros "(Hheapₛ & Hheapₜ & Hbij) Hl".
    iApply (sim_heap_validₜ with "Hheapₜ Hl").
  Qed.

  Lemma sim_state_interp_updateₛ {l} v w σₛ σₜ :
    sim_state_interp σₛ σₜ -∗
    l ↦ₛ w ==∗
      sim_state_interp (<[l := v]> σₛ) σₜ ∗
      l ↦ₛ v.
  Proof.
    iIntros "(Hheapₛ & Hheapₜ & Hbij) Hl".
    iMod (sim_heap_updateₛ with "Hheapₛ Hl") as "(Hheapₛ & $)".
    iFrame. done.
  Qed.
  Lemma sim_state_interp_updateₜ {l} v w σₛ σₜ :
    sim_state_interp σₛ σₜ -∗
    l ↦ₜ w ==∗
      sim_state_interp σₛ (<[l := v]> σₜ) ∗
      l ↦ₜ v.
  Proof.
    iIntros "(Hheapₛ & Hheapₜ & Hbij) Hl".
    iMod (sim_heap_updateₜ with "Hheapₜ Hl") as "(Hheapₜ & $)".
    iFrame. done.
  Qed.

  Lemma sim_state_interp_heap_bij_valid σₛ lₛ σₜ lₜ :
    sim_state_interp σₛ σₜ -∗
    lₛ ≈ lₜ -∗
      ∃ vₛ vₜ,
      ⌜σₛ !! lₛ = Some vₛ ∧ σₜ !! lₜ = Some vₜ⌝ ∗
      vₛ ≈ vₜ.
  Proof.
    iIntros "(Hheapₛ & Hheapₜ & Hbij) Hl".
    iDestruct (sim_heap_bij_access with "Hbij Hl") as "(Htie & _)".
    iDestruct (sim_heap_bij_tie_eq_1 with "Htie") as "(%vₛ & %vₜ & Hlₛ & Hlₜ & Hl)".
    iDestruct (sim_heap_validₛ with "Hheapₛ Hlₛ") as %?.
    iDestruct (sim_heap_validₜ with "Hheapₜ Hlₜ") as %?.
    auto.
  Qed.

  Lemma sim_state_interp_heap_bij_access σₛ lₛ σₜ lₜ :
    sim_state_interp σₛ σₜ -∗
    lₛ ≈ lₜ -∗
      lₛ ⟷ lₜ ∗
      (lₛ ⟷ lₜ -∗ sim_state_interp σₛ σₜ).
  Proof.
    iIntros "(Hheapₛ & Hheapₜ & Hbij) Hl".
    iDestruct (sim_heap_bij_access with "Hbij Hl") as "(Hl & Hbij)".
    iFrame. done.
  Qed.

  Lemma sim_state_interp_heap_bij_insert lₛ lₜ :
    lₛ ⟷ lₜ ++∗
    lₛ ≈ lₜ.
  Proof.
    rewrite sim_cupd_eq.
    iIntros "Hl %σₛ %σₜ (Hheapₛ & Hheapₜ & Hbij)".
    iMod (sim_heap_bij_insert with "Hbij Hl") as "(Hbij & Hl)".
    iFrame. done.
  Qed.

  Lemma sim_state_interp_heap_bij_update σₛ lₛ vₛ σₜ lₜ vₜ :
    sim_state_interp σₛ σₜ -∗
    lₛ ≈ lₜ -∗
    vₛ ≈ vₜ ==∗
    sim_state_interp (<[lₛ := vₛ]> σₛ) (<[lₜ := vₜ]> σₜ).
  Proof.
    iIntros "(Hheapₛ & Hheapₜ & Hbij) Hl Hv".
    iDestruct (sim_heap_bij_access with "Hbij Hl") as "(Hl & Hbij)".
    iDestruct (sim_heap_bij_tie_eq_1 with "Hl") as "(%vₛ' & %vₜ' & Hlₛ & Hlₜ & Hv')".
    iMod (sim_heap_updateₛ with "Hheapₛ Hlₛ") as "(Hheapₛ & Hlₛ)".
    iMod (sim_heap_updateₜ with "Hheapₜ Hlₜ") as "(Hheapₜ & Hlₜ)".
    iFrame. iApply "Hbij". iExists vₛ, vₜ. iFrame. done.
  Qed.

  Context (progₛ progₜ : program).
  Context (X : sim_protocol Σ).

  Lemma sim_constr_detₛ constr v1 v2 e Φ :
    ( ∀ l,
      l ↦ₛ constr -∗
      (l +ₗ 1) ↦ₛ v1 -∗
      (l +ₗ 2) ↦ₛ v2 -∗
      SIM progₛ; l ≳ progₜ; e [[ X ]] {{ Φ }}
    ) -∗
    SIM progₛ; &&constr v1 v2 ≳ progₜ; e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi".
    set l := loc_fresh (dom σₛ).
    set (σₛ' := {[l +ₗ 2 := v2 ; l +ₗ 1 := v1 ; l +ₗ 0 := Int (Z.of_nat constr)]} : state).
    iMod (sim_state_interp_alloc_bigₛ σₛ' with "Hsi") as "(Hsi & Hmapstos & _)".
    { rewrite !map_disjoint_insert_l -!not_elem_of_dom. split_and!;
      [ apply loc_fresh_fresh; done..
      | apply map_disjoint_empty_l
      ].
    }
    iDestruct (big_sepM_insert with "Hmapstos") as "(Hl2 & Hmapstos)".
    { do 2 (rewrite lookup_insert_ne; last by intros ?%(inj _)). done. }
    iDestruct (big_sepM_insert with "Hmapstos") as "(Hl1 & Hl)".
    { rewrite lookup_insert_ne; last by intros ?%(inj _). done. }
    rewrite big_sepM_singleton loc_add_0.
    iExists #l, (σₛ' ∪ σₛ). iFrame. iSplitR.
    { iPureIntro. apply head_step_constr_det'.
      rewrite -!insert_union_l loc_add_0 left_id //.
    }
    iApply ("Hsim" with "Hl Hl1 Hl2").
  Qed.
  Lemma sim_constr_detₜ e constr v1 v2 Φ :
    ( ∀ l,
      l ↦ₜ constr -∗
      (l +ₗ 1) ↦ₜ v1 -∗
      (l +ₗ 2) ↦ₜ v2 -∗
      SIM progₛ; e ≳ progₜ; l [[ X ]] {{ Φ }}
    ) -∗
    SIM progₛ; e ≳ progₜ; &&constr v1 v2 [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₜ. iIntros "%σₛ %σₜ Hsi".
    iSplitR; first auto with language. iIntros "!> %eₜ' %σₜ'' %Hstepₜ".
    invert_head_step.
    set (σₜ' := {[l +ₗ 2 := v2 ; l +ₗ 1 := v1 ; l +ₗ 0 := Int (Z.of_nat constr)]} : state).
    iMod (sim_state_interp_alloc_bigₜ σₜ' with "Hsi") as "(Hsi & Hmapstos & _)".
    { rewrite !map_disjoint_insert_l loc_add_0. naive_solver apply map_disjoint_empty_l. }
    iDestruct (big_sepM_insert with "Hmapstos") as "(Hl2 & Hmapstos)".
    { do 2 (rewrite lookup_insert_ne; last by intros ?%(inj _)). done. }
    iDestruct (big_sepM_insert with "Hmapstos") as "(Hl1 & Hl)".
    { rewrite lookup_insert_ne; last by intros ?%(inj _). done. }
    rewrite big_sepM_singleton loc_add_0.
    rewrite -!insert_union_l loc_add_0 left_id. iFrame.
    iApply ("Hsim" with "Hl Hl1 Hl2").
  Qed.
  Lemma sim_constr_det constr vₛ1 vₛ2 vₜ1 vₜ2 Φ :
    vₛ1 ≈ vₜ1 -∗
    vₛ2 ≈ vₜ2 -∗
    ( ∀ lₛ lₜ,
      lₛ ≈ lₜ -∗
      (lₛ +ₗ 1) ≈ (lₜ +ₗ 1) -∗
      (lₛ +ₗ 2) ≈ (lₜ +ₗ 2) ++∗
      Φ #lₛ #lₜ
    ) -∗
    SIM progₛ; &&constr vₛ1 vₛ2 ≳ progₜ; &&constr vₜ1 vₜ2 [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hv1 Hv2 HΦ".
    iApply sim_constr_detₛ. iIntros "%lₛ Hlₛ Hlₛ1 Hlₛ2".
    iApply sim_constr_detₜ. iIntros "%lₜ Hlₜ Hlₜ1 Hlₜ2".
    iApply cupd_sim.
    iMod (sim_state_interp_heap_bij_insert with "[Hlₛ Hlₜ]") as "Hl".
    { iExists constr, constr. auto with iFrame. }
    iMod (sim_state_interp_heap_bij_insert with "[Hlₛ1 Hlₜ1 Hv1]") as "Hl1".
    { iExists vₛ1, vₜ1. auto with iFrame. }
    iMod (sim_state_interp_heap_bij_insert with "[Hlₛ2 Hlₜ2 Hv2]") as "Hl2".
    { iExists vₛ2, vₜ2. auto with iFrame. }
    iMod ("HΦ" with "Hl Hl1 Hl2") as "HΦ".
    iApply (sim_post with "HΦ"); done.
  Qed.

  Lemma sim_constrₛ1 constr e1 e2 e Φ :
    SIM progₛ; let: e1 in let: e2.[ren (+1)] in &&constr $1 $0 ≳ progₜ; e [[ X ]] {{ Φ }} -∗
    SIM progₛ; &constr e1 e2 ≳ progₜ; e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
    iExists _, σₛ. iFrame. auto with language.
  Qed.
  Lemma sim_constrₛ2 constr e1 e2 e Φ :
    SIM progₛ; let: e2 in let: e1.[ren (+1)] in &&constr $0 $1 ≳ progₜ; e [[ X ]] {{ Φ }} -∗
    SIM progₛ; &constr e1 e2 ≳ progₜ; e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
    iExists _, σₛ. iFrame. auto with language.
  Qed.
  Lemma sim_constrₜ constr e e1 e2 Φ :
      SIM progₛ; e ≳ progₜ; let: e1 in let: e2.[ren (+1)] in &&constr $1 $0 [[ X ]] {{ Φ }}
    ∧ SIM progₛ; e ≳ progₜ; let: e2 in let: e1.[ren (+1)] in &&constr $0 $1 [[ X ]] {{ Φ }}
    -∗
    SIM progₛ; e ≳ progₜ; &constr e1 e2 [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
    iSplit; first auto with language. iIntros "%eₜ' %σₜ' %Hstepₜ".
    invert_head_step; iFrame.
    - iDestruct "Hsim" as "($ & _)". done.
    - iDestruct "Hsim" as "(_ & $)". done.
  Qed.

  Lemma sim_loadₛ l v e Φ :
    l ↦ₛ v -∗
    ( l ↦ₛ v -∗
      SIM progₛ; v ≳ progₜ; e [[ X ]] {{ Φ }}
    ) -∗
    SIM progₛ; !l ≳ progₜ; e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hl Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
    iDestruct (sim_state_interp_validₛ with "Hsi Hl") as %?.
    iExists #v, σₛ. iSplit; first auto with language. iFrame.
    iApply ("Hsim" with "Hl").
  Qed.
  Lemma sim_loadₜ e l v Φ :
    l ↦ₜ v -∗
    ( l ↦ₜ v -∗
      SIM progₛ; e ≳ progₜ; v [[ X ]] {{ Φ }}
    ) -∗
    SIM progₛ; e ≳ progₜ; !l [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hl Hsim".
    iApply sim_head_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
    iDestruct (sim_state_interp_validₜ with "Hsi Hl") as %?.
    iSplit; first auto with language. iIntros "%eₜ' %σₜ' %Hstepₜ !>".
    invert_head_step. iFrame.
    iApply ("Hsim" with "Hl").
  Qed.
  Lemma sim_load lₛ lₜ Φ :
    lₛ ≈ lₜ -∗
    ( ∀ vₛ vₜ,
      vₛ ≈ vₜ -∗
      SIM progₛ; vₛ ≳ progₜ; vₜ [[ X ]] {{ Φ }}
    ) -∗
    SIM progₛ; !lₛ ≳ progₜ; !lₜ [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hl Hsim".
    iApply sim_head_step. iIntros "%σₛ %σₜ Hsi !>".
    iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl") as "#(%vₛ & %vₜ & (% & %) & Hv)".
    iSplit; first auto with language. iIntros "%eₜ' %σₜ' %Hstepₜ !>".
    invert_head_step.
    iExists vₛ, σₛ. iSplit; first auto with language. iFrame.
    iApply ("Hsim" with "Hv").
  Qed.

  Lemma sim_storeₛ l v w e Φ :
    l ↦ₛ w -∗
    ( l ↦ₛ v -∗
      SIM progₛ; #() ≳ progₜ; e [[ X ]] {{ Φ }}
    ) -∗
    SIM progₛ; l <- v ≳ progₜ; e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hl Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi".
    iDestruct (sim_state_interp_validₛ with "Hsi Hl") as %?.
    iMod (sim_state_interp_updateₛ v with "Hsi Hl") as "(Hsi & Hl)".
    iExists #(), (<[l := v]> σₛ). iFrame. iSplitR; first auto with language.
    iApply ("Hsim" with "Hl").
  Qed.
  Lemma sim_storeₜ e l v w Φ :
    l ↦ₜ w -∗
    ( l ↦ₜ v -∗
      SIM progₛ; e ≳ progₜ; #() [[ X ]] {{ Φ }}
    ) -∗
    SIM progₛ; e ≳ progₜ; l <- v [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hl Hsim".
    iApply sim_head_stepₜ. iIntros "%σₛ %σₜ Hsi".
    iDestruct (sim_state_interp_validₜ with "Hsi Hl") as %?.
    iSplitR; first auto with language. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
    invert_head_step.
    iMod (sim_state_interp_updateₜ v with "Hsi Hl") as "(Hsi & Hl)".
    iFrame. iApply ("Hsim" with "Hl").
  Qed.
  Lemma sim_store vₛ1 vₛ2 vₜ1 vₜ2 Φ :
    vₛ1 ≈ vₜ1 -∗
    vₛ2 ≈ vₜ2 -∗
    Φ #() #() -∗
    SIM progₛ; vₛ1 <- vₛ2 ≳ progₜ; vₜ1 <- vₜ2 [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hv1 Hv2 HΦ".
    destruct vₛ1, vₜ1;
      try solve
      [ iDestruct "Hv1" as %[]
      | iApply sim_strongly_head_stuck; apply is_strongly_head_stuck
      ].
    iApply sim_head_step. iIntros "%σₛ %σₜ Hsi !>".
    iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hv1") as "#(%wₛ2 & %wₜ2 & (% & %) & Hw)".
    iSplit; first auto with language. iIntros "%eₜ' %σₜ' %Hstepₜ".
    invert_head_step.
    iMod (sim_state_interp_heap_bij_update with "Hsi Hv1 Hv2").
    iExists #(), _. iFrame. iSplitR; first auto with language.
    iApply sim_post; done.
  Qed.
End sim_GS.
