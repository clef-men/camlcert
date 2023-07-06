From simuliris Require Import
  prelude.
From simuliris.base_logic Require Import
  lib.cupd.proofmode.
From simuliris.program_logic Require Export
  sim.rules.
From simuliris.lambda_lang Require Export
  tactics.
From simuliris.lambda_lang Require Import
  well_formed.
From simuliris.tmc Require Export
  sim.definition.
From simuliris.tmc Require Import
  sim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms lambda_ectx_lang lambda_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Implicit Types tag : lambda_tag.
  Implicit Types idx idxₛ idxₜ : lambda_index.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types e eₛ eₜ : lambda_expr.
  Implicit Types v vₛ vₜ w : lambda_val.

  #[global] Instance lambda_val_bi_similar_persistent vₛ vₜ :
    Persistent (vₛ ≈ vₜ).
  Proof.
    destruct vₛ, vₜ; apply _.
  Qed.

  Lemma lambda_val_similar_bi_similar vₛ vₜ :
    lambda_val_well_formed sim_progₛ vₛ →
    vₛ ≈ vₜ →
    ⊢ vₛ ≈ vₜ.
  Proof.
    intros Hwf Hv.
    destruct vₛ, vₜ; inversion Hwf; inversion Hv; naive_solver.
  Qed.
  Lemma lambda_val_bi_similar_similar vₛ vₜ :
    vₛ ≈ vₜ -∗
    ⌜vₛ ≈ vₜ⌝.
  Proof.
    iIntros "Hv".
    destruct vₛ, vₜ; try iDestruct "Hv" as %[]; done.
  Qed.

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
      lₛ ⋈ lₜ ∗
      (lₛ ⋈ lₜ -∗ sim_state_interp σₛ σₜ).
  Proof.
    iIntros "(Hheapₛ & Hheapₜ & Hbij) Hl".
    iDestruct (sim_heap_bij_access with "Hbij Hl") as "(Hl & Hbij)".
    iFrame. done.
  Qed.

  Lemma sim_state_interp_heap_bij_insert lₛ lₜ :
    lₛ ⋈ lₜ ++∗
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

  Context (X : sim_protocol Σ).

  Lemma sim_binopₛ1 op e1 e2 e Φ :
    SIM let: e1 in let: e2.[ren (+1)] in LambdaBinopDet op $1 $0 ≳ e [[ X ]] {{ Φ }} -∗
    SIM LambdaBinop op e1 e2 ≳ e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
    iExists _, σₛ. iFrame. auto with lambda_lang.
  Qed.
  Lemma sim_binopₛ2 op e1 e2 e Φ :
    SIM let: e2 in let: e1.[ren (+1)] in LambdaBinopDet op $0 $1 ≳ e [[ X ]] {{ Φ }} -∗
    SIM LambdaBinop op e1 e2 ≳ e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
    iExists _, σₛ. iFrame. auto with lambda_lang.
  Qed.
  Lemma sim_binopₜ op e e1 e2 Φ :
      SIM e ≳ let: e1 in let: e2.[ren (+1)] in LambdaBinopDet op $1 $0 [[ X ]] {{ Φ }}
    ∧ SIM e ≳ let: e2 in let: e1.[ren (+1)] in LambdaBinopDet op $0 $1 [[ X ]] {{ Φ }}
    -∗
    SIM e ≳ LambdaBinop op e1 e2 [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
    iSplit; first auto with lambda_lang. iIntros "%eₜ' %σₜ' %Hstepₜ".
    invert_lambda_head_step; iFrame.
    - iDestruct "Hsim" as "($ & _)". done.
    - iDestruct "Hsim" as "(_ & $)". done.
  Qed.

  Lemma sim_constrₛ1 tag e1 e2 e Φ :
    SIM let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 ≳ e [[ X ]] {{ Φ }} -∗
    SIM &tag e1 e2 ≳ e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
    iExists _, σₛ. iFrame. auto with lambda_lang.
  Qed.
  Lemma sim_constrₛ2 tag e1 e2 e Φ :
    SIM let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 ≳ e [[ X ]] {{ Φ }} -∗
    SIM &tag e1 e2 ≳ e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
    iExists _, σₛ. iFrame. auto with lambda_lang.
  Qed.
  Lemma sim_constrₜ tag e e1 e2 Φ :
      SIM e ≳ let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 [[ X ]] {{ Φ }}
    ∧ SIM e ≳ let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 [[ X ]] {{ Φ }}
    -∗
    SIM e ≳ &tag e1 e2 [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
    iSplit; first auto with lambda_lang. iIntros "%eₜ' %σₜ' %Hstepₜ".
    invert_lambda_head_step; iFrame.
    - iDestruct "Hsim" as "($ & _)". done.
    - iDestruct "Hsim" as "(_ & $)". done.
  Qed.

  Lemma sim_constr_detₛ tag v1 v2 e Φ :
    ( ∀ l,
      (l +ₗ 0) ↦ₛ tag -∗
      (l +ₗ 1) ↦ₛ v1 -∗
      (l +ₗ 2) ↦ₛ v2 -∗
      SIM l ≳ e [[ X ]] {{ Φ }}
    ) -∗
    SIM &&tag v1 v2 ≳ e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi".
    set l := loc_fresh (dom σₛ).
    set (σₛ' := {[l +ₗ 2 := v2 ; l +ₗ 1 := v1 ; l +ₗ 0 := LambdaTag tag]} : lambda_state).
    iMod (sim_state_interp_alloc_bigₛ σₛ' with "Hsi") as "(Hsi & Hmapstos & _)".
    { rewrite !map_disjoint_insert_l -!not_elem_of_dom. split_and!;
      [ apply loc_fresh_fresh; done..
      | apply map_disjoint_empty_l
      ].
    }
    iDestruct (big_sepM_insert with "Hmapstos") as "(Hl2 & Hmapstos)".
    { do 2 (rewrite lookup_insert_ne; last by intros ?%(inj _)). done. }
    iDestruct (big_sepM_insert with "Hmapstos") as "(Hl1 & Hl0)".
    { rewrite lookup_insert_ne; last by intros ?%(inj _). done. }
    rewrite big_sepM_singleton.
    iExists #l, (σₛ' ∪ σₛ). iFrame. iSplitR.
    { iPureIntro. apply lambda_head_step_constr_det'.
      rewrite -!insert_union_l left_id //.
    }
    iApply ("Hsim" with "Hl0 Hl1 Hl2").
  Qed.
  Lemma sim_constr_detₜ e tag v1 v2 Φ :
    ( ∀ l,
      (l +ₗ 0) ↦ₜ tag -∗
      (l +ₗ 1) ↦ₜ v1 -∗
      (l +ₗ 2) ↦ₜ v2 -∗
      SIM e ≳ l [[ X ]] {{ Φ }}
    ) -∗
    SIM e ≳ &&tag v1 v2 [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iApply sim_head_stepₜ. iIntros "%σₛ %σₜ Hsi".
    iSplitR; first auto with lambda_lang. iIntros "!> %eₜ' %σₜ'' %Hstepₜ".
    invert_lambda_head_step.
    set (σₜ' := {[l +ₗ 2 := v2 ; l +ₗ 1 := v1 ; l +ₗ 0 := LambdaTag tag]} : lambda_state).
    iMod (sim_state_interp_alloc_bigₜ σₜ' with "Hsi") as "(Hsi & Hmapstos & _)".
    { rewrite !map_disjoint_insert_l . naive_solver apply map_disjoint_empty_l. }
    iDestruct (big_sepM_insert with "Hmapstos") as "(Hl2 & Hmapstos)".
    { do 2 (rewrite lookup_insert_ne; last by intros ?%(inj _)). done. }
    iDestruct (big_sepM_insert with "Hmapstos") as "(Hl1 & Hl0)".
    { rewrite lookup_insert_ne; last by intros ?%(inj _). done. }
    rewrite big_sepM_singleton.
    rewrite -!insert_union_l left_id. iFrame.
    iApply ("Hsim" with "Hl0 Hl1 Hl2").
  Qed.
  Lemma sim_constr_det tag vₛ1 vₛ2 vₜ1 vₜ2 Φ :
    vₛ1 ≈ vₜ1 -∗
    vₛ2 ≈ vₜ2 -∗
    ( ∀ lₛ lₜ,
      LambdaLoc lₛ ≈ LambdaLoc lₜ ++∗
      Φ #lₛ #lₜ
    ) -∗
    SIM &&tag vₛ1 vₛ2 ≳ &&tag vₜ1 vₜ2 [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hv1 Hv2 HΦ".
    iApply sim_constr_detₛ. iIntros "%lₛ Hlₛ0 Hlₛ1 Hlₛ2".
    iApply sim_constr_detₜ. iIntros "%lₜ Hlₜ0 Hlₜ1 Hlₜ2".
    iApply cupd_sim.
    iMod (sim_state_interp_heap_bij_insert with "[Hlₛ0 Hlₜ0]") as "Hl0".
    { iExists tag, tag. auto with iFrame. }
    iMod (sim_state_interp_heap_bij_insert with "[Hlₛ1 Hlₜ1 Hv1]") as "Hl1".
    { iExists vₛ1, vₜ1. auto with iFrame. }
    iMod (sim_state_interp_heap_bij_insert with "[Hlₛ2 Hlₜ2 Hv2]") as "Hl2".
    { iExists vₛ2, vₜ2. auto with iFrame. }
    iMod ("HΦ" with "[$Hl0 $Hl1 $Hl2]") as "HΦ".
    iApply (sim_post with "HΦ"); done.
  Qed.

  Lemma sim_loadₛ l idx v e Φ :
    (l +ₗ idx) ↦ₛ v -∗
    ( (l +ₗ idx) ↦ₛ v -∗
      SIM v ≳ e [[ X ]] {{ Φ }}
    ) -∗
    SIM ![idx] l ≳ e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hl Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
    iDestruct (sim_state_interp_validₛ with "Hsi Hl") as %?.
    iExists #v, σₛ. iSplit; first auto with lambda_lang. iFrame.
    iApply ("Hsim" with "Hl").
  Qed.
  Lemma sim_loadₜ e l idx v Φ :
    (l +ₗ idx) ↦ₜ v -∗
    ( (l +ₗ idx) ↦ₜ v -∗
      SIM e ≳ v [[ X ]] {{ Φ }}
    ) -∗
    SIM e ≳ ![idx] l [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hl Hsim".
    iApply sim_head_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
    iDestruct (sim_state_interp_validₜ with "Hsi Hl") as %?.
    iSplit; first auto with lambda_lang. iIntros "%eₜ' %σₜ' %Hstepₜ !>".
    invert_lambda_head_step. iFrame.
    iApply ("Hsim" with "Hl").
  Qed.
  Lemma sim_load lₛ idxₛ lₜ idxₜ Φ :
    LambdaLoc lₛ ≈ LambdaLoc lₜ -∗
    LambdaIndex idxₛ ≈ LambdaIndex idxₜ -∗
    ( ∀ vₛ vₜ,
      vₛ ≈ vₜ -∗
      SIM vₛ ≳ vₜ [[ X ]] {{ Φ }}
    ) -∗
    SIM ![idxₛ] lₛ ≳ ![idxₜ] lₜ [[ X ]] {{ Φ }}.
  Proof.
    iIntros "(Hl0 & Hl1 & Hl2) <- Hsim".
    iApply sim_head_step. iIntros "%σₛ %σₜ Hsi !>".
    destruct idxₛ.
    1: iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl0") as "#(%vₛ0 & %vₜ0 & (% & %) & Hv0)".
    2: iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl1") as "#(%vₛ1 & %vₜ1 & (% & %) & Hv1)".
    3: iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl2") as "#(%vₛ2 & %vₜ2 & (% & %) & Hv2)".
    all: iSplit; first auto with lambda_lang; iIntros "%eₜ' %σₜ' %Hstepₜ !>".
    all: invert_lambda_head_step.
    all: iExists _, σₛ; iFrame; iSplit; first auto with lambda_lang.
    - iApply ("Hsim" with "Hv0").
    - iApply ("Hsim" with "Hv1").
    - iApply ("Hsim" with "Hv2").
  Qed.

  Lemma sim_storeₛ l idx v w e Φ :
    (l +ₗ idx) ↦ₛ w -∗
    ( (l +ₗ idx) ↦ₛ v -∗
      SIM #() ≳ e [[ X ]] {{ Φ }}
    ) -∗
    SIM l <-[idx]- v ≳ e [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hl Hsim".
    iApply sim_head_stepₛ. iIntros "%σₛ %σₜ Hsi".
    iDestruct (sim_state_interp_validₛ with "Hsi Hl") as %?.
    iMod (sim_state_interp_updateₛ v with "Hsi Hl") as "(Hsi & Hl)".
    iExists #(), (<[l +ₗ idx := v]> σₛ). iFrame. iSplitR; first auto with lambda_lang.
    iApply ("Hsim" with "Hl").
  Qed.
  Lemma sim_storeₜ e l idx v w Φ :
    (l +ₗ idx) ↦ₜ w -∗
    ( (l +ₗ idx) ↦ₜ v -∗
      SIM e ≳ #() [[ X ]] {{ Φ }}
    ) -∗
    SIM e ≳ l <-[idx]- v [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hl Hsim".
    iApply sim_head_stepₜ. iIntros "%σₛ %σₜ Hsi".
    iDestruct (sim_state_interp_validₜ with "Hsi Hl") as %?.
    iSplitR; first auto with lambda_lang. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
    invert_lambda_head_step.
    iMod (sim_state_interp_updateₜ v with "Hsi Hl") as "(Hsi & Hl)".
    iFrame. iApply ("Hsim" with "Hl").
  Qed.
  Lemma sim_store vₛ1 vₛ2 vₛ3 vₜ1 vₜ2 vₜ3 Φ :
    vₛ1 ≈ vₜ1 -∗
    vₛ2 ≈ vₜ2 -∗
    vₛ3 ≈ vₜ3 -∗
    Φ #() #() -∗
    SIM vₛ1 <-[vₛ2]- vₛ3 ≳ vₜ1 <-[vₜ2]- vₜ3 [[ X ]] {{ Φ }}.
  Proof.
    iIntros "Hv1 Hv2 Hv3 HΦ".
    destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[];
    destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[];
    try solve [iApply sim_strongly_head_stuck; auto with lambda_lang].
    iDestruct "Hv1" as "(Hl0 & Hl1 & Hl2)".
    iApply sim_head_step. iIntros "%σₛ %σₜ Hsi !>".
    destruct idx.
    1: iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl0") as "#(%wₛ0 & %wₜ0 & (% & %) & Hw0)".
    2: iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl1") as "#(%wₛ1 & %wₜ1 & (% & %) & Hw1)".
    3: iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl2") as "#(%wₛ2 & %wₜ2 & (% & %) & Hw2)".
    all: iSplit; first auto with lambda_lang; iIntros "%eₜ' %σₜ' %Hstepₜ".
    all: invert_lambda_head_step.
    1: iMod (sim_state_interp_heap_bij_update with "Hsi Hl0 Hv3").
    2: iMod (sim_state_interp_heap_bij_update with "Hsi Hl1 Hv3").
    3: iMod (sim_state_interp_heap_bij_update with "Hsi Hl2 Hv3").
    all: iExists #(), _; iFrame; iSplitR; first auto with lambda_lang.
    all: iApply sim_post; done.
  Qed.
End sim_GS.
