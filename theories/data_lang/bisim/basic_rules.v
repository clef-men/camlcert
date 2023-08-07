From simuliris Require Import
  prelude.
From simuliris.program_logic Require Export
  bisim.rules.
From simuliris.program_logic Require Import
  bisim.proofmode.
From simuliris.data_lang Require Export
  tactics
  (* FIXME: remove this dependency *)
  sim.basic_rules
  bisim.definition.
From simuliris.data_lang Require Import
  metatheory
  bisim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (Χ : sim_protocol Σ).
  Implicit Types tag : data_tag.
  Implicit Types idx idxₛ idxₜ : data_index.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types e eₛ eₜ : data_expr.
  Implicit Types v vₛ vₜ w : data_val.

  Section bisim.
    Implicit Types Φ : data_expr → data_expr → iProp Σ.

    Lemma bisim_binopₛ Φ op e1 e2 e :
        BISIM let: e1 in let: e2.[ren (+1)] in DataBinopDet op $1 $0 ≃ e [[ Χ ]] {{ Φ }}
      ∧ BISIM let: e2 in let: e1.[ren (+1)] in DataBinopDet op $0 $1 ≃ e [[ Χ ]] {{ Φ }}
      ⊢
      BISIM DataBinop op e1 e2 ≃ e [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim".
      iApply bisim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
      iSplit; first auto with data_lang. iIntros "%eₛ' %σₛ' %Hstepₛ".
      invert_data_head_step; iFrame.
      - iDestruct "Hbisim" as "($ & _)". iSmash.
      - iDestruct "Hbisim" as "(_ & $)". iSmash.
    Qed.
    Lemma bisim_binopₜ Φ op e e1 e2 :
        BISIM e ≃ let: e1 in let: e2.[ren (+1)] in DataBinopDet op $1 $0 [[ Χ ]] {{ Φ }}
      ∧ BISIM e ≃ let: e2 in let: e1.[ren (+1)] in DataBinopDet op $0 $1 [[ Χ ]] {{ Φ }}
      ⊢
      BISIM e ≃ DataBinop op e1 e2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim".
      iApply bisim_head_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
      iSplit; first auto with data_lang. iIntros "%eₜ' %σₜ' %Hstepₜ".
      invert_data_head_step; iFrame.
      - iDestruct "Hbisim" as "($ & _)". iSmash.
      - iDestruct "Hbisim" as "(_ & $)". iSmash.
    Qed.

    Lemma bisim_binop_det Φ vₛ1 vₛ2 vₜ1 vₜ2 :
      vₛ1 ≈ vₜ1 -∗
      vₛ2 ≈ vₜ2 -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM DataBinopDet DataOpPlus vₛ1 vₛ2 ≃ DataBinopDet DataOpPlus vₜ1 vₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "#Hv1 #Hv2 HΦ".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try bisim_strongly_stuck;
      destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[]; try bisim_strongly_stuck.
      iApply bisim_pure_step; [auto with data_lang.. |].
      bisim_post.
    Qed.

    Lemma bisim_constrₛ Φ tag e1 e2 e :
        BISIM let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 ≃ e [[ Χ ]] {{ Φ }}
      ∧ BISIM let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 ≃ e [[ Χ ]] {{ Φ }}
      ⊢
      BISIM &tag e1 e2 ≃ e [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim".
      iApply bisim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
      iSplit; first auto with data_lang. iIntros "%eₛ' %σₛ' %Hstepₛ".
      invert_data_head_step; iFrame.
      - iDestruct "Hbisim" as "($ & _)". iSmash.
      - iDestruct "Hbisim" as "(_ & $)". iSmash.
    Qed.
    Lemma bisim_constrₜ Φ tag e e1 e2 :
        BISIM e ≃ let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 [[ Χ ]] {{ Φ }}
      ∧ BISIM e ≃ let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 [[ Χ ]] {{ Φ }}
      ⊢
      BISIM e ≃ &tag e1 e2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim".
      iApply bisim_head_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
      iSplit; first auto with data_lang. iIntros "%eₜ' %σₜ' %Hstepₜ".
      invert_data_head_step; iFrame.
      - iDestruct "Hbisim" as "($ & _)". iSmash.
      - iDestruct "Hbisim" as "(_ & $)". iSmash.
    Qed.

    Lemma bisim_constr_detₛ Φ tag v1 v2 e :
      ( ∀ l,
        (l +ₗ 0) ↦ₛ tag -∗
        (l +ₗ 1) ↦ₛ v1 -∗
        (l +ₗ 2) ↦ₛ v2 -∗
        BISIM l ≃ e [[ Χ ]] {{ Φ }}
      ) ⊢
      BISIM &&tag v1 v2 ≃ e [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim".
      iApply bisim_head_stepₛ. iIntros "%σₛ %σₜ Hsi".
      iSplitR; first auto with data_lang. iIntros "!> %eₛ' %σₛ'' %Hstepₛ".
      invert_data_head_step.
      set (σₛ' := {[l +ₗ 2 := v2 ; l +ₗ 1 := v1 ; l +ₗ 0 := DataTag tag]} : data_state).
      iMod (sim_state_interp_alloc_bigₛ σₛ' with "Hsi") as "(Hsi & Hmapstos & _)".
      { rewrite !map_disjoint_insert_l . naive_solver apply map_disjoint_empty_l. }
      iDestruct (big_sepM_insert with "Hmapstos") as "(Hl2 & Hmapstos)".
      { do 2 (rewrite lookup_insert_ne; last by intros ?%(inj _)). done. }
      iDestruct (big_sepM_insert with "Hmapstos") as "(Hl1 & Hl0)".
      { rewrite lookup_insert_ne; last by intros ?%(inj _). done. }
      rewrite big_sepM_singleton.
      rewrite -!insert_union_l left_id. iFrame. iSmash.
    Qed.
    Lemma bisim_constr_detₜ Φ e tag v1 v2 :
      ( ∀ l,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ v1 -∗
        (l +ₗ 2) ↦ₜ v2 -∗
        BISIM e ≃ l [[ Χ ]] {{ Φ }}
      ) ⊢
      BISIM e ≃ &&tag v1 v2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim".
      iApply bisim_head_stepₜ. iIntros "%σₛ %σₜ Hsi".
      iSplitR; first auto with data_lang. iIntros "!> %eₜ' %σₜ'' %Hstepₜ".
      invert_data_head_step.
      set (σₜ' := {[l +ₗ 2 := v2 ; l +ₗ 1 := v1 ; l +ₗ 0 := DataTag tag]} : data_state).
      iMod (sim_state_interp_alloc_bigₜ σₜ' with "Hsi") as "(Hsi & Hmapstos & _)".
      { rewrite !map_disjoint_insert_l . naive_solver apply map_disjoint_empty_l. }
      iDestruct (big_sepM_insert with "Hmapstos") as "(Hl2 & Hmapstos)".
      { do 2 (rewrite lookup_insert_ne; last by intros ?%(inj _)). done. }
      iDestruct (big_sepM_insert with "Hmapstos") as "(Hl1 & Hl0)".
      { rewrite lookup_insert_ne; last by intros ?%(inj _). done. }
      rewrite big_sepM_singleton.
      rewrite -!insert_union_l left_id. iFrame. iSmash.
    Qed.
    Lemma bisim_constr_det Φ tag vₛ1 vₛ2 vₜ1 vₜ2 :
      vₛ1 ≈ vₜ1 -∗
      vₛ2 ≈ vₜ2 -∗
      ( ∀ lₛ lₜ,
        DataLoc lₛ ≈ DataLoc lₜ ++∗
        Φ #lₛ #lₜ
      ) -∗
      BISIM &&tag vₛ1 vₛ2 ≃ &&tag vₜ1 vₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hv1 Hv2 HΦ".
      iApply bisim_constr_detₛ. iIntros "%lₛ Hlₛ0 Hlₛ1 Hlₛ2".
      iApply bisim_constr_detₜ. iIntros "%lₜ Hlₜ0 Hlₜ1 Hlₜ2".
      iMod (sim_state_interp_heap_bij_insert with "[Hlₛ0 Hlₜ0]") as "Hl0".
      { iExists tag, tag. iSmash. }
      iMod (sim_state_interp_heap_bij_insert with "[Hlₛ1 Hlₜ1 Hv1]") as "Hl1".
      { iExists vₛ1, vₜ1. iSmash. }
      iMod (sim_state_interp_heap_bij_insert with "[Hlₛ2 Hlₜ2 Hv2]") as "Hl2".
      { iExists vₛ2, vₜ2. iSmash. }
      iMod ("HΦ" with "[$Hl0 $Hl1 $Hl2]") as "HΦ".
      bisim_post.
    Qed.

    Lemma bisim_loadₛ Φ l idx v e :
      (l +ₗ idx) ↦ₛ v -∗
      ( (l +ₗ idx) ↦ₛ v -∗
        BISIM v ≃ e [[ Χ ]] {{ Φ }}
      ) -∗
      BISIM ![idx] l ≃ e [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hl Hbisim".
      iApply bisim_head_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
      iDestruct (sim_state_interp_validₛ with "Hsi Hl") as %?.
      iSplit; first auto with data_lang. iIntros "%eₛ' %σₛ' %Hstepₛ !>".
      invert_data_head_step. iFrame. iSmash.
    Qed.
    Lemma bisim_loadₜ Φ e l idx v :
      (l +ₗ idx) ↦ₜ v -∗
      ( (l +ₗ idx) ↦ₜ v -∗
        BISIM e ≃ v [[ Χ ]] {{ Φ }}
      ) -∗
      BISIM e ≃ ![idx] l [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hl Hbisim".
      iApply bisim_head_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
      iDestruct (sim_state_interp_validₜ with "Hsi Hl") as %?.
      iSplit; first auto with data_lang. iIntros "%eₜ' %σₜ' %Hstepₜ !>".
      invert_data_head_step. iFrame. iSmash.
    Qed.
    Lemma bisim_load Φ lₛ idxₛ lₜ idxₜ :
      DataLoc lₛ ≈ DataLoc lₜ -∗
      DataIndex idxₛ ≈ DataIndex idxₜ -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM ![idxₛ] lₛ ≃ ![idxₜ] lₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "(Hl0 & Hl1 & Hl2) <- Hbisim".
      iApply bisim_head_step. iIntros "%σₛ %σₜ Hsi !>".
      iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl0") as "#(%vₛ0 & %vₜ0 & (%Hlₛ0 & %Hlₜ0) & Hv0)".
      iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl1") as "#(%vₛ1 & %vₜ1 & (%Hlₛ1 & %Hlₜ1) & Hv1)".
      iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl2") as "#(%vₛ2 & %vₜ2 & (%Hlₛ2 & %Hlₜ2) & Hv2)".
      destruct idxₛ.
      all: iSplit; first auto with data_lang; iIntros "%eₛ' %σₛ' %eₜ' %σₜ' (%Hstepₛ & %Hstepₜ) !>".
      all: invert_data_head_step.
      all: iFrame; bisim_post.
    Qed.

    Lemma bisim_storeₛ Φ l idx v w e :
      (l +ₗ idx) ↦ₛ w -∗
      ( (l +ₗ idx) ↦ₛ v -∗
        BISIM #() ≃ e [[ Χ ]] {{ Φ }}
      ) -∗
      BISIM l <-[idx]- v ≃ e [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hl Hbisim".
      iApply bisim_head_stepₛ. iIntros "%σₛ %σₜ Hsi".
      iDestruct (sim_state_interp_validₛ with "Hsi Hl") as %?.
      iSplitR; first auto with data_lang. iIntros "!> %eₛ' %σₛ' %Hstepₛ".
      invert_data_head_step.
      iMod (sim_state_interp_updateₛ v with "Hsi Hl") as "(Hsi & Hl)".
      iFrame. iSmash.
    Qed.
    Lemma bisim_storeₜ Φ e l idx v w :
      (l +ₗ idx) ↦ₜ w -∗
      ( (l +ₗ idx) ↦ₜ v -∗
        BISIM e ≃ #() [[ Χ ]] {{ Φ }}
      ) -∗
      BISIM e ≃ l <-[idx]- v [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hl Hbisim".
      iApply bisim_head_stepₜ. iIntros "%σₛ %σₜ Hsi".
      iDestruct (sim_state_interp_validₜ with "Hsi Hl") as %?.
      iSplitR; first auto with data_lang. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
      invert_data_head_step.
      iMod (sim_state_interp_updateₜ v with "Hsi Hl") as "(Hsi & Hl)".
      iFrame. iSmash.
    Qed.
    Lemma bisim_store Φ vₛ1 vₛ2 vₛ3 vₜ1 vₜ2 vₜ3 :
      vₛ1 ≈ vₜ1 -∗
      vₛ2 ≈ vₜ2 -∗
      vₛ3 ≈ vₜ3 -∗
      Φ #() #() -∗
      BISIM vₛ1 <-[vₛ2]- vₛ3 ≃ vₜ1 <-[vₜ2]- vₜ3 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hv1 Hv2 Hv3 HΦ".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try bisim_strongly_stuck.
      destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[]; try bisim_strongly_stuck.
      iDestruct "Hv1" as "(Hl0 & Hl1 & Hl2)".
      iApply bisim_head_step. iIntros "%σₛ %σₜ Hsi !>".
      iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl0") as "#(%wₛ0 & %wₜ0 & (%Hlₛ0 & %Hlₜ0) & Hw0)".
      iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl1") as "#(%wₛ1 & %wₜ1 & (%Hlₛ1 & %Hlₜ1) & Hw1)".
      iDestruct (sim_state_interp_heap_bij_valid with "Hsi Hl2") as "#(%wₛ2 & %wₜ2 & (%Hlₛ2 & %Hlₜ2) & Hw2)".
      destruct idx.
      all: iSplit; first auto with data_lang; iIntros "%eₛ' %σₛ' %eₜ' %σₜ' (%Hstepₛ & %Hstepₜ)".
      all: invert_data_head_step.
      1: iMod (sim_state_interp_heap_bij_update with "Hsi Hl0 Hv3").
      2: iMod (sim_state_interp_heap_bij_update with "Hsi Hl1 Hv3").
      3: iMod (sim_state_interp_heap_bij_update with "Hsi Hl2 Hv3").
      all: iModIntro; iFrame; bisim_post.
    Qed.
  End bisim.

  Section bisimv.
    Implicit Types Φ : data_val → data_val → iProp Σ.

    Lemma bisimv_binop_det Φ vₛ1 vₛ2 vₜ1 vₜ2 :
      vₛ1 ≈ vₜ1 -∗
      vₛ2 ≈ vₜ2 -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM DataBinopDet DataOpPlus vₛ1 vₛ2 ≃ DataBinopDet DataOpPlus vₜ1 vₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "#Hv1 #Hv2 HΦ".
      iApply (bisim_binop_det with "Hv1 Hv2").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma bisimv_constr_det Φ tag vₛ1 vₛ2 vₜ1 vₜ2 :
      vₛ1 ≈ vₜ1 -∗
      vₛ2 ≈ vₜ2 -∗
      ( ∀ lₛ lₜ,
        DataLoc lₛ ≈ DataLoc lₜ ++∗
        Φ lₛ lₜ
      ) -∗
      BISIM &&tag vₛ1 vₛ2 ≃ &&tag vₜ1 vₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "#Hv1 #Hv2 HΦ".
      iApply (bisim_constr_det with "Hv1 Hv2").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma bisimv_load Φ lₛ idxₛ lₜ idxₜ :
      DataLoc lₛ ≈ DataLoc lₜ -∗
      DataIndex idxₛ ≈ DataIndex idxₜ -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM ![idxₛ] lₛ ≃ ![idxₜ] lₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "#Hl #Hidx HΦ".
      iApply (bisim_load with "Hl Hidx").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma bisimv_store Φ vₛ1 vₛ2 vₛ3 vₜ1 vₜ2 vₜ3 :
      vₛ1 ≈ vₜ1 -∗
      vₛ2 ≈ vₜ2 -∗
      vₛ3 ≈ vₜ3 -∗
      Φ ()%data_val ()%data_val -∗
      BISIM vₛ1 <-[vₛ2]- vₛ3 ≃ vₜ1 <-[vₜ2]- vₜ3 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "#Hv1 #Hv2 #Hv3 HΦ".
      iApply (bisim_store with "Hv1 Hv2 Hv3").
      rewrite /sim_post_vals'. iSmash.
    Qed.
  End bisimv.
End sim_GS.
