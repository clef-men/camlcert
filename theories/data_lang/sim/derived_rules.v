From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  sim.basic_rules.
From simuliris.data_lang Require Import
  sim.proofmode
  sim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (Χ : sim_protocol Σ).

  Implicit Types n : Z.
  Implicit Types func : data_function.
  Implicit Types tag : data_tag.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types v vₛ vₜ : data_val.
  Implicit Types e eₛ eₜ : data_expr.

  Section sim.
    Implicit Types Φ : data_expr → data_expr → iProp Σ.

    Lemma sim_let Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        SIM eₛ2.[#vₛ/] ≳ eₜ2.[#vₜ/] [[ Χ ]] {{ Φ }}
      ) -∗
      SIM let: eₛ1 in eₛ2 ≳ let: eₜ1 in eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2".
      sim_mono "Hsim1". iIntros "% % (%vₛ & %vₜ & (-> & ->) & #Hv)".
      sim_mono ("Hsim2" with "Hv").
    Qed.

    Lemma sim_call Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ func annot vₛ vₜ,
        ⌜func ∈ dom sim_progₛ⌝ -∗
        vₛ ≈ vₜ -∗
        SIM (DataFunc func annot) vₛ ≳ (DataFunc func annot) vₜ [[ Χ ]] {{ Φ }}
      ) -∗
      SIM eₛ1 eₛ2 ≳ eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 Hsim".
      sim_mono "Hsim2". iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      sim_mono "Hsim1". iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %?; simplify; try sim_strongly_stuck. iSmash.
    Qed.

    Lemma sim_unop Φ op eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM DataUnop op eₛ ≳ DataUnop op eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      sim_mono "Hsim". iIntros "% % (%vₛ & %vₜ & (-> & ->) & #Hv)".
      destruct vₛ, vₜ; try iDestruct "Hv" as %[];
      destruct op; try sim_strongly_stuck;
      sim_pures.
    Qed.

    Lemma sim_binop Φ op eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM DataBinop op eₛ1 eₛ2 ≳ DataBinop op eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_binopₜ;
      [ sim_binopₛ1
      | iCombine "Hsim1 Hsim2" as "(Hsim2 & Hsim1)"; sim_binopₛ2
      ].
      all: sim_mono "Hsim1"; iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      all: sim_mono "Hsim2"; iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      all: sim_pures.
      all: destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try sim_strongly_stuck.
      all: destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[]; try sim_strongly_stuck.
      all: destruct op; try sim_strongly_stuck.
      all: sim_pures.
      all: iDestruct "Hv1" as "(Hv1 & _)"; iDestruct "Hv2" as "(Hv2 & _)"; rewrite !loc_add_0.
      all: iDestruct (sim_heap_bij_agree with "Hv1 Hv2") as %Hiff.
      all: iApply "HΦ".
      all: iPureIntro; rewrite ?bool_decide_not; f_equal; apply bool_decide_ext; naive_solver.
    Qed.
    Lemma sim_binop_valsₛ Φ op v1 v2 v e :
      data_binop_eval op v1 v2 = Some v →
      SIM v ≳ e [[ Χ ]] {{ Φ }} ⊢
      SIM DataBinop op v1 v2 ≳ e [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "%Heval Hsim".
      sim_binopₛ1. sim_pures.
    Qed.
    Lemma sim_binop_valsₜ Φ op e v1 v2 v :
      data_binop_eval op v1 v2 = Some v →
      SIM e ≳ v [[ Χ ]] {{ Φ }} ⊢
      SIM e ≳ DataBinop op v1 v2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "%Heval Hsim".
      sim_binopₜ; sim_pures.
    Qed.

    Lemma sim_if Φ eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      SIM eₛ0 ≳ eₜ0 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }} ∧
        SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }}
      ) -∗
      SIM DataIf eₛ0 eₛ1 eₛ2 ≳ DataIf eₜ0 eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim0 Hsim12".
      sim_mono "Hsim0". iIntros "% % (%vₛ0 & %vₜ0 & (-> & ->) & #Hv0)".
      destruct vₛ0, vₜ0; try iDestruct "Hv0" as %[]; try sim_strongly_stuck.
      destruct b.
      - iDestruct "Hsim12" as "(Hsim1 & _)".
        sim_apply "Hsim1".
      - iDestruct "Hsim12" as "(_ & Hsim2)".
        sim_apply "Hsim2".
    Qed.

    Lemma sim_constr Φ tag eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ lₛ lₜ,
        DataLoc lₛ ≈ DataLoc lₜ -∗
        Φ lₛ lₜ
      ) -∗
      SIM &tag eₛ1 eₛ2 ≳ &tag eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_constrₜ;
      [ sim_constrₛ1
      | iCombine "Hsim1 Hsim2" as "(Hsim2 & Hsim1)"; sim_constrₛ2
      ].
      all: sim_mono "Hsim1"; iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      all: sim_mono "Hsim2"; iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      all: sim_constr_det as lₛ lₜ "Hl".
      all: iApply "HΦ"; iSmash+.
    Qed.
    Lemma sim_constr_valₜ1 Φ eₛ tag vₜ1 eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ l vₜ2,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ2 -∗
        Φ vₛ l
      ) -∗
      SIM eₛ ≳ &tag vₜ1 eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      sim_constrₜ.
      all: sim_mono "Hsim"; iIntros "% % (%vₛ & %vₜ2 & (-> & ->) & #Hv)".
      all: sim_constr_detₜ as l "Hl0" "Hl1" "Hl2".
    Qed.
    Lemma sim_constr_valₜ2 Φ eₛ tag eₜ vₜ2 :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ l vₜ1,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ1 -∗
        Φ vₛ l
      ) -∗
      SIM eₛ ≳ &tag eₜ vₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      sim_constrₜ.
      all: sim_mono "Hsim"; iIntros "% % (%vₛ & %vₜ1 & (-> & ->) & #Hv)".
      all: sim_constr_detₜ as l "Hl0" "Hl1" "Hl2".
    Qed.

    Lemma sim_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM ![eₛ2] eₛ1 ≳ ![eₜ2] eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_mono "Hsim2". iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      sim_mono "Hsim1". iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try sim_strongly_stuck.
      destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[]; try sim_strongly_stuck.
      sim_load as wₛ wₜ "Hw".
    Qed.

    Lemma sim_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      SIM eₛ3 ≳ eₜ3 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      Φ #() #() -∗
      SIM eₛ1 <-[eₛ2]- eₛ3 ≳ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 Hsim3 HΦ".
      sim_mono "Hsim3". iIntros "% % (%vₛ3 & %vₜ3 & (-> & ->) & #Hv3)".
      sim_mono "Hsim2". iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      sim_mono "Hsim1". iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try sim_strongly_stuck.
      destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[]; try sim_strongly_stuck.
      sim_store.
    Qed.
  End sim.

  Section simv.
    Implicit Types Φ : data_val → data_val → iProp Σ.

    Lemma simv_let Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        SIM eₛ2.[#vₛ/] ≳ eₜ2.[#vₜ/] [[ Χ ]] {{# Φ }}
      ) -∗
      SIM let: eₛ1 in eₛ2 ≳ let: eₜ1 in eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim1 Hsim2".
      sim_apply (sim_let with "Hsim1 Hsim2").
    Qed.

    Lemma simv_call Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ func annot vₛ vₜ,
        ⌜func ∈ dom sim_progₛ⌝ -∗
        vₛ ≈ vₜ -∗
        SIM (DataFunc func annot) vₛ ≳ (DataFunc func annot) vₜ [[ Χ ]] {{# Φ }}
      ) -∗
      SIM eₛ1 eₛ2 ≳ eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_apply (sim_call with "Hsim1 Hsim2").
    Qed.

    Lemma simv_unop Φ op eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM DataUnop op eₛ ≳ DataUnop op eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim HΦ".
      sim_apply (sim_unop with "Hsim").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma simv_binop Φ op eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM DataBinop op eₛ1 eₛ2 ≳ DataBinop op eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_apply (sim_binop with "Hsim1 Hsim2").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma simv_if Φ eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      SIM eₛ0 ≳ eₜ0 [[ Χ ]] {{# (≈) }} -∗
      ( SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# Φ }} ∧
        SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# Φ }}
      ) -∗
      SIM DataIf eₛ0 eₛ1 eₛ2 ≳ DataIf eₜ0 eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim0 Hsim12".
      sim_apply (sim_if with "Hsim0 Hsim12").
    Qed.

    Lemma simv_constr Φ tag eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ lₛ lₜ,
        DataLoc lₛ ≈ DataLoc lₜ -∗
        Φ lₛ lₜ
      ) -∗
      SIM &tag eₛ1 eₛ2 ≳ &tag eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_apply (sim_constr with "Hsim1 Hsim2").
      rewrite /sim_post_vals'. iSmash.
    Qed.
    Lemma simv_constr_valₜ1 Φ eₛ tag vₜ1 eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ l vₜ2,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ2 -∗
        Φ vₛ l
      ) -∗
      SIM eₛ ≳ &tag vₜ1 eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim HΦ".
      sim_apply (sim_constr_valₜ1 with "Hsim").
      rewrite /sim_post_vals'. iSmash.
    Qed.
    Lemma simv_constr_valₜ2 Φ eₛ tag eₜ vₜ2 :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ l vₜ1,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ1 -∗
        Φ vₛ l
      ) -∗
      SIM eₛ ≳ &tag eₜ vₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim HΦ".
      sim_apply (sim_constr_valₜ2 with "Hsim").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma simv_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM ![eₛ2] eₛ1 ≳ ![eₜ2] eₜ1 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_apply (sim_load with "Hsim1 Hsim2").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma simv_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ3 ≳ eₜ3 [[ Χ ]] {{# (≈) }} -∗
      Φ ()%data_val ()%data_val -∗
      SIM eₛ1 <-[eₛ2]- eₛ3 ≳ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal.
      iIntros "Hsim1 Hsim2 Hsim3 HΦ".
      sim_apply (sim_store with "Hsim1 Hsim2 Hsim3").
    Qed.
  End simv.
End sim_GS.
