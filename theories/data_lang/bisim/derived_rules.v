From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  bisim.basic_rules.
From simuliris.data_lang Require Import
  bisim.proofmode
  bisim.notations.

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

  Section bisim.
    Implicit Types Φ : data_expr → data_expr → iProp Σ.

    Lemma bisim_let Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        BISIM eₛ2.[#vₛ/] ≃ eₜ2.[#vₜ/] [[ Χ ]] {{ Φ }}
      ) -∗
      BISIM let: eₛ1 in eₛ2 ≃ let: eₜ1 in eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim1 Hbisim2".
      bisim_mono "Hbisim1". iIntros "% % (%vₛ & %vₜ & (-> & ->) & #Hv)".
      bisim_mono ("Hbisim2" with "Hv").
    Qed.

    Lemma bisim_call Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ func annot vₛ vₜ,
        ⌜func ∈ dom sim_progₛ⌝ -∗
        vₛ ≈ vₜ -∗
        BISIM (DataFunc func annot) vₛ ≃ (DataFunc func annot) vₜ [[ Χ ]] {{ Φ }}
      ) -∗
      BISIM eₛ1 eₛ2 ≃ eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim1 Hbisim2 Hbisim".
      bisim_mono "Hbisim2". iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      bisim_mono "Hbisim1". iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %?; simplify; try bisim_strongly_stuck. iSmash.
    Qed.

    Lemma bisim_unop Φ op eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM DataUnop op eₛ ≃ DataUnop op eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim HΦ".
      bisim_mono "Hbisim". iIntros "% % (%vₛ & %vₜ & (-> & ->) & #Hv)".
      destruct vₛ, vₜ; try iDestruct "Hv" as %[];
      destruct op; try bisim_strongly_stuck;
      bisim_pures.
    Qed.

    Lemma bisim_binop_valsₛ Φ op v1 v2 v e :
      data_binop_eval op v1 v2 = Some v →
      BISIM v ≃ e [[ Χ ]] {{ Φ }} ⊢
      BISIM DataBinop op v1 v2 ≃ e [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "%Heval Hbisim".
      bisim_binopₛ; bisim_pures.
    Qed.
    Lemma bisim_binop_valsₜ Φ op e v1 v2 v :
      data_binop_eval op v1 v2 = Some v →
      BISIM e ≃ v [[ Χ ]] {{ Φ }} ⊢
      BISIM e ≃ DataBinop op v1 v2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "%Heval Hbisim".
      bisim_binopₜ; bisim_pures.
    Qed.

    Lemma bisim_if Φ eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      BISIM eₛ0 ≃ eₜ0 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{ Φ }} ∧
        BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{ Φ }}
      ) -∗
      BISIM DataIf eₛ0 eₛ1 eₛ2 ≃ DataIf eₜ0 eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim0 Hbisim12".
      bisim_mono "Hbisim0". iIntros "% % (%vₛ0 & %vₜ0 & (-> & ->) & #Hv0)".
      destruct vₛ0, vₜ0; try iDestruct "Hv0" as %[]; try bisim_strongly_stuck.
      destruct b.
      - iDestruct "Hbisim12" as "(Hbisim1 & _)".
        bisim_apply "Hbisim1".
      - iDestruct "Hbisim12" as "(_ & Hbisim2)".
        bisim_apply "Hbisim2".
    Qed.

    Lemma bisim_constr_valₜ1 Φ eₛ tag vₜ1 eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ l vₜ2,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ2 -∗
        Φ vₛ l
      ) -∗
      BISIM eₛ ≃ &tag vₜ1 eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim HΦ".
      bisim_constrₜ.
      all: bisim_mono "Hbisim"; iIntros "% % (%vₛ & %vₜ2 & (-> & ->) & #Hv)".
      all: bisim_constr_detₜ as l "Hl0" "Hl1" "Hl2".
    Qed.
    Lemma bisim_constr_valₜ2 Φ eₛ tag eₜ vₜ2 :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ l vₜ1,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ1 -∗
        Φ vₛ l
      ) -∗
      BISIM eₛ ≃ &tag eₜ vₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim HΦ".
      bisim_constrₜ.
      all: bisim_mono "Hbisim"; iIntros "% % (%vₛ & %vₜ1 & (-> & ->) & #Hv)".
      all: bisim_constr_detₜ as l "Hl0" "Hl1" "Hl2".
    Qed.

    Lemma bisim_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM ![eₛ2] eₛ1 ≃ ![eₜ2] eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim1 Hbisim2 HΦ".
      bisim_mono "Hbisim2". iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      bisim_mono "Hbisim1". iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try bisim_strongly_stuck.
      destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[]; try bisim_strongly_stuck.
      bisim_load as wₛ wₜ "Hw".
    Qed.

    Lemma bisim_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      BISIM eₛ3 ≃ eₜ3 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      Φ #() #() -∗
      BISIM eₛ1 <-[eₛ2]- eₛ3 ≃ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hbisim1 Hbisim2 Hbisim3 HΦ".
      bisim_mono "Hbisim3". iIntros "% % (%vₛ3 & %vₜ3 & (-> & ->) & #Hv3)".
      bisim_mono "Hbisim2". iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      bisim_mono "Hbisim1". iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try bisim_strongly_stuck.
      destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[]; try bisim_strongly_stuck.
      bisim_store.
    Qed.
  End bisim.

  Section bisimv.
    Implicit Types Φ : data_val → data_val → iProp Σ.

    Lemma bisimv_let Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        BISIM eₛ2.[#vₛ/] ≃ eₜ2.[#vₜ/] [[ Χ ]] {{# Φ }}
      ) -∗
      BISIM let: eₛ1 in eₛ2 ≃ let: eₜ1 in eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "Hbisim1 Hbisim2".
      bisim_apply (bisim_let with "Hbisim1 Hbisim2").
    Qed.

    Lemma bisimv_call Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ func annot vₛ vₜ,
        ⌜func ∈ dom sim_progₛ⌝ -∗
        vₛ ≈ vₜ -∗
        BISIM (DataFunc func annot) vₛ ≃ (DataFunc func annot) vₜ [[ Χ ]] {{# Φ }}
      ) -∗
      BISIM eₛ1 eₛ2 ≃ eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "Hbisim1 Hbisim2 HΦ".
      bisim_apply (bisim_call with "Hbisim1 Hbisim2").
    Qed.

    Lemma bisimv_unop Φ op eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM DataUnop op eₛ ≃ DataUnop op eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "Hbisim HΦ".
      bisim_apply (bisim_unop with "Hbisim").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma bisimv_if Φ eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      BISIM eₛ0 ≃ eₜ0 [[ Χ ]] {{# (≈) }} -∗
      ( BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{# Φ }} ∧
        BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{# Φ }}
      ) -∗
      BISIM DataIf eₛ0 eₛ1 eₛ2 ≃ DataIf eₜ0 eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "Hbisim0 Hbisim12".
      bisim_apply (bisim_if with "Hbisim0 Hbisim12").
    Qed.

    Lemma bisimv_constr_valₜ1 Φ eₛ tag vₜ1 eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ l vₜ2,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ2 -∗
        Φ vₛ l
      ) -∗
      BISIM eₛ ≃ &tag vₜ1 eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "Hbisim HΦ".
      bisim_apply (bisim_constr_valₜ1 with "Hbisim").
      rewrite /sim_post_vals'. iSmash.
    Qed.
    Lemma bisimv_constr_valₜ2 Φ eₛ tag eₜ vₜ2 :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ l vₜ1,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ1 -∗
        Φ vₛ l
      ) -∗
      BISIM eₛ ≃ &tag eₜ vₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "Hbisim HΦ".
      bisim_apply (bisim_constr_valₜ2 with "Hbisim").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma bisimv_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM ![eₛ2] eₛ1 ≃ ![eₜ2] eₜ1 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "Hbisim1 Hbisim2 HΦ".
      bisim_apply (bisim_load with "Hbisim1 Hbisim2").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma bisimv_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      BISIM eₛ3 ≃ eₜ3 [[ Χ ]] {{# (≈) }} -∗
      Φ ()%data_val ()%data_val -∗
      BISIM eₛ1 <-[eₛ2]- eₛ3 ≃ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal.
      iIntros "Hbisim1 Hbisim2 Hbisim3 HΦ".
      bisim_apply (bisim_store with "Hbisim1 Hbisim2 Hbisim3").
    Qed.
  End bisimv.
End sim_GS.
