From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  sim.basic_rules.
From simuliris.lambda_lang Require Import
  sim.proofmode
  sim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms lambda_ectx_lang lambda_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (Χ : sim_protocol Σ).
  Implicit Types func : lambda_function.
  Implicit Types tag : lambda_tag.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types v vₛ vₜ : lambda_val.
  Implicit Types e eₛ eₜ : lambda_expr.

  Section sim.
    Implicit Types Φ : lambda_expr → lambda_expr → iProp Σ.

    Lemma sim_let Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        SIM eₛ2.[#vₛ/] ≳ eₜ2.[#vₜ/] [[ Χ ]] {{ Φ }}
      ) -∗
      SIM let: eₛ1 in eₛ2 ≳ let: eₜ1 in eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
      iIntros "Hsim1 Hsim2".
      sim_mono "Hsim1". iIntros "% % (%vₛ & %vₜ & (-> & ->) & #Hv)".
      sim_mono ("Hsim2" with "Hv").
    Qed.

    Lemma sim_call Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ func vₛ vₜ,
        ⌜func ∈ dom sim_progₛ⌝ -∗
        vₛ ≈ vₜ -∗
        SIM func vₛ ≳ func vₜ [[ Χ ]] {{ Φ }}
      ) -∗
      SIM eₛ1 eₛ2 ≳ eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
      iIntros "Hsim1 Hsim2 Hsim".
      sim_mono "Hsim2". iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      sim_mono "Hsim1". iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try sim_strongly_stuck.
      iSmash.
    Qed.

    Lemma sim_unop Φ op eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaUnop op eₛ ≳ LambdaUnop op eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
      iIntros "Hsim HΦ".
      sim_mono "Hsim". iIntros "% % (%vₛ & %vₜ & (-> & ->) & #Hv)".
      destruct vₛ, vₜ; try iDestruct "Hv" as %[];
      destruct op; try sim_strongly_stuck;
      sim_pures.
    Qed.

    Lemma sim_binop Φ op eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaBinop op eₛ1 eₛ2 ≳ LambdaBinop op eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_binopₜ;
        [| iCombine "Hsim1 Hsim2" as "(Hsim2 & Hsim1)"];
        [sim_binopₛ1 | sim_binopₛ2];
        sim_mono "Hsim1"; iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)";
        sim_mono "Hsim2"; iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)";
        sim_pures;
        destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try sim_strongly_stuck;
        destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[]; try sim_strongly_stuck;
        destruct op; try sim_strongly_stuck;
        sim_pures.
    Qed.

    Lemma sim_if Φ eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      SIM eₛ0 ≳ eₜ0 [[ Χ ]] {{# (≈) }} -∗
      ( SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }} ∧
        SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }}
      ) -∗
      SIM LambdaIf eₛ0 eₛ1 eₛ2 ≳ LambdaIf eₜ0 eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
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
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ lₛ lₜ,
        LambdaLoc lₛ ≈ LambdaLoc lₜ -∗
        Φ lₛ lₜ
      ) -∗
      SIM &tag eₛ1 eₛ2 ≳ &tag eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_constrₜ;
        [| iCombine "Hsim1 Hsim2" as "(Hsim2 & Hsim1)"];
        [sim_constrₛ1 | sim_constrₛ2];
        sim_mono "Hsim1"; iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)";
        sim_mono "Hsim2"; iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)";
        sim_constr_det as lₛ lₜ "Hl";
        iApply "HΦ"; iSmash+.
    Qed.
    Lemma sim_constr_valₜ1 Φ eₛ tag eₜ vₜ2 :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ l vₜ1,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ1 -∗
        Φ vₛ l
      ) -∗
      SIM eₛ ≳ &tag eₜ vₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
      iIntros "Hsim HΦ".
      sim_constrₜ;
        sim_mono "Hsim"; iIntros "% % (%vₛ & %vₜ1 & (-> & ->) & #Hv)";
        sim_constr_detₜ as l "Hl0" "Hl1" "Hl2".
    Qed.
    Lemma sim_constr_valₜ2 Φ eₛ tag vₜ1 eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ l vₜ2,
        (l +ₗ 0) ↦ₜ tag -∗
        (l +ₗ 1) ↦ₜ vₜ1 -∗
        (l +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ2 -∗
        Φ vₛ l
      ) -∗
      SIM eₛ ≳ &tag vₜ1 eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
      iIntros "Hsim HΦ".
      sim_constrₜ;
        sim_mono "Hsim"; iIntros "% % (%vₛ & %vₜ2 & (-> & ->) & #Hv)";
        sim_constr_detₜ as l "Hl0" "Hl1" "Hl2".
    Qed.

    Lemma sim_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM ![eₛ2] eₛ1 ≳ ![eₜ2] eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_mono "Hsim2". iIntros "% % (%vₛ2 & %vₜ2 & (-> & ->) & #Hv2)".
      sim_mono "Hsim1". iIntros "% % (%vₛ1 & %vₜ1 & (-> & ->) & #Hv1)".
      destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try sim_strongly_stuck.
      destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[]; try sim_strongly_stuck.
      sim_load as wₛ wₜ "Hw".
    Qed.

    Lemma sim_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ3 ≳ eₜ3 [[ Χ ]] {{# (≈) }} -∗
      Φ #() #() -∗
      SIM eₛ1 <-[eₛ2]- eₛ3 ≳ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite simv_unseal.
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
    Implicit Types Φ : lambda_val → lambda_val → iProp Σ.

    Lemma simv_unop Φ op eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaUnop op eₛ ≳ LambdaUnop op eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      sim_apply (sim_unop with "Hsim").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma simv_binop Φ op eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaBinop op eₛ1 eₛ2 ≳ LambdaBinop op eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_apply (sim_binop with "Hsim1 Hsim2").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma simv_constr Φ tag eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ lₛ lₜ,
        LambdaLoc lₛ ≈ LambdaLoc lₜ -∗
        Φ lₛ lₜ
      ) -∗
      SIM &tag eₛ1 eₛ2 ≳ &tag eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      sim_apply (sim_constr with "Hsim1 Hsim2").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.
    Lemma simv_constr_valₜ1 Φ eₛ tag eₜ vₜ2 :
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
      iIntros "Hsim HΦ".
      sim_apply (sim_constr_valₜ1 with "Hsim").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.
    Lemma simv_constr_valₜ2 Φ eₛ tag vₜ1 eₜ :
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
      iIntros "Hsim HΦ".
      sim_apply (sim_constr_valₜ2 with "Hsim").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
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
      iIntros "Hsim1 Hsim2 HΦ".
      sim_apply (sim_load with "Hsim1 Hsim2").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma simv_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ3 ≳ eₜ3 [[ Χ ]] {{# (≈) }} -∗
      Φ ()%lambda_val ()%lambda_val -∗
      SIM eₛ1 <-[eₛ2]- eₛ3 ≳ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 Hsim3 HΦ".
      sim_apply (sim_store with "Hsim1 Hsim2 Hsim3").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.
  End simv.
End sim_GS.
