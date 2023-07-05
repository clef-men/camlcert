From simuliris Require Import
  prelude.
From simuliris.tmc Require Export
  sim.basic_rules.
From simuliris.tmc Require Import
  sim.proofmode
  sim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms lambda_ectx_lang lambda_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (X : sim_protocol Σ).
  Implicit Types func : lambda_function.
  Implicit Types tag : lambda_tag.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types v vₛ vₜ : lambda_val.
  Implicit Types e eₛ eₜ : lambda_expr.
  Implicit Types Φ : lambda_val → lambda_val → iProp Σ.

  Lemma simv_let eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    ( ∀ vₛ vₜ,
      vₛ ≈ vₜ -∗
      SIM eₛ2.[#vₛ/] ≳ eₜ2.[#vₜ/] [[ X ]] [[ Φ ]]
    ) -∗
    SIM let: eₛ1 in eₛ2 ≳ let: eₜ1 in eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2".
    sim_mono "Hsim1". iIntros "%vₛ %vₜ #Hv".
    sim_smart_mono ("Hsim2" with "Hv").
  Qed.

  Lemma simv_call eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ (≈) ]] -∗
    ( ∀ func vₛ vₜ,
      ⌜func ∈ dom sim_progₛ⌝ -∗
      vₛ ≈ vₜ -∗
      SIM func vₛ ≳ func vₜ [[ X ]] [[ Φ ]]
    ) -∗
    SIM eₛ1 eₛ2 ≳ eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2 Hsim".
    sim_mono "Hsim2". iIntros "%vₛ2 %vₜ2 #Hv2".
    sim_mono "Hsim1". iIntros "%vₛ1 %vₜ1 #Hv1".
    destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try sim_strongly_stuck.
    subst. sim_apply ("Hsim" with "[//] Hv2").
  Qed.

  Lemma simv_unop op eₛ eₜ Φ :
    SIM eₛ ≳ eₜ [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM LambdaUnop op eₛ ≳ LambdaUnop op eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim HΦ".
    sim_mono "Hsim". iIntros "%vₛ %vₜ #Hv".
    destruct vₛ, vₜ; try iDestruct "Hv" as %[];
    destruct op; try sim_strongly_stuck;
      sim_pures;
      iApply "HΦ"; auto.
  Qed.

  Lemma simv_binop op eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM LambdaBinop op eₛ1 eₛ2 ≳ LambdaBinop op eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2 HΦ".
    sim_mono "Hsim2". iIntros "%vₛ2 %vₜ2 #Hv2".
    sim_mono "Hsim1". iIntros "%vₛ1 %vₜ1 #Hv1".
    destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[];
    destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[];
    destruct op; try sim_strongly_stuck;
      sim_pures;
      iApply "HΦ"; subst; auto.
  Qed.

  Lemma simv_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 Φ :
    SIM eₛ0 ≳ eₜ0 [[ X ]] [[ (≈) ]] -∗
    ( SIM eₛ1 ≳ eₜ1 [[ X ]] [[ Φ ]] ∧
      SIM eₛ2 ≳ eₜ2 [[ X ]] [[ Φ ]]
    ) -∗
    SIM LambdaIf eₛ0 eₛ1 eₛ2 ≳ LambdaIf eₜ0 eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim0 Hsim12".
    sim_mono "Hsim0". iIntros "%vₛ0 %vₜ0 #Hv0".
    destruct vₛ0, vₜ0; try iDestruct "Hv0" as %[]; try sim_strongly_stuck.
    destruct b.
    - iDestruct "Hsim12" as "(Hsim1 & _)".
      sim_smart_apply "Hsim1".
    - iDestruct "Hsim12" as "(_ & Hsim2)".
      sim_smart_apply "Hsim2".
  Qed.

  Lemma simv_constr tag eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ (≈) ]] -∗
    (∀ lₛ lₜ, LambdaLoc lₛ ≈ LambdaLoc lₜ -∗ Φ lₛ lₜ) -∗
    SIM &tag eₛ1 eₛ2 ≳ &tag eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2 HΦ".
    sim_constrₜ;
      [| iCombine "Hsim1 Hsim2" as "(Hsim2 & Hsim1)"];
      [sim_constrₛ1 | sim_constrₛ2];
      sim_mono "Hsim1"; iIntros "%vₛ1 %vₜ1 #Hv1";
      sim_smart_mono "Hsim2"; iIntros "%vₛ2 %vₜ2 #Hv2";
      sim_constr_det as lₛ lₜ "Hl";
      iApply "HΦ"; done.
  Qed.
  Lemma simv_constr_valₜ1 eₛ tag eₜ vₜ2 Φ :
    SIM eₛ ≳ eₜ [[ X ]] [[ (≈) ]] -∗
    ( ∀ vₛ l vₜ1,
      (l +ₗ 0) ↦ₜ tag -∗
      (l +ₗ 1) ↦ₜ vₜ1 -∗
      (l +ₗ 2) ↦ₜ vₜ2 -∗
      vₛ ≈ vₜ1 -∗
      Φ vₛ l
    ) -∗
    SIM eₛ ≳ &tag eₜ vₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim HΦ".
    sim_constrₜ;
      sim_smart_mono "Hsim"; iIntros "%vₛ %vₜ1 #Hv";
      sim_constr_detₜ as l "Hl0" "Hl1" "Hl2";
      iApply ("HΦ" with "Hl0 Hl1 Hl2 Hv").
  Qed.
  Lemma simv_constr_valₜ2 eₛ tag vₜ1 eₜ Φ :
    SIM eₛ ≳ eₜ [[ X ]] [[ (≈) ]] -∗
    ( ∀ vₛ l vₜ2,
      (l +ₗ 0) ↦ₜ tag -∗
      (l +ₗ 1) ↦ₜ vₜ1 -∗
      (l +ₗ 2) ↦ₜ vₜ2 -∗
      vₛ ≈ vₜ2 -∗
      Φ vₛ l
    ) -∗
    SIM eₛ ≳ &tag vₜ1 eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim HΦ".
    sim_constrₜ;
      sim_smart_mono "Hsim"; iIntros "%vₛ %vₜ2 #Hv";
      sim_constr_detₜ as l "Hl0" "Hl1" "Hl2";
      iApply ("HΦ" with "Hl0 Hl1 Hl2 Hv").
  Qed.

  Lemma simv_load eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM ![eₛ2] eₛ1 ≳ ![eₜ2] eₜ1 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2 HΦ".
    sim_mono "Hsim2". iIntros "%vₛ2 %vₜ2 #Hv2".
    sim_mono "Hsim1". iIntros "%vₛ1 %vₜ1 #Hv1".
    destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[];
    destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[];
      try sim_strongly_stuck.
    sim_load as wₛ wₜ "Hw".
    iApply ("HΦ" with "Hw").
  Qed.

  Lemma simv_store eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ3 ≳ eₜ3 [[ X ]] [[ (≈) ]] -∗
    Φ ()%lambda_val ()%lambda_val -∗
    SIM eₛ1 <-[eₛ2]- eₛ3 ≳ eₜ1 <-[eₜ2]- eₜ3 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2 Hsim3 HΦ".
    sim_mono "Hsim3". iIntros "%vₛ3 %vₜ3 #Hv3".
    sim_mono "Hsim2". iIntros "%vₛ2 %vₜ2 #Hv2".
    sim_mono "Hsim1". iIntros "%vₛ1 %vₜ1 #Hv1".
    destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[];
    destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[];
      try sim_strongly_stuck.
    sim_store.
  Qed.
End sim_GS.
