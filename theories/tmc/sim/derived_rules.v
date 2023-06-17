From simuliris Require Import
  prelude.
From simuliris.tmc Require Export
  sim.basic_rules.
From simuliris.tmc Require Import
  sim.proofmode
  sim.notations.

Section sim.
  Context `{sim_programs : !SimPrograms ectx_language ectx_language}.
  Context `{sim_GS : !SimGS Σ}.
  Context (X : sim_protocol Σ).
  Implicit Types func : function.
  Implicit Types constr : constructor.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types v vₛ vₜ : val.
  Implicit Types e eₛ eₜ : expr.
  Implicit Types Φ : val → val → iProp Σ.

  Lemma simv_let eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    ( ∀ vₛ vₜ,
      vₛ ≈ vₜ -∗
      SIM eₛ2.[#vₛ/] ≳ eₜ2.[#vₜ/] [[ X ]] [[ Φ ]]
    ) -∗
    SIM let: eₛ1 in eₛ2 ≳ let: eₜ1 in eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2".
    simv_mono "Hsim1". iIntros "%vₛ %vₜ #Hv".
    simv_smart_mono ("Hsim2" with "Hv").
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
    simv_mono "Hsim2". iIntros "%vₛ2 %vₜ2 #Hv2".
    simv_mono "Hsim1". iIntros "%vₛ1 %vₜ1 #Hv1".
    destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[]; try simv_strongly_stuck.
    subst. simv_apply ("Hsim" with "[//] Hv2").
  Qed.

  Lemma simv_unop op eₛ eₜ Φ :
    SIM eₛ ≳ eₜ [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM Unop op eₛ ≳ Unop op eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim HΦ".
    simv_mono "Hsim". iIntros "%vₛ %vₜ #Hv".
    destruct vₛ, vₜ; try iDestruct "Hv" as %[];
    destruct op; try simv_strongly_stuck;
      simv_pures;
      iApply "HΦ"; auto.
  Qed.

  Lemma simv_binop op eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM Binop op eₛ1 eₛ2 ≳ Binop op eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2 HΦ".
    simv_mono "Hsim2". iIntros "%vₛ2 %vₜ2 #Hv2".
    simv_mono "Hsim1". iIntros "%vₛ1 %vₜ1 #Hv1".
    destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[];
    destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[];
    destruct op; try simv_strongly_stuck;
      simv_pures;
      iApply "HΦ"; subst; auto.
  Qed.

  Lemma simv_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 Φ :
    SIM eₛ0 ≳ eₜ0 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ Φ ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ Φ ]] -∗
    SIM If eₛ0 eₛ1 eₛ2 ≳ If eₜ0 eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim0 Hsim1 Hsim2".
    simv_mono "Hsim0". iIntros "%vₛ0 %vₜ0 #Hv0".
    destruct vₛ0, vₜ0; try iDestruct "Hv0" as %[]; try simv_strongly_stuck.
    destruct b; [simv_smart_apply "Hsim1" | simv_smart_apply "Hsim2"].
  Qed.

  Lemma simv_constr constr eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ (≈) ]] -∗
    (∀ lₛ lₜ, Loc lₛ ≈ Loc lₜ -∗ Φ lₛ lₜ) -∗
    SIM &constr eₛ1 eₛ2 ≳ &constr eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2 HΦ".
    simv_constrₜ;
      [| iCombine "Hsim1 Hsim2" as "(Hsim2 & Hsim1)"];
      [simv_constrₛ1 | simv_constrₛ2];
      simv_mono "Hsim1"; iIntros "%vₛ1 %vₜ1 #Hv1";
      simv_smart_mono "Hsim2"; iIntros "%vₛ2 %vₜ2 #Hv2";
      simv_constr_det as lₛ lₜ "Hl";
      iApply "HΦ"; done.
  Qed.
  Lemma simv_constr_valₜ1 eₛ constr eₜ vₜ2 Φ :
    SIM eₛ ≳ eₜ [[ X ]] [[ (≈) ]] -∗
    ( ∀ vₛ l vₜ1,
      (l +ₗ 0) ↦ₜ constr -∗
      (l +ₗ 1) ↦ₜ vₜ1 -∗
      (l +ₗ 2) ↦ₜ vₜ2 -∗
      vₛ ≈ vₜ1 -∗
      Φ vₛ l
    ) -∗
    SIM eₛ ≳ &constr eₜ vₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim HΦ".
    simv_constrₜ;
      simv_smart_mono "Hsim"; iIntros "%vₛ %vₜ1 #Hv";
      simv_constr_detₜ as l "Hl0" "Hl1" "Hl2";
      iApply ("HΦ" with "Hl0 Hl1 Hl2 Hv").
  Qed.
  Lemma simv_constr_valₜ2 eₛ constr vₜ1 eₜ Φ :
    SIM eₛ ≳ eₜ [[ X ]] [[ (≈) ]] -∗
    ( ∀ vₛ l vₜ2,
      (l +ₗ 0) ↦ₜ constr -∗
      (l +ₗ 1) ↦ₜ vₜ1 -∗
      (l +ₗ 2) ↦ₜ vₜ2 -∗
      vₛ ≈ vₜ2 -∗
      Φ vₛ l
    ) -∗
    SIM eₛ ≳ &constr vₜ1 eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim HΦ".
    simv_constrₜ;
      simv_smart_mono "Hsim"; iIntros "%vₛ %vₜ2 #Hv";
      simv_constr_detₜ as l "Hl0" "Hl1" "Hl2";
      iApply ("HΦ" with "Hl0 Hl1 Hl2 Hv").
  Qed.

  Lemma simv_load eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM ![eₛ2] eₛ1 ≳ ![eₜ2] eₜ1 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2 HΦ".
    simv_mono "Hsim2". iIntros "%vₛ2 %vₜ2 #Hv2".
    simv_mono "Hsim1". iIntros "%vₛ1 %vₜ1 #Hv1".
    destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[];
    destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[];
      try simv_strongly_stuck.
    simv_load as wₛ wₜ "Hw".
    iApply ("HΦ" with "Hw").
  Qed.

  Lemma simv_store eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 Φ :
    SIM eₛ1 ≳ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ≳ eₜ2 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ3 ≳ eₜ3 [[ X ]] [[ (≈) ]] -∗
    Φ ()%V ()%V -∗
    SIM eₛ1 <-[eₛ2]- eₛ3 ≳ eₜ1 <-[eₜ2]- eₜ3 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hsim1 Hsim2 Hsim3 HΦ".
    simv_mono "Hsim3". iIntros "%vₛ3 %vₜ3 #Hv3".
    simv_mono "Hsim2". iIntros "%vₛ2 %vₜ2 #Hv2".
    simv_mono "Hsim1". iIntros "%vₛ1 %vₜ1 #Hv1".
    destruct vₛ1, vₜ1; try iDestruct "Hv1" as %[];
    destruct vₛ2, vₜ2; try iDestruct "Hv2" as %[];
      try simv_strongly_stuck.
    simv_store.
  Qed.
End sim.
