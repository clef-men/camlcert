From simuliris Require Import
  prelude.
From simuliris.tmc_lang Require Export
  well_formed.
From simuliris.tmc Require Export
  sim.derived_rules
  csim.definition.
From simuliris.tmc Require Import
  sim.proofmode
  csim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms tmc_ectx_lang tmc_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (X : sim_protocol Σ).
  Implicit Types func : function.
  Implicit Types constr : constructor.
  Implicit Types v vₛ vₜ : val.
  Implicit Types e eₛ eₜ : expr.
  Implicit Types Φ : val → val → iProp Σ.

  Notation csimv := (csimv X).

  #[local] Ltac csimv_start :=
    iIntros "%Γ % % (-> & ->) #HΓ"; sim_simpl.

  Lemma csimv_mono eₛ eₜ Φ1 Φ2 :
    (∀ vₛ vₜ, Φ1 vₛ vₜ -∗ Φ2 vₛ vₜ) -∗
    csimv Φ1 eₛ eₜ -∗ csimv Φ2 eₛ eₜ.
  Proof.
    iIntros "HΦ Hcsim". csimv_start.
    sim_mono "Hcsim".
  Qed.

  Lemma cupd_csimv eₛ eₜ Φ :
    (|++> SIM eₛ ⩾ eₜ [[ X ]] [[ Φ ]]) -∗
    SIM eₛ ⩾ eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim". csimv_start.
    iMod "Hcsim". sim_apply ("Hcsim" with "[//] HΓ").
  Qed.
  Lemma bupd_csimv eₛ eₜ Φ :
    (|==> SIM eₛ ⩾ eₜ [[ X ]] [[ Φ ]]) -∗
    SIM eₛ ⩾ eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim". csimv_start.
    iMod "Hcsim". sim_apply ("Hcsim" with "[//] HΓ").
  Qed.

  Lemma csimv_cupd eₛ eₜ Φ :
    SIM eₛ ⩾ eₜ [[ X ]] [[ λ vₛ vₜ, |++> Φ vₛ vₜ ]] -∗
    SIM eₛ ⩾ eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim". csimv_start.
    sim_cupd. sim_apply ("Hcsim" with "[//] HΓ").
  Qed.
  Lemma csimv_bupd eₛ eₜ Φ :
    SIM eₛ ⩾ eₜ [[ X ]] [[ λ vₛ vₜ, |==> Φ vₛ vₜ ]] -∗
    SIM eₛ ⩾ eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim". csimv_start.
    sim_bupd. sim_apply ("Hcsim" with "[//] HΓ").
  Qed.

  Lemma csimv_val v Φ :
    val_well_formed sim_progₛ v →
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM v ⩾ v [[ X ]] [[ Φ ]].
  Proof.
    iIntros "%Hwf HΦ". csimv_start.
    sim_post. iApply "HΦ". expr_simplifier.
  Qed.

  Lemma csimv_var x Φ :
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM $x ⩾ $x [[ X ]] [[ Φ ]].
  Proof.
    iIntros "HΦ". csimv_start.
    sim_post. iApply ("HΦ" with "HΓ").
  Qed.

  Lemma csimv_let eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₜ1 ⩾ eₛ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₜ2 ⩾ eₛ2 [[ X ]] [[ Φ ]] -∗
    SIM let: eₜ1 in eₜ2 ⩾ let: eₛ1 in eₛ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim1 Hcsim2". csimv_start.
    sim_apply (simv_let with "(Hcsim1 [//] HΓ)"). iIntros "%vₛ1 %vₜ1 #Hv1".
    sim_asimpl.
    sim_evalₛ (rewrite (bisubst_consₛ _ vₜ1)).
    sim_evalₜ (rewrite (bisubst_consₜ vₛ1)).
    sim_apply ("Hcsim2" with "[//]").
    iApply bisubst_cons_well_formed; done.
  Qed.

  Lemma csimv_call eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₜ1 ⩾ eₛ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₜ2 ⩾ eₛ2 [[ X ]] [[ (≈) ]] -∗
    ( ∀ func vₛ vₜ,
      ⌜func ∈ dom sim_progₛ⌝ -∗
      vₛ ≈ vₜ -∗
      SIM func vₛ ≳ func vₜ [[ X ]] [[ Φ ]]
    ) -∗
    SIM eₜ1 eₜ2 ⩾ eₛ1 eₛ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim1 Hcsim2 Hsim". csimv_start.
    sim_apply (simv_call with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ) Hsim").
  Qed.

  Lemma csimv_unop op eₛ eₜ Φ :
    SIM eₛ ⩾ eₜ [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM Unop op eₛ ⩾ Unop op eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim HΦ". csimv_start.
    sim_apply (simv_unop with "(Hcsim [//] HΓ)").
  Qed.

  Lemma csimv_binop op eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ⩾ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ⩾ eₜ2 [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM Binop op eₛ1 eₛ2 ⩾ Binop op eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim1 Hcsim2 HΦ". csimv_start.
    sim_apply (simv_binop with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ)").
  Qed.

  Lemma csimv_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 Φ :
    SIM eₛ0 ⩾ eₜ0 [[ X ]] [[ (≈) ]] -∗
    ( SIM eₛ1 ⩾ eₜ1 [[ X ]] [[ Φ ]] ∧
      SIM eₛ2 ⩾ eₜ2 [[ X ]] [[ Φ ]]
    ) -∗
    SIM If eₛ0 eₛ1 eₛ2 ⩾ If eₜ0 eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim0 Hcsim12". csimv_start.
    sim_apply (simv_if with "(Hcsim0 [//] HΓ)").
    iSplit.
    - iDestruct "Hcsim12" as "(Hcsim1 & _)".
      iApply ("Hcsim1" with "[//] HΓ").
    - iDestruct "Hcsim12" as "(_ & Hcsim2)".
      iApply ("Hcsim2" with "[//] HΓ").
  Qed.

  Lemma csimv_constr constr eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ⩾ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ⩾ eₜ2 [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM &constr eₛ1 eₛ2 ⩾ &constr eₜ1 eₜ2 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim1 Hcsim2 HΦ". csimv_start.
    sim_apply (simv_constr with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ)"). iIntros "%lₛ %lₜ #Hl".
    iApply ("HΦ" with "Hl").
  Qed.
  Lemma csimv_constr_valₜ1 constr eₛ eₜ Φ :
    SIM eₛ ⩾ eₜ [[ X ]] [[ (≈) ]] -∗
    ( ∀ vₛ lₜ vₜ,
      (lₜ +ₗ 0) ↦ₜ constr -∗
      (lₜ +ₗ 1) ↦ₜ vₜ -∗
      (lₜ +ₗ 2) ↦ₜ () -∗
      vₛ ≈ vₜ -∗
      Φ vₛ lₜ
    ) -∗
    SIM eₛ ⩾ &constr eₜ #() [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim HΦ". csimv_start.
    sim_apply (simv_constr_valₜ1 with "(Hcsim [//] HΓ)").
  Qed.
  Lemma csimv_constr_valₜ2 constr eₛ eₜ Φ :
    SIM eₛ ⩾ eₜ [[ X ]] [[ (≈) ]] -∗
    ( ∀ vₛ lₜ vₜ,
      (lₜ +ₗ 0) ↦ₜ constr -∗
      (lₜ +ₗ 1) ↦ₜ () -∗
      (lₜ +ₗ 2) ↦ₜ vₜ -∗
      vₛ ≈ vₜ -∗
      Φ vₛ lₜ
    ) -∗
    SIM eₛ ⩾ &constr #() eₜ [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim HΦ". csimv_start.
    sim_apply (simv_constr_valₜ2 with "(Hcsim [//] HΓ)").
  Qed.

  Lemma csimv_load eₛ1 eₛ2 eₜ1 eₜ2 Φ :
    SIM eₛ1 ⩾ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ⩾ eₜ2 [[ X ]] [[ (≈) ]] -∗
    (∀ vₛ vₜ, vₛ ≈ vₜ -∗ Φ vₛ vₜ) -∗
    SIM ![eₛ2] eₛ1 ⩾ ![eₜ2] eₜ1 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim1 Hcsim2 HΦ". csimv_start.
    sim_apply (simv_load with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ)").
  Qed.

  Lemma csimv_store eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 Φ :
    SIM eₛ1 ⩾ eₜ1 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ2 ⩾ eₜ2 [[ X ]] [[ (≈) ]] -∗
    SIM eₛ3 ⩾ eₜ3 [[ X ]] [[ (≈) ]] -∗
    Φ ()%V ()%V -∗
    SIM eₛ1 <-[eₛ2]- eₛ3 ⩾ eₜ1 <-[eₜ2]- eₜ3 [[ X ]] [[ Φ ]].
  Proof.
    iIntros "Hcsim1 Hcsim2 Hcsim3 HΦ". csimv_start.
    sim_apply (simv_store with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ) (Hcsim3 [//] HΓ)").
  Qed.
End sim_GS.
