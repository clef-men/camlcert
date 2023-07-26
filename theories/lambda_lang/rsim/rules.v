From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  metatheory
  sim.derived_rules
  rsim.definition.
From simuliris.lambda_lang Require Import
  sim.proofmode
  rsim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms lambda_ectx_lang lambda_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (Χ : sim_protocol Σ).
  Implicit Types func : lambda_function.
  Implicit Types tag : lambda_tag.
  Implicit Types v vₛ vₜ : lambda_val.
  Implicit Types e eₛ eₜ : lambda_expr.

  #[local] Ltac rsim_intro :=
    iIntros "%Γ % % (-> & ->) #HΓ"; sim_simpl.

  Section rsim.
    Implicit Types Φ : lambda_expr → lambda_expr → iProp Σ.

    Lemma rsim_mono Φ1 Φ2 eₛ eₜ :
      (∀ eₛ eₜ, Φ1 eₛ eₜ -∗ Φ2 eₛ eₜ) -∗
      SIM eₛ ⩾ eₜ [[ Χ ]] {{ Φ1 }} -∗
      SIM eₛ ⩾ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      iIntros "HΦ Hrsim". rsim_intro.
      sim_mono "Hrsim".
    Qed.

    Lemma cupd_rsim Φ eₛ eₜ :
      (|++> SIM eₛ ⩾ eₜ [[ Χ ]] {{ Φ }}) ⊢
      SIM eₛ ⩾ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim". rsim_intro.
      iMod "Hrsim". iSmash.
    Qed.
    Lemma bupd_rsim Φ eₛ eₜ :
      (|==> SIM eₛ ⩾ eₜ [[ Χ ]] {{ Φ }}) ⊢
      SIM eₛ ⩾ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim". rsim_intro.
      iMod "Hrsim". iSmash.
    Qed.

    Lemma rsim_cupd Φ eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }} ⊢
      SIM eₛ ⩾ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim". rsim_intro.
      sim_cupd. iSmash.
    Qed.
    Lemma rsim_bupd Φ eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }} ⊢
      SIM eₛ ⩾ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim". rsim_intro.
      sim_bupd. iSmash.
    Qed.

    Lemma rsim_val Φ v :
      lambda_val_well_formed sim_progₛ v →
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      SIM v ⩾ v [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "%Hwf HΦ". rsim_intro.
      sim_post. iApply "HΦ". lambda_expr_simplifier.
    Qed.

    Lemma rsim_var Φ x :
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      SIM $x ⩾ $x [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "HΦ". rsim_intro.
      sim_post.
    Qed.

    Lemma rsim_let Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₜ1 ⩾ eₛ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₜ2 ⩾ eₛ2 [[ Χ ]] {{ Φ }} -∗
      SIM let: eₜ1 in eₜ2 ⩾ let: eₛ1 in eₛ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim1 Hrsim2". rsim_intro.
      sim_apply (sim_let with "(Hrsim1 [//] HΓ)"). iIntros "%vₛ1 %vₜ1 #Hv1".
      sim_asimpl.
      sim_evalₛ (rewrite (bisubst_consₛ _ vₜ1)).
      sim_evalₜ (rewrite (bisubst_consₜ vₛ1)).
      sim_apply ("Hrsim2" with "[//]").
      iApply bisubst_cons_well_formed; iSmash.
    Qed.

    Lemma rsim_call Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₜ1 ⩾ eₛ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₜ2 ⩾ eₛ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ func vₛ vₜ,
        ⌜func ∈ dom sim_progₛ⌝ -∗
        vₛ ≈ vₜ -∗
        SIM func vₛ ≳ func vₜ [[ Χ ]] {{ Φ }}
      ) -∗
      SIM eₜ1 eₜ2 ⩾ eₛ1 eₛ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim1 Hrsim2 Hsim". rsim_intro.
      sim_apply (sim_call with "(Hrsim1 [//] HΓ) (Hrsim2 [//] HΓ) Hsim").
    Qed.

    Lemma rsim_unop Φ op eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaUnop op eₛ ⩾ LambdaUnop op eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim HΦ". rsim_intro.
      sim_apply (sim_unop with "(Hrsim [//] HΓ)").
    Qed.

    Lemma rsim_binop Φ op eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaBinop op eₛ1 eₛ2 ⩾ LambdaBinop op eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim1 Hrsim2 HΦ". rsim_intro.
      sim_apply (sim_binop with "(Hrsim1 [//] HΓ) (Hrsim2 [//] HΓ)").
    Qed.

    Lemma rsim_if Φ eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      SIM eₛ0 ⩾ eₜ0 [[ Χ ]] {{# (≈) }} -∗
      ( SIM eₛ1 ⩾ eₜ1 [[ Χ ]] {{ Φ }} ∧
        SIM eₛ2 ⩾ eₜ2 [[ Χ ]] {{ Φ }}
      ) -∗
      SIM LambdaIf eₛ0 eₛ1 eₛ2 ⩾ LambdaIf eₜ0 eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim0 Hrsim12". rsim_intro.
      sim_apply (sim_if with "(Hrsim0 [//] HΓ)").
      iSplit.
      - iDestruct "Hrsim12" as "(Hrsim1 & _)". iSmash.
      - iDestruct "Hrsim12" as "(_ & Hrsim2)". iSmash.
    Qed.

    Lemma rsim_constr Φ tag eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM &tag eₛ1 eₛ2 ⩾ &tag eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim1 Hrsim2 HΦ". rsim_intro.
      sim_apply (sim_constr with "(Hrsim1 [//] HΓ) (Hrsim2 [//] HΓ)").
    Qed.
    Lemma rsim_constr_valₜ1 Φ tag eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ vₜ -∗
        (lₜ +ₗ 2) ↦ₜ () -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      SIM eₛ ⩾ &tag eₜ #() [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim HΦ". rsim_intro.
      sim_apply (sim_constr_valₜ1 with "(Hrsim [//] HΓ)").
    Qed.
    Lemma rsim_constr_valₜ2 Φ tag eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ () -∗
        (lₜ +ₗ 2) ↦ₜ vₜ -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      SIM eₛ ⩾ &tag #() eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim HΦ". rsim_intro.
      sim_apply (sim_constr_valₜ2 with "(Hrsim [//] HΓ)").
    Qed.

    Lemma rsim_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM ![eₛ2] eₛ1 ⩾ ![eₜ2] eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim1 Hrsim2 HΦ". rsim_intro.
      sim_apply (derived_rules.sim_load with "(Hrsim1 [//] HΓ) (Hrsim2 [//] HΓ)").
    Qed.

    Lemma rsim_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      SIM eₛ1 ⩾ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ3 ⩾ eₜ3 [[ Χ ]] {{# (≈) }} -∗
      Φ #() #() -∗
      SIM eₛ1 <-[eₛ2]- eₛ3 ⩾ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrsim1 Hrsim2 Hrsim3 HΦ". rsim_intro.
      sim_apply (derived_rules.sim_store with "(Hrsim1 [//] HΓ) (Hrsim2 [//] HΓ) (Hrsim3 [//] HΓ)").
    Qed.
  End rsim.

  Section rsimv.
    Implicit Types Φ : lambda_val → lambda_val → iProp Σ.

    Lemma rsimv_mono Φ1 Φ2 eₛ eₜ :
      (∀ vₛ vₜ, Φ1 vₛ vₜ -∗ Φ2 vₛ vₜ) -∗
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# Φ1 }} -∗
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      iIntros "HΦ Hrsim". rsim_intro.
      sim_mono "Hrsim".
    Qed.

    Lemma rsimv_cupd Φ eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# λ vₛ vₜ, |++> Φ vₛ vₜ }} ⊢
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hrsim". rsim_intro.
      sim_cupd. iSmash.
    Qed.
    Lemma rsimv_bupd Φ eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# λ vₛ vₜ, |==> Φ vₛ vₜ }} ⊢
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hrsim". rsim_intro.
      sim_bupd. iSmash.
    Qed.

    Lemma rsimv_val Φ v :
      lambda_val_well_formed sim_progₛ v →
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      SIM v ⩾ v [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "%Hwf HΦ".
      iApply rsim_val; first done.
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma rsimv_var Φ x :
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      SIM $x ⩾ $x [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "HΦ".
      iApply rsim_var.
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma rsimv_unop Φ op eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaUnop op eₛ ⩾ LambdaUnop op eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      iApply (rsim_unop with "Hsim").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma rsimv_binop Φ op eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaBinop op eₛ1 eₛ2 ⩾ LambdaBinop op eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      iApply (rsim_binop with "Hsim1 Hsim2").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma rsimv_constr Φ tag eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM &tag eₛ1 eₛ2 ⩾ &tag eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      iApply (rsim_constr with "Hsim1 Hsim2").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.
    Lemma rsimv_constr_valₜ1 Φ tag eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ vₜ -∗
        (lₜ +ₗ 2) ↦ₜ () -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      SIM eₛ ⩾ &tag eₜ #() [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      iApply (rsim_constr_valₜ1 with "Hsim").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.
    Lemma rsimv_constr_valₜ2 Φ tag eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ () -∗
        (lₜ +ₗ 2) ↦ₜ vₜ -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      SIM eₛ ⩾ &tag #() eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      iApply (rsim_constr_valₜ2 with "Hsim").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma rsimv_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM ![eₛ2] eₛ1 ⩾ ![eₜ2] eₜ1 [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      iApply (rsim_load with "Hsim1 Hsim2").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma rsimv_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      SIM eₛ1 ⩾ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      SIM eₛ3 ⩾ eₜ3 [[ Χ ]] {{# (≈) }} -∗
      Φ ()%lambda_val ()%lambda_val -∗
      SIM eₛ1 <-[eₛ2]- eₛ3 ⩾ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 Hsim3 HΦ".
      iApply (rsim_store with "Hsim1 Hsim2 Hsim3").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.
  End rsimv.
End sim_GS.
