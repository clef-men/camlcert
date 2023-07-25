From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  well_formed.
From simuliris.lambda_lang Require Export
  sim.derived_rules
  csim.definition.
From simuliris.lambda_lang Require Import
  sim.proofmode
  csim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms lambda_ectx_lang lambda_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (X : sim_protocol Σ).
  Implicit Types func : lambda_function.
  Implicit Types tag : lambda_tag.
  Implicit Types v vₛ vₜ : lambda_val.
  Implicit Types e eₛ eₜ : lambda_expr.

  #[local] Ltac csim_intro :=
    iIntros "%Γ % % (-> & ->) #HΓ"; sim_simpl.

  Section csim.
    Implicit Types Φ : lambda_expr → lambda_expr → iProp Σ.

    Lemma csim_mono Φ1 Φ2 eₛ eₜ :
      (∀ eₛ eₜ, Φ1 eₛ eₜ -∗ Φ2 eₛ eₜ) -∗
      SIM eₛ ⩾ eₜ [[ X ]] {{ Φ1 }} -∗
      SIM eₛ ⩾ eₜ [[ X ]] {{ Φ2 }}.
    Proof.
      iIntros "HΦ Hcsim". csim_intro.
      sim_mono "Hcsim".
    Qed.

    Lemma cupd_csim Φ eₛ eₜ :
      (|++> SIM eₛ ⩾ eₜ [[ X ]] {{ Φ }}) ⊢
      SIM eₛ ⩾ eₜ [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim". csim_intro.
      iMod "Hcsim". iSmash.
    Qed.
    Lemma bupd_csim Φ eₛ eₜ :
      (|==> SIM eₛ ⩾ eₜ [[ X ]] {{ Φ }}) ⊢
      SIM eₛ ⩾ eₜ [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim". csim_intro.
      iMod "Hcsim". iSmash.
    Qed.

    Lemma csim_cupd Φ eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }} ⊢
      SIM eₛ ⩾ eₜ [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim". csim_intro.
      sim_cupd. iSmash.
    Qed.
    Lemma csim_bupd Φ eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }} ⊢
      SIM eₛ ⩾ eₜ [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim". csim_intro.
      sim_bupd. iSmash.
    Qed.

    Lemma csim_val Φ v :
      lambda_val_well_formed sim_progₛ v →
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      SIM v ⩾ v [[ X ]] {{ Φ }}.
    Proof.
      iIntros "%Hwf HΦ". csim_intro.
      sim_post. iApply "HΦ". lambda_expr_simplifier.
    Qed.

    Lemma csim_var Φ x :
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      SIM $x ⩾ $x [[ X ]] {{ Φ }}.
    Proof.
      iIntros "HΦ". csim_intro.
      sim_post.
    Qed.

    Lemma csim_let Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₜ1 ⩾ eₛ1 [[ X ]] {{# (≈) }} -∗
      SIM eₜ2 ⩾ eₛ2 [[ X ]] {{ Φ }} -∗
      SIM let: eₜ1 in eₜ2 ⩾ let: eₛ1 in eₛ2 [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim1 Hcsim2". csim_intro.
      sim_apply (sim_let with "(Hcsim1 [//] HΓ)"). iIntros "%vₛ1 %vₜ1 #Hv1".
      sim_asimpl.
      sim_evalₛ (rewrite (bisubst_consₛ _ vₜ1)).
      sim_evalₜ (rewrite (bisubst_consₜ vₛ1)).
      sim_apply ("Hcsim2" with "[//]").
      iApply bisubst_cons_well_formed; iSmash.
    Qed.

    Lemma csim_call Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₜ1 ⩾ eₛ1 [[ X ]] {{# (≈) }} -∗
      SIM eₜ2 ⩾ eₛ2 [[ X ]] {{# (≈) }} -∗
      ( ∀ func vₛ vₜ,
        ⌜func ∈ dom sim_progₛ⌝ -∗
        vₛ ≈ vₜ -∗
        SIM func vₛ ≳ func vₜ [[ X ]] {{ Φ }}
      ) -∗
      SIM eₜ1 eₜ2 ⩾ eₛ1 eₛ2 [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim1 Hcsim2 Hsim". csim_intro.
      sim_apply (sim_call with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ) Hsim").
    Qed.

    Lemma csim_unop Φ op eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaUnop op eₛ ⩾ LambdaUnop op eₜ [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim HΦ". csim_intro.
      sim_apply (sim_unop with "(Hcsim [//] HΓ)").
    Qed.

    Lemma csim_binop Φ op eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ X ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaBinop op eₛ1 eₛ2 ⩾ LambdaBinop op eₜ1 eₜ2 [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim1 Hcsim2 HΦ". csim_intro.
      sim_apply (sim_binop with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ)").
    Qed.

    Lemma csim_if Φ eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      SIM eₛ0 ⩾ eₜ0 [[ X ]] {{# (≈) }} -∗
      ( SIM eₛ1 ⩾ eₜ1 [[ X ]] {{ Φ }} ∧
        SIM eₛ2 ⩾ eₜ2 [[ X ]] {{ Φ }}
      ) -∗
      SIM LambdaIf eₛ0 eₛ1 eₛ2 ⩾ LambdaIf eₜ0 eₜ1 eₜ2 [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim0 Hcsim12". csim_intro.
      sim_apply (sim_if with "(Hcsim0 [//] HΓ)").
      iSplit.
      - iDestruct "Hcsim12" as "(Hcsim1 & _)". iSmash.
      - iDestruct "Hcsim12" as "(_ & Hcsim2)". iSmash.
    Qed.

    Lemma csim_constr Φ tag eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ X ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM &tag eₛ1 eₛ2 ⩾ &tag eₜ1 eₜ2 [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim1 Hcsim2 HΦ". csim_intro.
      sim_apply (sim_constr with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ)").
    Qed.
    Lemma csim_constr_valₜ1 Φ tag eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ vₜ -∗
        (lₜ +ₗ 2) ↦ₜ () -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      SIM eₛ ⩾ &tag eₜ #() [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim HΦ". csim_intro.
      sim_apply (sim_constr_valₜ1 with "(Hcsim [//] HΓ)").
    Qed.
    Lemma csim_constr_valₜ2 Φ tag eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ () -∗
        (lₜ +ₗ 2) ↦ₜ vₜ -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      SIM eₛ ⩾ &tag #() eₜ [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim HΦ". csim_intro.
      sim_apply (sim_constr_valₜ2 with "(Hcsim [//] HΓ)").
    Qed.

    Lemma csim_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ X ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM ![eₛ2] eₛ1 ⩾ ![eₜ2] eₜ1 [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim1 Hcsim2 HΦ". csim_intro.
      sim_apply (derived_rules.sim_load with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ)").
    Qed.

    Lemma csim_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      SIM eₛ1 ⩾ eₜ1 [[ X ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ X ]] {{# (≈) }} -∗
      SIM eₛ3 ⩾ eₜ3 [[ X ]] {{# (≈) }} -∗
      Φ #() #() -∗
      SIM eₛ1 <-[eₛ2]- eₛ3 ⩾ eₜ1 <-[eₜ2]- eₜ3 [[ X ]] {{ Φ }}.
    Proof.
      iIntros "Hcsim1 Hcsim2 Hcsim3 HΦ". csim_intro.
      sim_apply (derived_rules.sim_store with "(Hcsim1 [//] HΓ) (Hcsim2 [//] HΓ) (Hcsim3 [//] HΓ)").
    Qed.
  End csim.

  Section csimv.
    Implicit Types Φ : lambda_val → lambda_val → iProp Σ.

    Lemma csimv_mono Φ1 Φ2 eₛ eₜ :
      (∀ vₛ vₜ, Φ1 vₛ vₜ -∗ Φ2 vₛ vₜ) -∗
      SIM eₛ ⩾ eₜ [[ X ]] {{# Φ1 }} -∗
      SIM eₛ ⩾ eₜ [[ X ]] {{# Φ2 }}.
    Proof.
      iIntros "HΦ Hcsim". csim_intro.
      sim_mono "Hcsim".
    Qed.

    Lemma csimv_cupd Φ eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{# λ vₛ vₜ, |++> Φ vₛ vₜ }} ⊢
      SIM eₛ ⩾ eₜ [[ X ]] {{# Φ }}.
    Proof.
      iIntros "Hcsim". csim_intro.
      sim_cupd. iSmash.
    Qed.
    Lemma csimv_bupd Φ eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{# λ vₛ vₜ, |==> Φ vₛ vₜ }} ⊢
      SIM eₛ ⩾ eₜ [[ X ]] {{# Φ }}.
    Proof.
      iIntros "Hcsim". csim_intro.
      sim_bupd. iSmash.
    Qed.

    Lemma csimv_val Φ v :
      lambda_val_well_formed sim_progₛ v →
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      SIM v ⩾ v [[ X ]] {{# Φ }}.
    Proof.
      iIntros "%Hwf HΦ".
      iApply csim_val; first done.
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma csimv_var Φ x :
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      SIM $x ⩾ $x [[ X ]] {{# Φ }}.
    Proof.
      iIntros "HΦ".
      iApply csim_var.
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma csimv_unop Φ op eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaUnop op eₛ ⩾ LambdaUnop op eₜ [[ X ]] {{# Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      iApply (csim_unop with "Hsim").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma csimv_binop Φ op eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ X ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM LambdaBinop op eₛ1 eₛ2 ⩾ LambdaBinop op eₜ1 eₜ2 [[ X ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      iApply (csim_binop with "Hsim1 Hsim2").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma csimv_constr Φ tag eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ X ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM &tag eₛ1 eₛ2 ⩾ &tag eₜ1 eₜ2 [[ X ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      iApply (csim_constr with "Hsim1 Hsim2").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.
    Lemma csimv_constr_valₜ1 Φ tag eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ vₜ -∗
        (lₜ +ₗ 2) ↦ₜ () -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      SIM eₛ ⩾ &tag eₜ #() [[ X ]] {{# Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      iApply (csim_constr_valₜ1 with "Hsim").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.
    Lemma csimv_constr_valₜ2 Φ tag eₛ eₜ :
      SIM eₛ ⩾ eₜ [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ () -∗
        (lₜ +ₗ 2) ↦ₜ vₜ -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      SIM eₛ ⩾ &tag #() eₜ [[ X ]] {{# Φ }}.
    Proof.
      iIntros "Hsim HΦ".
      iApply (csim_constr_valₜ2 with "Hsim").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma csimv_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      SIM eₛ1 ⩾ eₜ1 [[ X ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ X ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      SIM ![eₛ2] eₛ1 ⩾ ![eₜ2] eₜ1 [[ X ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 HΦ".
      iApply (csim_load with "Hsim1 Hsim2").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.

    Lemma csimv_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      SIM eₛ1 ⩾ eₜ1 [[ X ]] {{# (≈) }} -∗
      SIM eₛ2 ⩾ eₜ2 [[ X ]] {{# (≈) }} -∗
      SIM eₛ3 ⩾ eₜ3 [[ X ]] {{# (≈) }} -∗
      Φ ()%lambda_val ()%lambda_val -∗
      SIM eₛ1 <-[eₛ2]- eₛ3 ⩾ eₜ1 <-[eₜ2]- eₜ3 [[ X ]] {{# Φ }}.
    Proof.
      iIntros "Hsim1 Hsim2 Hsim3 HΦ".
      iApply (csim_store with "Hsim1 Hsim2 Hsim3").
      rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    Qed.
  End csimv.
End sim_GS.
