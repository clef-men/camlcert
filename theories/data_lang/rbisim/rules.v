From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  metatheory
  bisim.derived_rules
  rbisim.definition.
From simuliris.data_lang Require Import
  bisim.proofmode
  rbisim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (Χ : sim_protocol Σ).
  Implicit Types func : data_function.
  Implicit Types tag : data_tag.
  Implicit Types v vₛ vₜ : data_val.
  Implicit Types e eₛ eₜ : data_expr.

  #[local] Ltac rbisim_intro :=
    iIntros "%Γ % % (-> & ->) #HΓ"; bisim_simpl.

  Section rbisim.
    Implicit Types Φ : data_expr → data_expr → iProp Σ.

    Lemma rbisim_mono Φ1 Φ2 eₛ eₜ :
      ( ∀ eₛ eₜ,
        Φ1 eₛ eₜ -∗
        Φ2 eₛ eₜ
      ) -∗
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ Φ1 }} -∗
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      iIntros "HΦ Hrbisim". rbisim_intro.
      bisim_mono "Hrbisim".
    Qed.

    Lemma cupd_rbisim Φ eₛ eₜ :
      (|++> BISIM eₛ ≅ eₜ [[ Χ ]] {{ Φ }}) ⊢
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim". rbisim_intro.
      iMod "Hrbisim". iSmash.
    Qed.
    Lemma bupd_rbisim Φ eₛ eₜ :
      (|==> BISIM eₛ ≅ eₜ [[ Χ ]] {{ Φ }}) ⊢
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim". rbisim_intro.
      iMod "Hrbisim". iSmash.
    Qed.

    Lemma rbisim_cupd Φ eₛ eₜ :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }} ⊢
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim". rbisim_intro.
      bisim_cupd. iSmash.
    Qed.
    Lemma rbisim_bupd Φ eₛ eₜ :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }} ⊢
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim". rbisim_intro.
      bisim_bupd. iSmash.
    Qed.

    Lemma rbisim_val Φ v :
      data_val_well_formed sim_progₛ v →
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      BISIM v ≅ v [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "%Hwf HΦ". rbisim_intro.
      bisim_post. iApply "HΦ". data_expr_simplifier.
    Qed.

    Lemma rbisim_var Φ x :
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      BISIM $x ≅ $x [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "HΦ". rbisim_intro.
      bisim_post.
    Qed.

    Lemma rbisim_let Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₜ1 ≅ eₛ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      BISIM eₜ2 ≅ eₛ2 [[ Χ ]] {{ Φ }} -∗
      BISIM let: eₜ1 in eₜ2 ≅ let: eₛ1 in eₛ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim1 Hrbisim2". rbisim_intro.
      bisim_apply (bisim_let with "(Hrbisim1 [//] HΓ)"). iIntros "%vₛ1 %vₜ1 #Hv1".
      bisim_asimpl.
      bisim_evalₛ (rewrite (bisubst_consₛ _ vₜ1)).
      bisim_evalₜ (rewrite (bisubst_consₜ vₛ1)).
      bisim_apply ("Hrbisim2" with "[//]").
      iApply bisubst_cons_well_formed; iSmash.
    Qed.

    Lemma rbisim_call Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₜ1 ≅ eₛ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      BISIM eₜ2 ≅ eₛ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ func annot vₛ vₜ,
        ⌜func ∈ dom sim_progₛ⌝ -∗
        vₛ ≈ vₜ -∗
        BISIM (DataFunc func annot) vₛ ≃ (DataFunc func annot) vₜ [[ Χ ]] {{ Φ }}
      ) -∗
      BISIM eₜ1 eₜ2 ≅ eₛ1 eₛ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim1 Hrbisim2 Hbisim". rbisim_intro.
      bisim_apply (bisim_call with "(Hrbisim1 [//] HΓ) (Hrbisim2 [//] HΓ) Hbisim").
    Qed.

    Lemma rbisim_unop Φ op eₛ eₜ :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM DataUnop op eₛ ≅ DataUnop op eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim HΦ". rbisim_intro.
      bisim_apply (bisim_unop with "(Hrbisim [//] HΓ)").
    Qed.

    Lemma rbisim_if Φ eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      BISIM eₛ0 ≅ eₜ0 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( BISIM eₛ1 ≅ eₜ1 [[ Χ ]] {{ Φ }} ∧
        BISIM eₛ2 ≅ eₜ2 [[ Χ ]] {{ Φ }}
      ) -∗
      BISIM DataIf eₛ0 eₛ1 eₛ2 ≅ DataIf eₜ0 eₜ1 eₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim0 Hrbisim12". rbisim_intro.
      bisim_apply (bisim_if with "(Hrbisim0 [//] HΓ)").
      iSplit.
      - iDestruct "Hrbisim12" as "(Hrbisim1 & _)". iSmash.
      - iDestruct "Hrbisim12" as "(_ & Hrbisim2)". iSmash.
    Qed.

    Lemma rbisim_constr_valₜ1 Φ tag eₛ vₜ1 eₜ :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ vₜ1 -∗
        (lₜ +ₗ 2) ↦ₜ vₜ -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      BISIM eₛ ≅ &tag vₜ1 eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim HΦ". rbisim_intro.
      bisim_apply (bisim_constr_valₜ1 with "(Hrbisim [//] HΓ)").
    Qed.
    Lemma rbisim_constr_valₜ2 Φ tag eₛ eₜ vₜ2 :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ vₜ -∗
        (lₜ +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      BISIM eₛ ≅ &tag eₜ vₜ2 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim HΦ". rbisim_intro.
      bisim_apply (bisim_constr_valₜ2 with "(Hrbisim [//] HΓ)").
    Qed.

    Lemma rbisim_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₛ1 ≅ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      BISIM eₛ2 ≅ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM ![eₛ2] eₛ1 ≅ ![eₜ2] eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim1 Hrbisim2 HΦ". rbisim_intro.
      bisim_apply (derived_rules.bisim_load with "(Hrbisim1 [//] HΓ) (Hrbisim2 [//] HΓ)").
    Qed.

    Lemma rbisim_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      BISIM eₛ1 ≅ eₜ1 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      BISIM eₛ2 ≅ eₜ2 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      BISIM eₛ3 ≅ eₜ3 [[ Χ ]] {{ sim_post_vals' (≈) }} -∗
      Φ #() #() -∗
      BISIM eₛ1 <-[eₛ2]- eₛ3 ≅ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "Hrbisim1 Hrbisim2 Hrbisim3 HΦ". rbisim_intro.
      bisim_apply (derived_rules.bisim_store with "(Hrbisim1 [//] HΓ) (Hrbisim2 [//] HΓ) (Hrbisim3 [//] HΓ)").
    Qed.
  End rbisim.

  Section rbisimv.
    Implicit Types Φ : data_val → data_val → iProp Σ.

    Lemma rbisimv_mono Φ1 Φ2 eₛ eₜ :
      ( ∀ vₛ vₜ,
        Φ1 vₛ vₜ -∗
        Φ2 vₛ vₜ
      ) -∗
      BISIM eₛ ≅ eₜ [[ Χ ]] {{# Φ1 }} -∗
      BISIM eₛ ≅ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      iIntros "HΦ Hrbisim". rbisim_intro.
      bisim_mono "Hrbisim".
    Qed.

    Lemma rbisimv_cupd Φ eₛ eₜ :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{# λ vₛ vₜ, |++> Φ vₛ vₜ }} ⊢
      BISIM eₛ ≅ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hrbisim". rbisim_intro.
      bisim_cupd. iSmash.
    Qed.
    Lemma rbisimv_bupd Φ eₛ eₜ :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{# λ vₛ vₜ, |==> Φ vₛ vₜ }} ⊢
      BISIM eₛ ≅ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      iIntros "Hrbisim". rbisim_intro.
      bisim_bupd. iSmash.
    Qed.

    Lemma rbisimv_val Φ v :
      data_val_well_formed sim_progₛ v →
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      BISIM v ≅ v [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !rbisimv_unseal.
      iIntros "%Hwf HΦ".
      iApply rbisim_val; first done.
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma rbisimv_var Φ x :
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) ⊢
      BISIM $x ≅ $x [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !rbisimv_unseal.
      iIntros "HΦ".
      iApply rbisim_var.
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma rbisimv_let Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₜ1 ≅ eₛ1 [[ Χ ]] {{# (≈) }} -∗
      BISIM eₜ2 ≅ eₛ2 [[ Χ ]] {{# Φ }} -∗
      BISIM let: eₜ1 in eₜ2 ≅ let: eₛ1 in eₛ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !rbisimv_unseal.
      iIntros "Hrbisim1 Hrbisim2".
      iApply (rbisim_let with "Hrbisim1 Hrbisim2").
    Qed.

    Lemma rbisimv_call Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₜ1 ≅ eₛ1 [[ Χ ]] {{# (≈) }} -∗
      BISIM eₜ2 ≅ eₛ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ func annot vₛ vₜ,
        ⌜func ∈ dom sim_progₛ⌝ -∗
        vₛ ≈ vₜ -∗
        BISIM (DataFunc func annot) vₛ ≃ (DataFunc func annot) vₜ [[ Χ ]] {{# Φ }}
      ) -∗
      BISIM eₜ1 eₜ2 ≅ eₛ1 eₛ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal !rbisimv_unseal.
      iIntros "Hrbisim1 Hrbisim2 HΦ".
      iApply (rbisim_call with "Hrbisim1 Hrbisim2"). iSmash.
    Qed.

    Lemma rbisimv_unop Φ op eₛ eₜ :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM DataUnop op eₛ ≅ DataUnop op eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !rbisimv_unseal.
      iIntros "Hrbisim HΦ".
      iApply (rbisim_unop with "Hrbisim").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma rbisimv_if Φ eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      BISIM eₛ0 ≅ eₜ0 [[ Χ ]] {{# (≈) }} -∗
      ( BISIM eₛ1 ≅ eₜ1 [[ Χ ]] {{# Φ }} ∧
        BISIM eₛ2 ≅ eₜ2 [[ Χ ]] {{# Φ }}
      ) -∗
      BISIM DataIf eₛ0 eₛ1 eₛ2 ≅ DataIf eₜ0 eₜ1 eₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !rbisimv_unseal.
      iIntros "Hrbisim0 Hrbisim12".
      iApply (rbisim_if with "Hrbisim0 Hrbisim12").
    Qed.

    Lemma rbisimv_constr_valₜ1 Φ tag eₛ vₜ1 eₜ :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ vₜ1 -∗
        (lₜ +ₗ 2) ↦ₜ vₜ -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      BISIM eₛ ≅ &tag vₜ1 eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !rbisimv_unseal.
      iIntros "Hrbisim HΦ".
      iApply (rbisim_constr_valₜ1 with "Hrbisim").
      rewrite /sim_post_vals'. iSmash.
    Qed.
    Lemma rbisimv_constr_valₜ2 Φ tag eₛ eₜ vₜ2 :
      BISIM eₛ ≅ eₜ [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ lₜ vₜ,
        (lₜ +ₗ 0) ↦ₜ tag -∗
        (lₜ +ₗ 1) ↦ₜ vₜ -∗
        (lₜ +ₗ 2) ↦ₜ vₜ2 -∗
        vₛ ≈ vₜ -∗
        Φ vₛ lₜ
      ) -∗
      BISIM eₛ ≅ &tag eₜ vₜ2 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !rbisimv_unseal.
      iIntros "Hrbisim HΦ".
      iApply (rbisim_constr_valₜ2 with "Hrbisim").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma rbisimv_load Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      BISIM eₛ1 ≅ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      BISIM eₛ2 ≅ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      ( ∀ vₛ vₜ,
        vₛ ≈ vₜ -∗
        Φ vₛ vₜ
      ) -∗
      BISIM ![eₛ2] eₛ1 ≅ ![eₜ2] eₜ1 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !rbisimv_unseal.
      iIntros "Hrbisim1 Hrbisim2 HΦ".
      iApply (rbisim_load with "Hrbisim1 Hrbisim2").
      rewrite /sim_post_vals'. iSmash.
    Qed.

    Lemma rbisimv_store Φ eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      BISIM eₛ1 ≅ eₜ1 [[ Χ ]] {{# (≈) }} -∗
      BISIM eₛ2 ≅ eₜ2 [[ Χ ]] {{# (≈) }} -∗
      BISIM eₛ3 ≅ eₜ3 [[ Χ ]] {{# (≈) }} -∗
      Φ ()%data_val ()%data_val -∗
      BISIM eₛ1 <-[eₛ2]- eₛ3 ≅ eₜ1 <-[eₜ2]- eₜ3 [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !rbisimv_unseal.
      iIntros "Hrbisim1 Hrbisim2 Hrbisim3 HΦ".
      iApply (rbisim_store with "Hrbisim1 Hrbisim2 Hrbisim3").
      rewrite /sim_post_vals'. iSmash.
    Qed.
  End rbisimv.
End sim_GS.
