From Coq Require Import
  FunctionalExtensionality.

From iris.proofmode Require Import
  proofmode.

From simuliris Require Import
  prelude.
From simuliris.tmc Require Export
  sim.definition.
From simuliris.tmc_lang Require Import
  notations.

Definition bisubst := var → val * val.

Notation "Γ .ₛ" := (fst ∘ Γ)
( at level 5,
  format "Γ .ₛ"
).
Notation "Γ .ₜ" := (snd ∘ Γ)
( at level 5,
  format "Γ .ₜ"
).
Notation "Γ .ₛ#" := (of_val ∘ Γ.ₛ)
( at level 5,
  format "Γ .ₛ#"
).
Notation "Γ .ₜ#" := (of_val ∘ Γ.ₜ)
( at level 5,
  format "Γ .ₜ#"
).

Section sim.
  Context `{sim_programs : !SimPrograms tmc_ectx_lang tmc_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Implicit Types v vₛ vₜ : val.
  Implicit Types Γ : bisubst.

  Lemma bisubst_consₛ vₛ vₜ Γ :
    #vₛ .: Γ.ₛ# = ((vₛ, vₜ) .: Γ).ₛ#.
  Proof.
    apply functional_extensionality. intros. autosubst.
  Qed.
  Lemma bisubst_consₜ vₛ vₜ Γ :
    #vₜ .: Γ.ₜ# = ((vₛ, vₜ) .: Γ).ₜ#.
  Proof.
    apply functional_extensionality. intros. autosubst.
  Qed.

  Definition bisubst_well_formed Γ : iProp Σ :=
    ∀ x, (Γ x).1 ≈ (Γ x).2.

  Lemma bisubst_cons_well_formed vₛ vₜ Γ :
    vₛ ≈ vₜ -∗
    bisubst_well_formed Γ -∗
    bisubst_well_formed ((vₛ, vₜ) .: Γ).
  Proof.
    iIntros "Hv Hwf" ([]) "//".
  Qed.

  #[global] Instance bisubst_inhabited : Inhabited bisubst :=
    populate (λ _, ((), ())%V).
  Lemma bisubst_inhabitant_well_formed :
    ⊢ bisubst_well_formed inhabitant.
  Proof.
    auto.
  Qed.
End sim.
