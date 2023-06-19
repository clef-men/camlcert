From simuliris Require Import
  prelude.
From simuliris.tmc Require Export
  csim.bisubst.
From simuliris.tmc Require Import
  sim.notations.

Section sim.
  Context `{sim_programs : !SimPrograms ectx_language ectx_language}.
  Context `{sim_GS : !SimGS Σ}.
  Context (X : sim_protocol Σ).

  Definition csimv Φ eₛ eₜ : iProp Σ :=
    ∀ Γ eₛ' eₜ',
    ⌜eₛ' = eₛ.[Γ.ₛ#] ∧ eₜ' = eₜ.[Γ.ₜ#]⌝ -∗
    bisubst_well_formed Γ -∗
    SIM eₛ' ≳ eₜ' [[ X ]] [[ Φ ]].
  #[global] Arguments csimv _%I _%E _%E : assert.
End sim.
