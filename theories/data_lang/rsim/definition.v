From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  rsim.bisubst.
From simuliris.data_lang Require Import
  sim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (Χ : sim_protocol Σ).

  Implicit Types Γ : bisubst.

  Definition rsim Φ eₛ eₜ : iProp Σ :=
    ∀ Γ eₛ' eₜ',
    ⌜eₛ' = eₛ.[Γ.ₛ#] ∧ eₜ' = eₜ.[Γ.ₜ#]⌝ -∗
    bisubst_well_formed Γ -∗
    SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}.
  #[global] Arguments rsim _%I (_ _)%data_expr : assert.

  Definition rsimv Φ eₛ eₜ : iProp Σ :=
    rsim (sim_post_vals Φ) eₛ eₜ.
  #[global] Arguments rsimv _%I (_ _)%data_expr : assert.

  Lemma rsimv_unseal Φ eₛ eₜ :
    rsimv Φ eₛ eₜ = rsim (sim_post_vals' Φ) eₛ eₜ.
  Proof.
    rewrite /rsimv sim_post_vals_unseal //.
  Qed.
End sim_GS.
