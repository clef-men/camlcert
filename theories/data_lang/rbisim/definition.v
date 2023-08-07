From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  rsim.bisubst.
From simuliris.data_lang Require Import
  bisim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (Χ : sim_protocol Σ).
  Implicit Types Γ : bisubst.

  Definition rbisim Φ eₛ eₜ : iProp Σ :=
    ∀ Γ eₛ' eₜ',
    ⌜eₛ' = eₛ.[Γ.ₛ#] ∧ eₜ' = eₜ.[Γ.ₜ#]⌝ -∗
    bisubst_well_formed Γ -∗
    BISIM eₛ' ≃ eₜ' [[ Χ ]] {{ Φ }}.
  #[global] Arguments rbisim _%I (_ _)%data_expr : assert.

  Definition rbisimv Φ eₛ eₜ : iProp Σ :=
    rbisim (sim_post_vals Φ) eₛ eₜ.
  #[global] Arguments rbisimv _%I (_ _)%data_expr : assert.

  Lemma rbisimv_unseal Φ eₛ eₜ :
    rbisimv Φ eₛ eₜ = rbisim (sim_post_vals' Φ) eₛ eₜ.
  Proof.
    rewrite /rbisimv sim_post_vals_unseal //.
  Qed.
End sim_GS.
