From simuliris Require Import
  prelude.
From simuliris.iris.program_logic Require Export
  refinement.
From simuliris.data_lang Require Export
  language
  metatheory.
From simuliris.data_lang Require Import
  notations.

Definition data_program_refinement (progₛ progₜ : data_program) :=
  map_Forall (λ (func : data_function) _,
    ∀ vₛ vₜ : data_val,
    data_val_well_formed progₛ vₛ →
    vₛ ≈ vₜ →
    expr_refinement progₛ progₜ (func vₛ) (func vₜ)
  ) progₛ.
