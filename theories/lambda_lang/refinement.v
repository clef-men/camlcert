From simuliris Require Import
  prelude.
From simuliris.program_logic Require Export
  refinement.
From simuliris.lambda_lang Require Export
  language
  metatheory.
From simuliris.lambda_lang Require Import
  notations.

Definition lambda_program_refinement (progₛ progₜ : lambda_program) :=
  map_Forall (λ (func : lambda_function) _,
    ∀ vₛ vₜ : lambda_val,
    lambda_val_well_formed progₛ vₛ →
    vₛ ≈ vₜ →
    expr_refinement progₛ progₜ (func vₛ) (func vₜ)
  ) progₛ.
