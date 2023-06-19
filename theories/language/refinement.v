From simuliris Require Import
  prelude.
From simuliris.program_logic Require Export
  refinement.
From simuliris.language Require Export
  language
  well_formed.
From simuliris.language Require Import
  notations.

Definition program_refinement (progₛ progₜ : program) :=
  map_Forall (λ (func : function) _,
    ∀ vₛ vₜ : val,
    val_well_formed progₛ vₛ →
    vₛ ≈ vₜ →
    expr_refinement progₛ progₜ (func vₛ) (func vₜ)
  ) progₛ.
