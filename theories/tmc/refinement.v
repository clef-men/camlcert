From simuliris Require Import
  prelude.
From simuliris.program_logic Require Import
  refinement.
From simuliris.language Require Export
  language.

Definition program_refinement progₛ progₜ :=
  map_Forall (λ func _,
    ∀ vₛ vₜ,
    vₛ ≈ vₜ →
    expr_refinement progₛ (func vₛ) progₜ (func vₜ)
  ) progₛ.
