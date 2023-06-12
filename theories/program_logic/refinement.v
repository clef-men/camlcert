From simuliris Require Import
  prelude.
From simuliris.common Require Export
  typeclasses.
From simuliris.program_logic Require Export
  language.

Section behaviour.
  Context {Λ : language}.

  Inductive behaviour :=
    | behaviour_converges : expr Λ → state Λ → behaviour
    | behaviour_diverges : behaviour.

  Inductive has_behaviour prog e σ : behaviour → Prop :=
    | has_behaviour_converges e' σ' :
        converges prog e σ e' σ' →
        has_behaviour prog e σ (behaviour_converges e' σ')
    | has_behaviour_diverges :
        diverges prog e σ →
        has_behaviour prog e σ behaviour_diverges.
End behaviour.
#[global] Arguments behaviour : clear implicits.

Section refinement.
  Context `{!Similar (val Λₛ) (val Λₜ)}.

  Inductive behaviour_refinement progₛ progₜ : behaviour Λₛ → behaviour Λₜ → Prop :=
    | behaviour_refinement_val eₛ vₛ σₛ eₜ vₜ σₜ:
        eₛ = of_val vₛ →
        eₜ = of_val vₜ →
        vₛ ≈ vₜ →
        behaviour_refinement progₛ progₜ
          (behaviour_converges eₛ σₛ)
          (behaviour_converges eₜ σₜ)
    | behaviour_refinement_stuck eₛ σₛ eₜ σₜ :
        stuck progₛ eₛ σₛ →
        stuck progₜ eₜ σₜ →
        behaviour_refinement progₛ progₜ
          (behaviour_converges eₛ σₛ)
          (behaviour_converges eₜ σₜ)
    | behaviour_refinement_diverges :
        behaviour_refinement progₛ progₜ
          behaviour_diverges
          behaviour_diverges.

  Definition config_refinement progₛ progₜ eₛ σₛ eₜ σₜ :=
    ∀ bₜ, has_behaviour progₜ eₜ σₜ bₜ →
    ∃ bₛ, has_behaviour progₛ eₛ σₛ bₛ ∧ behaviour_refinement progₛ progₜ bₛ bₜ.

  Definition expr_refinement `{!Empty (state Λₛ)} `{!Empty (state Λₜ)} progₛ progₜ eₛ eₜ :=
    config_refinement progₛ progₜ eₛ ∅ eₜ ∅.
End refinement.
