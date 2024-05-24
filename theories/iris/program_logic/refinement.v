From camlcert Require Import
  prelude.
From camlcert.common Require Export
  typeclasses.
From camlcert.iris.program_logic Require Export
  language.

Section behaviour.
  Context {Λ : language}.

  Inductive behaviour :=
    | behaviour_converges : expr Λ → behaviour
    | behaviour_diverges : behaviour.

  Inductive has_behaviour prog e σ : behaviour → Prop :=
    | has_behaviour_converges e' σ' :
        converges prog e σ e' σ' →
        has_behaviour prog e σ (behaviour_converges e')
    | has_behaviour_diverges :
        diverges prog e σ →
        has_behaviour prog e σ behaviour_diverges.
End behaviour.
#[global] Arguments behaviour : clear implicits.

Section refinement.
  Context `{!Similar (val Λₛ) (val Λₜ)}.

  Inductive behaviour_refinement : behaviour Λₛ → behaviour Λₜ → Prop :=
    | behaviour_refinement_val eₛ vₛ eₜ vₜ :
        eₛ = of_val vₛ →
        eₜ = of_val vₜ →
        vₛ ≈ vₜ →
        behaviour_refinement (behaviour_converges eₛ) (behaviour_converges eₜ)
    | behaviour_refinement_stuck eₛ eₜ :
        to_val eₛ = None →
        to_val eₜ = None →
        behaviour_refinement (behaviour_converges eₛ) (behaviour_converges eₜ)
    | behaviour_refinement_diverges :
        behaviour_refinement behaviour_diverges behaviour_diverges.

  Definition config_refinement progₛ progₜ eₛ σₛ eₜ σₜ :=
    ∀ bₜ, has_behaviour progₜ eₜ σₜ bₜ →
    ∃ bₛ, has_behaviour progₛ eₛ σₛ bₛ ∧ behaviour_refinement bₛ bₜ.

  Definition expr_refinement `{!Empty (state Λₛ)} `{!Empty (state Λₜ)} progₛ progₜ eₛ eₜ :=
    config_refinement progₛ progₜ eₛ ∅ eₜ ∅.
End refinement.
