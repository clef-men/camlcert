From iris.bi Require Import
  fixpoint.

From simuliris Require Import
  prelude.
From simuliris.base_logic Require Export
  lib.cupd.rules.
From simuliris.base_logic Require Import
  lib.cupd.proofmode.
From simuliris.program_logic Require Export
  (* FIXME: remove this dependency *)
  sim.definition.

Section sim_state.
  Context `{sim_programs : !SimPrograms Λₛ Λₜ}.
  Context `{!BiBUpd PROP, !BiAffine PROP}.
  Context `{sim_state : !SimState PROP Λₛ Λₜ}.
  Context (Χ : sim_protocol_O PROP Λₛ Λₜ).

  Notation expr_relation :=
    (expr Λₛ → expr Λₜ → PROP).
  Notation expr_relation_O :=
    (expr_O Λₛ -d> expr_O Λₜ -d> PROP).

  Implicit Types N M I : sim_protocol_O PROP Λₛ Λₜ.
  Implicit Types R : expr_relation_O → expr_relation_O → PROP.

  Definition bisim_body N M : sim_protocol_O PROP Λₛ Λₜ := (
    λ Φ eₛ eₜ,
      ∀ σₛ σₜ,
      sim_state_interp σₛ σₜ ==∗ (
        sim_state_interp σₛ σₜ ∗
        (⌜stuck sim_progₛ eₛ σₛ ∧ stuck sim_progₜ eₜ σₜ⌝ ∨ Φ eₛ eₜ)
      ) ∨ (
        ⌜reducible sim_progₛ eₛ σₛ⌝ ∗
          ∀ eₛ' σₛ',
          ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ==∗
            sim_state_interp σₛ' σₜ ∗
            M Φ eₛ' eₜ
      ) ∨ (
        ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
          ∀ eₜ' σₜ',
          ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
            sim_state_interp σₛ σₜ' ∗
            M Φ eₛ eₜ'
      ) ∨ (
        ⌜reducible sim_progₛ eₛ σₛ ∧ reducible sim_progₜ eₜ σₜ⌝ ∗
          ∀ eₛ' σₛ' eₜ' σₜ',
          ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ' ∧ prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
            sim_state_interp σₛ' σₜ' ∗
            N Φ eₛ' eₜ'
      ) ∨ (
        ∃ Kₛ eₛ' Kₜ eₜ' Ψ,
        ⌜eₛ = Kₛ @@ eₛ' ∧ eₜ = Kₜ @@ eₜ'⌝ ∗
        Χ Ψ eₛ' eₜ' ∗
        sim_state_interp σₛ σₜ ∗
          ∀ eₛ eₜ,
          Ψ eₛ eₜ ++∗
          M Φ (Kₛ @@ eₛ) (Kₜ @@ eₜ)
      )
  )%I.
  #[global] Arguments bisim_body _ _ _%I _ _ : assert.

  #[local] Definition bisim_body' N (M : prodO (prodO expr_relation_O (expr_O Λₛ)) (expr_O Λₜ) → PROP)
  : prodO (prodO expr_relation_O (expr_O Λₛ)) (expr_O Λₜ) → PROP
  :=
    uncurry3 $ bisim_body N $ curry3 M.
  #[local] Definition bisim_inner_def N : sim_protocol_O PROP Λₛ Λₜ :=
    curry3 $ bi_least_fixpoint (bisim_body' N).
  #[local] Definition bisim_inner_aux :
    seal (@bisim_inner_def). Proof. by eexists. Qed.
  Definition bisim_inner :=
    bisim_inner_aux.(unseal).
  #[local] Definition bisim_inner_unseal : @bisim_inner = @bisim_inner_def :=
    bisim_inner_aux.(seal_eq).
  #[global] Arguments bisim_inner _ _%I _ _ : assert.

  #[local] Definition bisim_inner' (N : prodO (prodO expr_relation_O (expr_O Λₛ)) (expr_O Λₜ) → PROP)
  : prodO (prodO expr_relation_O (expr_O Λₛ)) (expr_O Λₜ) → PROP
  :=
    uncurry3 $ bisim_inner $ curry3 N.
  #[local] Definition bisim_def : sim_protocol_O PROP Λₛ Λₜ :=
    curry3 $ bi_greatest_fixpoint bisim_inner'.
  #[local] Definition bisim_aux :
    seal (@bisim_def). Proof. by eexists. Qed.
  Definition bisim :=
    bisim_aux.(unseal).
  #[local] Definition bisim_unseal : @bisim = @bisim_def :=
    bisim_aux.(seal_eq).
  #[global] Arguments bisim _%I _ _ : assert.

  Definition bisimv Φ :=
    bisim (sim_post_vals Φ).
  #[global] Arguments bisimv _%I _ _ : assert.

  Lemma bisimv_unseal Φ :
    bisimv Φ = bisim (sim_post_vals' Φ).
  Proof.
    rewrite /bisimv sim_post_vals_unseal //.
  Qed.
End sim_state.
