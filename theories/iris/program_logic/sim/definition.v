From iris.bi Require Import
  fixpoint.

From camlcert Require Import
  prelude.
From camlcert.iris.base_logic Require Export
  lib.cupd.rules.
From camlcert.iris.base_logic Require Import
  lib.cupd.proofmode.
From camlcert.iris.program_logic Require Export
  sim.protocol.

Class SimPrograms Λₛ Λₜ := {
  sim_progₛ : program Λₛ ;
  sim_progₜ : program Λₜ ;
}.
#[global] Arguments Build_SimPrograms {_ _} _ _ : assert.

Class SimState PROP Λₛ Λₜ := {
  sim_state_interp : state Λₛ → state Λₜ → PROP ;
}.
#[global] Arguments Build_SimState {_ _ _} _ : assert.

Section sim_cupd.
  Context `{!BiBUpd PROP, !BiAffine PROP}.
  Context `{sim_state : !SimState PROP Λₛ Λₜ}.

  #[local] Instance sim_cupd_instance : CUpd PROP := (
    λ P,
      ∀ σₛ σₜ,
      sim_state_interp σₛ σₜ ==∗
      sim_state_interp σₛ σₜ ∗ P
  )%I.
  #[global] Program Instance sim_bi_cupd : BiCUpd PROP :=
    Build_BiCUpd _.
  Next Obligation.
    split; rewrite /cupd /sim_cupd_instance.
    - solve_proper.
    - iSmash.
    - iIntros "%P %Q %HPQ HP * Hsi".
      iMod ("HP" with "Hsi") as "(Hsi & HP)".
      iFrame. iApply (HPQ with "HP").
    - iIntros "%P HP * Hsi".
      do 2 iMod ("HP" with "Hsi") as "(Hsi & HP)". iSmash.
    - iIntros "%P %R (HP & HR) * Hsi".
      iMod ("HP" with "Hsi") as "(Hsi & HP)". iSmash.
    - iSmash.
  Qed.

  Lemma sim_cupd_eq P :
    (|++> P) ⊣⊢
      ∀ σₛ σₜ,
      sim_state_interp σₛ σₜ ==∗
      sim_state_interp σₛ σₜ ∗ P.
  Proof.
    iSmash+.
  Qed.

  (* FIXME: we should not need this *)
  #[global] Instance sim_cupd_ne :
    NonExpansive (sim_cupd_instance).
  Proof.
    apply (@cupd_ne _ _ sim_bi_cupd).
  Qed.
End sim_cupd.

#[global] Opaque sim_cupd_instance.

Section sim_post_vals.
  Context {Λₛ Λₜ : ectx_language}.
  Context `{!BiBUpd PROP, !BiAffine PROP}.

  Definition sim_post_vals' (Φ : val_O Λₛ -d> val_O Λₜ -d> PROP) eₛ eₜ : PROP :=
    ∃ vₛ vₜ,
    ⌜eₛ = of_val vₛ ∧ eₜ = of_val vₜ⌝ ∗
    Φ vₛ vₜ.
  #[local] Definition sim_post_vals_aux :
    seal (@sim_post_vals'). Proof. by eexists. Qed.
  Definition sim_post_vals :=
    sim_post_vals_aux.(unseal).
  Definition sim_post_vals_unseal : @sim_post_vals = @sim_post_vals' :=
    sim_post_vals_aux.(seal_eq).
  #[global] Arguments sim_post_vals' _%I _ _ : assert.
  #[global] Arguments sim_post_vals _%I _ _ : assert.
End sim_post_vals.

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

  Definition sim_body N M : sim_protocol_O PROP Λₛ Λₜ := (
    λ Φ eₛ eₜ,
      ∀ σₛ σₜ,
      sim_state_interp σₛ σₜ ==∗ (
        sim_state_interp σₛ σₜ ∗
        (⌜stuck sim_progₛ eₛ σₛ ∧ stuck sim_progₜ eₜ σₜ⌝ ∨ Φ eₛ eₜ)
      ) ∨ (
        ∃ eₛ' σₛ',
        ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
        sim_state_interp σₛ' σₜ ∗
        M Φ eₛ' eₜ
      ) ∨ (
        ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
          ∀ eₜ' σₜ',
          ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗ (
            sim_state_interp σₛ σₜ' ∗
            M Φ eₛ eₜ'
          ) ∨ (
            ∃ eₛ' σₛ',
            ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
            sim_state_interp σₛ' σₜ' ∗
            N Φ eₛ' eₜ'
          )
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
  #[global] Arguments sim_body _ _ _%I _ _ : assert.

  #[local] Definition sim_body' N (M : prodO (prodO expr_relation_O (expr_O Λₛ)) (expr_O Λₜ) → PROP)
  : prodO (prodO expr_relation_O (expr_O Λₛ)) (expr_O Λₜ) → PROP
  :=
    uncurry3 $ sim_body N $ curry3 M.
  #[local] Definition sim_inner_def N : sim_protocol_O PROP Λₛ Λₜ :=
    curry3 $ bi_least_fixpoint (sim_body' N).
  #[local] Definition sim_inner_aux :
    seal (@sim_inner_def). Proof. by eexists. Qed.
  Definition sim_inner :=
    sim_inner_aux.(unseal).
  #[local] Definition sim_inner_unseal : @sim_inner = @sim_inner_def :=
    sim_inner_aux.(seal_eq).
  #[global] Arguments sim_inner _ _%I _ _ : assert.

  #[local] Definition sim_inner' (N : prodO (prodO expr_relation_O (expr_O Λₛ)) (expr_O Λₜ) → PROP)
  : prodO (prodO expr_relation_O (expr_O Λₛ)) (expr_O Λₜ) → PROP
  :=
    uncurry3 $ sim_inner $ curry3 N.
  #[local] Definition sim_def : sim_protocol_O PROP Λₛ Λₜ :=
    curry3 $ bi_greatest_fixpoint sim_inner'.
  #[local] Definition sim_aux :
    seal (@sim_def). Proof. by eexists. Qed.
  Definition sim :=
    sim_aux.(unseal).
  #[local] Definition sim_unseal : @sim = @sim_def :=
    sim_aux.(seal_eq).
  #[global] Arguments sim _%I _ _ : assert.

  Definition simv Φ :=
    sim (sim_post_vals Φ).
  #[global] Arguments simv _%I _ _ : assert.

  Lemma simv_unseal Φ :
    simv Φ = sim (sim_post_vals' Φ).
  Proof.
    rewrite /simv sim_post_vals_unseal //.
  Qed.
End sim_state.
