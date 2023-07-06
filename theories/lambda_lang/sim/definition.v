From iris.proofmode Require Import
  proofmode.

From simuliris Require Import
  prelude.
From simuliris.base_logic Require Export
  lib.sim.heap_bij.
From simuliris.program_logic Require Export
  sim.definition.
From simuliris.lambda_lang Require Export
  language.

Import heap.notations.

Definition sim_protocol Σ :=
  sim_protocol (iPropI Σ) lambda_ectx_lang lambda_ectx_lang.

Class SimGpreS Σ := {
  sim_GpreS_heap_GpreS : SimHeapGpreS Σ loc lambda_val loc lambda_val ;
  sim_GpreS_heap_bij_GpreS : SimHeapBijGpreS Σ loc loc ;
}.
#[global] Arguments Build_SimGpreS _ {_ _} : assert.
#[local] Existing Instance sim_GpreS_heap_GpreS.
#[local] Existing Instance sim_GpreS_heap_bij_GpreS.

Class SimGS Σ := {
  sim_GS_heap_GS :> SimHeapGS Σ loc lambda_val loc lambda_val ;
  sim_GS_heap_bij_GS :> SimHeapBijGS Σ loc loc ;
}.
#[global] Arguments Build_SimGS _ {_ _} : assert.

Definition sim_Σ := #[
  sim_heap_Σ loc lambda_val loc lambda_val ;
  sim_heap_bij_Σ loc loc
].

#[global] Instance subG_sim_GpreS Σ :
  subG sim_Σ Σ →
  SimGpreS Σ.
Proof.
  intros (HsubGₛ & (HsubGₜ & _)%subG_inv)%subG_inv. split; apply _.
Qed.

Section sim_programs.
  Context `{sim_programs : !SimPrograms lambda_ectx_lang lambda_ectx_lang}.

  #[global] Instance lambda_val_bi_similar `{sim_heap_bij_GS : !SimHeapBijGS Σ loc loc} : BiSimilar (iProp Σ) lambda_val lambda_val :=
    Build_BiSimilar $ λ vₛ vₜ,
      match vₛ, vₜ with
      | LambdaUnit, LambdaUnit =>
          True
      | LambdaIndex idx1, LambdaIndex idx2 =>
          ⌜idx1 = idx2⌝
      | LambdaTag tagₛ, LambdaTag tagₜ =>
          ⌜tagₛ = tagₜ⌝
      | LambdaInt nₛ, LambdaInt nₜ =>
          ⌜nₛ = nₜ⌝
      | LambdaBool bₛ, LambdaBool bₜ =>
          ⌜bₛ = bₜ⌝
      | LambdaLoc lₛ, LambdaLoc lₜ =>
          (lₛ +ₗ 0) ≈ (lₜ +ₗ 0) ∗
          (lₛ +ₗ 1) ≈ (lₜ +ₗ 1) ∗
          (lₛ +ₗ 2) ≈ (lₜ +ₗ 2)
      | LambdaFunc funcₛ, LambdaFunc funcₜ =>
          ⌜funcₛ = funcₜ ∧ funcₛ ∈ dom sim_progₛ⌝
      | _, _ =>
          False
      end%I.

  #[global] Instance sim_state `{sim_GS : !SimGS Σ} : SimState (iProp Σ) lambda_ectx_lang lambda_ectx_lang :=
    Build_SimState (
      λ (σₛ σₜ : lambda_state),
        sim_heap_interpₛ σₛ ∗
        sim_heap_interpₜ σₜ ∗
        sim_heap_bij_inv
    )%I.

  Lemma sim_init `{sim_GpreS : !SimGpreS Σ} σₛ σₜ :
    ⊢ |==>
      ∃ sim_GS : SimGS Σ,
      sim_state_interp σₛ σₜ ∗
      ([∗ map] lₛ ↦ vₛ ∈ σₛ, lₛ ↦ₛ vₛ) ∗
      ([∗ map] lₛ ↦ _ ∈ σₛ, meta_tokenₛ lₛ ⊤) ∗
      ([∗ map] lₜ ↦ vₜ ∈ σₜ, lₜ ↦ₜ vₜ) ∗
      ([∗ map] lₜ ↦ _ ∈ σₜ, meta_tokenₜ lₜ ⊤).
  Proof.
    iMod (sim_heap_init σₛ σₜ) as "(%sim_heap_GS & Hheapₛ & Hmapstoₛ & Hmetasₛ & Hheapₜ & Hmapstoₜ & Hmetasₜ)".
    iMod sim_heap_bij_init as "(%sim_heap_bij_GS & Hbij)".
    iExists (Build_SimGS Σ). auto with iFrame.
  Qed.
End sim_programs.
