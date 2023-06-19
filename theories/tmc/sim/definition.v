From iris.proofmode Require Import
  proofmode.

From simuliris Require Import
  prelude.
From simuliris.base_logic Require Export
  lib.sim.heap_bij.
From simuliris.program_logic Require Export
  sim.definition.
From simuliris.language Require Export
  language.

Import heap.notations.

Definition sim_protocol Σ :=
  sim_protocol (iPropI Σ) ectx_language ectx_language.

Class SimGpreS Σ := {
  sim_GpreS_heap_GpreS : SimHeapGpreS Σ loc val loc val ;
  sim_GpreS_heap_bij_GpreS : SimHeapBijGpreS Σ loc loc ;
}.
#[global] Arguments Build_SimGpreS _ {_ _} : assert.
#[local] Existing Instance sim_GpreS_heap_GpreS.
#[local] Existing Instance sim_GpreS_heap_bij_GpreS.

Class SimGS Σ := {
  sim_GS_heap_GS :> SimHeapGS Σ loc val loc val ;
  sim_GS_heap_bij_GS :> SimHeapBijGS Σ loc loc ;
}.
#[global] Arguments Build_SimGS _ {_ _} : assert.

Definition sim_Σ := #[
  sim_heap_Σ loc val loc val ;
  sim_heap_bij_Σ loc loc
].

#[global] Instance subG_sim_GpreS Σ :
  subG sim_Σ Σ →
  SimGpreS Σ.
Proof.
  intros (HsubGₛ & (HsubGₜ & _)%subG_inv)%subG_inv. split; apply _.
Qed.

Section sim_programs.
  Context `{sim_programs : !SimPrograms ectx_language ectx_language}.

  #[global] Instance val_bi_similar `{sim_heap_bij_GS : !SimHeapBijGS Σ loc loc} : BiSimilar (iProp Σ) val val :=
    Build_BiSimilar $ λ vₛ vₜ,
      match vₛ, vₜ with
      | Unit, Unit =>
          True
      | Index idx1, Index idx2 =>
          ⌜idx1 = idx2⌝
      | Int nₛ, Int nₜ =>
          ⌜nₛ = nₜ⌝
      | Bool bₛ, Bool bₜ =>
          ⌜bₛ = bₜ⌝
      | Loc lₛ, Loc lₜ =>
          (lₛ +ₗ 0) ≈ (lₜ +ₗ 0) ∗
          (lₛ +ₗ 1) ≈ (lₜ +ₗ 1) ∗
          (lₛ +ₗ 2) ≈ (lₜ +ₗ 2)
      | Func funcₛ, Func funcₜ =>
          ⌜funcₛ = funcₜ ∧ funcₛ ∈ dom sim_progₛ⌝
      | _, _ =>
          False
      end%I.

  #[global] Instance val_bi_similar_persistent `{sim_GS : !SimGS Σ} vₛ vₜ :
    Persistent (vₛ ≈ vₜ).
  Proof.
    destruct vₛ, vₜ; apply _.
  Qed.

  Lemma val_bi_similar_similar `{sim_GS : !SimGS Σ} vₛ vₜ :
    vₛ ≈ vₜ -∗
    ⌜vₛ ≈ vₜ⌝.
  Proof.
    iIntros "Hv".
    destruct vₛ, vₜ; try iDestruct "Hv" as %[]; done.
  Qed.

  #[global] Instance sim_state `{sim_GS : !SimGS Σ} : SimState (iProp Σ) ectx_language ectx_language :=
    Build_SimState (
      λ (σₛ σₜ : state),
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
