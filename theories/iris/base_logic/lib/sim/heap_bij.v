From iris.base_logic Require Export
  lib.iprop.
From iris.base_logic Require Import
  lib.gset_bij.

From camlcert Require Import
  prelude.
From camlcert.common Require Export
  typeclasses.
From camlcert.iris Require Import
  proofmode.
From camlcert.iris.base_logic Require Export
  lib.sim.heap.

Import heap.notations.

Class SimHeapBijGpreS Σ locₛ locₜ `{Countable locₛ, Countable locₜ} := {
  sim_heap_bij_GpreS_bij_G : gset_bijG Σ locₛ locₜ ;
}.
#[global] Arguments Build_SimHeapBijGpreS _ _ _ {_ _ _ _ _} : assert.
#[local] Existing Instance sim_heap_bij_GpreS_bij_G.

Class SimHeapBijGS Σ locₛ locₜ `{Countable locₛ, Countable locₜ} := {
  sim_heap_bij_GS_bij_G : gset_bijG Σ locₛ locₜ ;
  sim_heap_bij_GS_name : gname ;
}.
#[global] Arguments Build_SimHeapBijGS _ _ _ {_ _ _ _ _} _ : assert.
#[local] Existing Instance sim_heap_bij_GS_bij_G.

Definition sim_heap_bij_Σ locₛ locₜ `{Countable locₛ, Countable locₜ} := #[
  gset_bijΣ locₛ locₜ
].

#[global] Instance subG_sim_heap_bij_GpreS Σ locₛ locₜ `{Countable locₜ, Countable locₛ} :
  subG (sim_heap_bij_Σ locₛ locₜ) Σ →
  SimHeapBijGpreS Σ locₛ locₜ.
Proof.
  own.solve_inG.
Qed.

Section sim_heap_bij_GS.
  Context `{sim_heap_GS : SimHeapGS Σ locₛ valₛ locₜ valₜ}.
  Context `{sim_heap_bij_GS : !SimHeapBijGS Σ locₛ locₜ}.

  Implicit Types lₛ : locₛ.
  Implicit Types lₜ : locₜ.
  Implicit Types vₛ : valₛ.
  Implicit Types vₜ : valₜ.

  Definition sim_heap_bij_auth (bij : gset (locₛ * locₜ)) :=
    gset_bij_own_auth sim_heap_bij_GS_name (DfracOwn 1) bij.

  Definition sim_heap_bij_elem lₛ lₜ :=
    gset_bij_own_elem sim_heap_bij_GS_name lₛ lₜ.
  #[global] Instance sim_heap_bij_bi_similar : BiSimilar _ locₛ locₜ :=
    Build_BiSimilar sim_heap_bij_elem.

  #[global] Instance sim_heap_bij_auth_timeless bij :
    Timeless (sim_heap_bij_auth bij).
  Proof.
    apply _.
  Qed.
  #[global] Instance sim_heap_bij_elem_timeless lₛ lₜ :
    Timeless (lₛ ≈ lₜ).
  Proof.
    apply _.
  Qed.
  #[global] Instance sim_heap_bij_elem_persistent lₛ lₜ :
    Persistent (lₛ ≈ lₜ).
  Proof.
    apply _.
  Qed.

  Lemma sim_heap_bij_agree lₛ1 lₛ2 lₜ1 lₜ2 :
    lₛ1 ≈ lₜ1 -∗
    lₛ2 ≈ lₜ2 -∗
    ⌜lₛ1 = lₛ2 ↔ lₜ1 = lₜ2⌝.
  Proof.
    apply gset_bij_own_elem_agree.
  Qed.

  Lemma sim_heap_bij_func lₛ lₜ1 lₜ2 :
    lₛ ≈ lₜ1 -∗
    lₛ ≈ lₜ2 -∗
    ⌜lₜ1 = lₜ2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (sim_heap_bij_agree with "H1 H2") as %<-. done.
  Qed.

  Lemma sim_heap_bij_inj lₛ1 lₛ2 lₜ :
    lₛ1 ≈ lₜ -∗
    lₛ2 ≈ lₜ -∗
    ⌜lₛ1 = lₛ2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (sim_heap_bij_agree with "H1 H2") as %->. done.
  Qed.

  Section val_bi_similar.
    Context `{!BiSimilar (iProp Σ) valₛ valₜ}.

    Definition sim_heap_bij_tie lₛ lₜ : iProp Σ :=
      ∃ vₛ vₜ,
      lₛ ↦ₛ vₛ ∗ lₜ ↦ₜ vₜ ∗ vₛ ≈ vₜ.
    #[global] Instance sim_heap_bij_bi_tie : BiTie (iProp Σ) locₛ locₜ :=
      Build_BiTie sim_heap_bij_tie.

    Definition sim_heap_bij_inv : iProp Σ :=
      ∃ bij,
      sim_heap_bij_auth bij ∗
      [∗ set] p ∈ bij, p.1 ⋈ p.2.

    Lemma sim_heap_bij_tie_eq lₛ lₜ :
      lₛ ⋈ lₜ ⊣⊢
        ∃ vₛ vₜ,
        lₛ ↦ₛ vₛ ∗ lₜ ↦ₜ vₜ ∗ vₛ ≈ vₜ.
    Proof.
      done.
    Qed.
    Lemma sim_heap_bij_tie_eq_1 lₛ lₜ :
      lₛ ⋈ lₜ ⊢
        ∃ vₛ vₜ,
        lₛ ↦ₛ vₛ ∗ lₜ ↦ₜ vₜ ∗ vₛ ≈ vₜ.
    Proof.
      rewrite sim_heap_bij_tie_eq. auto.
    Qed.
    Lemma sim_heap_bij_tie_eq_2 lₛ vₛ lₜ vₜ :
      lₛ ↦ₛ vₛ -∗
      lₜ ↦ₜ vₜ -∗
      vₛ ≈ vₜ -∗
      lₛ ⋈ lₜ.
    Proof.
      rewrite sim_heap_bij_tie_eq. auto with iFrame.
    Qed.

    Lemma sim_heap_bij_tie_exclusiveₛ lₛ lₜ1 lₜ2 :
      lₛ ⋈ lₜ1 -∗
      lₛ ⋈ lₜ2 -∗
      False.
    Proof.
      iIntros "(%vₛ1 & %vₜ1 & Hmapsto1 & _) (%vₛ2 & %vₜ2 & Hmapsto2 & _)".
      iApply (mapstoₛ_exclusive with "Hmapsto1 Hmapsto2").
    Qed.
    Lemma sim_heap_bij_tie_exclusiveₜ lₛ1 lₛ2 lₜ :
      lₛ1 ⋈ lₜ -∗
      lₛ2 ⋈ lₜ -∗
      False.
    Proof.
      iIntros "(%vₛ1 & %vₜ1 & _ & Hmapsto1 & _) (%vₛ2 & %vₜ2 & _ & Hmapsto2 & _)".
      iApply (mapstoₜ_exclusive with "Hmapsto1 Hmapsto2").
    Qed.

    Lemma sim_heap_bij_access lₛ lₜ :
      sim_heap_bij_inv -∗
      lₛ ≈ lₜ -∗
        lₛ ⋈ lₜ ∗
        (lₛ ⋈ lₜ -∗ sim_heap_bij_inv).
    Proof.
      iIntros "(%bij & Hauth & Hbij) #Helem".
      iDestruct (gset_bij_elem_of with "Hauth Helem") as %?.
      iDestruct (big_sepS_elem_of_acc with "Hbij") as "(Htie & Hbij)"; first done.
      iFrame. iIntros "Htie". iExists bij. iFrame. iApply ("Hbij" with "Htie").
    Qed.

    Lemma sim_heap_bij_insert lₛ lₜ :
      sim_heap_bij_inv -∗
      lₛ ⋈ lₜ ==∗
        sim_heap_bij_inv ∗
        lₛ ≈ lₜ.
    Proof.
      iIntros "(%bij & Hauth & Hbij) Htie".
      iAssert ⌜∀ lₛ', (lₛ', lₜ) ∉ bij⌝%I as %?.
      { iIntros "%lₛ' %".
        iDestruct (big_sepS_elem_of with "Hbij") as "Htie'"; first done.
        iApply (sim_heap_bij_tie_exclusiveₜ with "Htie Htie'").
      }
      iAssert ⌜∀ lₜ', (lₛ, lₜ') ∉ bij⌝%I as %?.
      { iIntros "%lₜ' %".
        iDestruct (big_sepS_elem_of with "Hbij") as "Htie'"; first done.
        iApply (sim_heap_bij_tie_exclusiveₛ with "Htie Htie'").
      }
      iMod (gset_bij_own_extend lₛ lₜ with "Hauth") as "(Hauth & Helem)"; [done.. |].
      iFrame. iExists _. iFrame.
      iApply big_sepS_insert; first done. iFrame. done.
    Qed.
  End val_bi_similar.
End sim_heap_bij_GS.

Section sim_heap_bij_init.
  Context `{sim_heap_GS : SimHeapGS Σ locₛ valₛ locₜ valₜ}.
  Context `{sim_heap_bij_GpreS : !SimHeapBijGpreS Σ locₛ locₜ}.
  Context `{∀ `{!SimHeapBijGS Σ locₛ locₜ}, BiSimilar (iProp Σ) valₛ valₜ}.

  Lemma sim_heap_bij_init_names :
    ⊢ |==>
      ∃ γ : gname,
      let sim_heap_bij_GS := Build_SimHeapBijGS Σ locₛ locₜ γ in
      sim_heap_bij_inv.
  Proof.
    iMod (gset_bij_own_alloc_empty) as "(%γ & Hinv)".
    iExists γ, ∅. iSplitL "Hinv"; first by iApply "Hinv".
    iApply big_sepS_empty. done.
  Qed.

  Lemma sim_heap_bij_init :
    ⊢ |==>
      ∃ sim_heap_bij_GS : SimHeapBijGS Σ locₛ locₜ,
      sim_heap_bij_inv.
  Proof.
    iMod (sim_heap_bij_init_names) as "(%γ & Hinv)".
    iExists _. iFrame. done.
  Qed.
End sim_heap_bij_init.

#[global] Opaque sim_heap_bij_auth.
#[global] Opaque sim_heap_bij_elem.
#[global] Opaque sim_heap_bij_tie.
#[global] Opaque sim_heap_bij_inv.
