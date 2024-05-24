From iris.algebra Require Export
  dfrac.

From iris.bi Require Import
  lib.fractional.
From iris.base_logic Require Import
  lib.gen_heap.

From camlcert Require Import
  prelude.
From camlcert.iris Require Import
  proofmode.

Class SimHeapGpreS Σ locₛ valₛ locₜ valₜ `{Countable locₛ, Countable locₜ} := {
  sim_heap_GpreS_heapₛ_GpreS : gen_heapGpreS locₛ valₛ Σ ;
  sim_heap_GpreS_heapₜ_GpreS : gen_heapGpreS locₜ valₜ Σ ;
}.
#[global] Arguments Build_SimHeapGpreS _ _ _ _ _ {_ _ _ _ _ _} : assert.
#[local] Existing Instance sim_heap_GpreS_heapₛ_GpreS.
#[local] Existing Instance sim_heap_GpreS_heapₜ_GpreS.

Class SimHeapGS Σ locₛ valₛ locₜ valₜ `{Countable locₛ, Countable locₜ} := {
  sim_heap_GS_heapₛ_GS : gen_heapGS locₛ valₛ Σ ;
  sim_heap_GS_heapₜ_GS : gen_heapGS locₜ valₜ Σ ;
}.
#[global] Arguments Build_SimHeapGS _ _ _ _ _ {_ _ _ _ _ _} : assert.

Definition sim_heap_Σ locₛ valₛ locₜ valₜ `{Countable locₛ, Countable locₜ} := #[
  gen_heapΣ locₛ valₛ ;
  gen_heapΣ locₜ valₜ
].

#[global] Instance subG_sim_heap_GpreS Σ locₛ valₛ locₜ valₜ `{Countable locₛ, Countable locₜ} :
  subG (sim_heap_Σ locₛ valₛ locₜ valₜ) Σ →
  SimHeapGpreS Σ locₛ valₛ locₜ valₜ.
Proof.
  intros (HsubGₛ & (HsubGₜ & _)%subG_inv)%subG_inv. split; apply _.
Qed.

Section sim_heap_GS.
  Context `{sim_heap_GS : SimHeapGS Σ locₛ valₛ locₜ valₜ}.

  Definition sim_heap_interpₛ :=
    gen_heap_interp (hG := sim_heap_GS_heapₛ_GS).
  Definition sim_heap_interpₜ :=
    gen_heap_interp (hG := sim_heap_GS_heapₜ_GS).

  Definition mapstoₛ :=
    mapsto (hG := sim_heap_GS_heapₛ_GS).
  Definition mapstoₜ :=
    mapsto (hG := sim_heap_GS_heapₜ_GS).

  Definition meta_tokenₛ :=
    meta_token (hG := sim_heap_GS_heapₛ_GS).
  Definition meta_tokenₜ :=
    meta_token (hG := sim_heap_GS_heapₜ_GS).

  Definition metaₛ `{Countable X} l N (x : X) :=
    meta (hG := sim_heap_GS_heapₛ_GS) l N x.
  Definition metaₜ `{Countable X} l N (x : X) :=
    meta (hG := sim_heap_GS_heapₜ_GS) l N x.
End sim_heap_GS.

Module Import notations.
  Notation "l ↦ₛ{ dq } v" := (
    mapstoₛ l dq v
  )(at level 20,
    format "l  ↦ₛ{ dq }  v"
  ) : bi_scope.
  Notation "l ↦ₛ□ v" :=
    (l ↦ₛ{DfracDiscarded} v)%I
  ( at level 20,
    format "l  ↦ₛ□  v"
  ) : bi_scope.
  Notation "l ↦ₛ{# q } v" :=
    (l ↦ₛ{DfracOwn q} v)%I
  ( at level 20,
    format "l  ↦ₛ{# q }  v"
  ) : bi_scope.
  Notation "l ↦ₛ v" :=
    (l ↦ₛ{#1} v)%I
  ( at level 20,
    format "l  ↦ₛ  v"
  ) : bi_scope.

  Notation "l ↦ₜ{ dq } v" := (
    mapstoₜ l dq v
  )(at level 20,
    format "l  ↦ₜ{ dq }  v"
  ) : bi_scope.
  Notation "l ↦ₜ□ v" :=
    (l ↦ₜ{DfracDiscarded} v)%I
  ( at level 20,
    format "l  ↦ₜ□  v"
  ) : bi_scope.
  Notation "l ↦ₜ{# q } v" :=
    (l ↦ₜ{DfracOwn q} v)%I
  ( at level 20,
    format "l  ↦ₜ{# q }  v"
  ) : bi_scope.
  Notation "l ↦ₜ v" :=
    (l ↦ₜ{#1} v)%I
  ( at level 20,
    format "l  ↦ₜ  v"
  ) : bi_scope.
End notations.

Section sim_heap_GS.
  Context `{sim_heap_GS : SimHeapGS Σ locₛ valₛ locₜ valₜ}.

  #[global] Instance mapstoₛ_timeless l dq v :
    Timeless (l ↦ₛ{dq} v).
  Proof.
    apply _.
  Qed.
  #[global] Instance mapstoₜ_timeless l dq v :
    Timeless (l ↦ₜ{dq} v).
  Proof.
    apply _.
  Qed.

  #[global] Instance mapstoₛ_fractional l v :
    Fractional (λ q, l ↦ₛ{#q} v)%I.
  Proof.
    apply _.
  Qed.
  #[global] Instance mapstoₜ_fractional l v :
    Fractional (λ q, l ↦ₜ{#q} v)%I.
  Proof.
    apply _.
  Qed.

  #[global] Instance mapstoₛ_as_fractional l q v :
    AsFractional (l ↦ₛ{#q} v) (λ q, l ↦ₛ{#q} v)%I q.
  Proof.
    apply _.
  Qed.
  #[global] Instance mapstoₜ_as_fractional l q v :
    AsFractional (l ↦ₜ{#q} v) (λ q, l ↦ₜ{#q} v)%I q.
  Proof.
    apply _.
  Qed.

  #[global] Instance mapstoₛ_persistent l v :
    Persistent (l ↦ₛ□ v).
  Proof.
    apply _.
  Qed.
  #[global] Instance mapstoₜ_persistent l v :
    Persistent (l ↦ₜ□ v).
  Proof.
    apply _.
  Qed.

  #[global] Instance meta_tokenₛ_timeless l N :
    Timeless (meta_tokenₛ l N).
  Proof.
    apply _.
  Qed.
  #[global] Instance meta_tokenₜ_timeless l N :
    Timeless (meta_tokenₜ l N).
  Proof.
    apply _.
  Qed.

  #[global] Instance metaₛ_timeless `{Countable X} l N (x : X) :
    Timeless (metaₛ l N x).
  Proof.
    apply _.
  Qed.
  #[global] Instance metaₜ_timeless `{Countable X} l N (x : X) :
    Timeless (metaₜ l N x).
  Proof.
    apply _.
  Qed.

  #[global] Instance metaₛ_persistent `{Countable X} l N (x : X) :
    Persistent (metaₛ l N x).
  Proof.
    apply _.
  Qed.
  #[global] Instance metaₜ_persistent `{Countable X} l N (x : X) :
    Persistent (metaₜ l N x).
  Proof.
    apply _.
  Qed.

  Lemma mapstoₛ_valid l dq v :
    l ↦ₛ{dq} v ⊢
    ⌜✓ dq⌝.
  Proof.
    apply bi.wand_entails', mapsto_valid.
  Qed.
  Lemma mapstoₜ_valid l dq v :
    l ↦ₜ{dq} v ⊢
    ⌜✓ dq⌝.
  Proof.
    apply bi.wand_entails', mapsto_valid.
  Qed.

  Lemma mapstoₛ_valid_2 l dq1 v1 dq2 v2 :
    l ↦ₛ{dq1} v1 -∗
    l ↦ₛ{dq2} v2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    apply mapsto_valid_2.
  Qed.
  Lemma mapstoₜ_valid_2 l dq1 v1 dq2 v2 :
    l ↦ₜ{dq1} v1 -∗
    l ↦ₜ{dq2} v2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    apply mapsto_valid_2.
  Qed.

  Lemma mapstoₛ_agree l dq1 v1 dq2 v2 :
    l ↦ₛ{dq1} v1 -∗
    l ↦ₛ{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply mapsto_agree.
  Qed.
  Lemma mapstoₜ_agree l dq1 v1 dq2 v2 :
    l ↦ₜ{dq1} v1 -∗
    l ↦ₜ{dq2} v2 -∗
    ⌜v1 = v2⌝.
  Proof.
    apply mapsto_agree.
  Qed.

  Lemma mapstoₛ_combine l dq1 v1 dq2 v2 :
    l ↦ₛ{dq1} v1 -∗
    l ↦ₛ{dq2} v2 -∗
      l ↦ₛ{dq1 ⋅ dq2} v1 ∗
      ⌜v1 = v2⌝.
  Proof.
    apply mapsto_combine.
  Qed.
  Lemma mapstoₜ_combine l dq1 v1 dq2 v2 :
    l ↦ₜ{dq1} v1 -∗
    l ↦ₜ{dq2} v2 -∗
      l ↦ₜ{dq1 ⋅ dq2} v1 ∗
      ⌜v1 = v2⌝.
  Proof.
    apply mapsto_combine.
  Qed.

  Lemma mapstoₛ_frac_ne l1 dq1 v1 l2 dq2 v2 :
    ¬ ✓(dq1 ⋅ dq2) →
    l1 ↦ₛ{dq1} v1 -∗
    l2 ↦ₛ{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply mapsto_frac_ne.
  Qed.
  Lemma mapstoₜ_frac_ne l1 dq1 v1 l2 dq2 v2 :
    ¬ ✓(dq1 ⋅ dq2) →
    l1 ↦ₜ{dq1} v1 -∗
    l2 ↦ₜ{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply mapsto_frac_ne.
  Qed.

  Lemma mapstoₛ_ne l1 v1 l2 dq2 v2 :
    l1 ↦ₛ v1 -∗
    l2 ↦ₛ{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply mapsto_ne.
  Qed.
  Lemma mapstoₜ_ne l1 v1 l2 dq2 v2 :
    l1 ↦ₜ v1 -∗
    l2 ↦ₜ{dq2} v2 -∗
    ⌜l1 ≠ l2⌝.
  Proof.
    apply mapsto_ne.
  Qed.

  Lemma mapstoₛ_exclusive l v1 v2 :
    l ↦ₛ v1 -∗
    l ↦ₛ v2 -∗
    False.
  Proof.
    iIntros "Hmapsto1 Hmapsto2".
    iDestruct (mapstoₛ_valid_2 with "Hmapsto1 Hmapsto2") as %?. naive_solver.
  Qed.
  Lemma mapstoₜ_exclusive l v1 v2 :
    l ↦ₜ v1 -∗
    l ↦ₜ v2 -∗
    False.
  Proof.
    iIntros "Hmapsto1 Hmapsto2".
    iDestruct (mapstoₜ_valid_2 with "Hmapsto1 Hmapsto2") as %?. naive_solver.
  Qed.

  Lemma mapstoₛ_persist l dq v :
     l ↦ₛ{dq} v ⊢ |==>
     l ↦ₛ□ v.
  Proof.
    apply bi.wand_entails', mapsto_persist.
  Qed.
  Lemma mapstoₜ_persist l dq v :
    l ↦ₜ{dq} v ⊢ |==>
    l ↦ₜ□ v.
  Proof.
    apply bi.wand_entails', mapsto_persist.
  Qed.

  Lemma meta_tokenₛ_union_1 l E1 E2 :
    E1 ## E2 →
    meta_tokenₛ l (E1 ∪ E2) ⊢
      meta_tokenₛ l E1 ∗
      meta_tokenₛ l E2.
  Proof.
    intros. apply bi.wand_entails', meta_token_union_1. done.
  Qed.
  Lemma meta_tokenₜ_union_1 l E1 E2 :
    E1 ## E2 →
    meta_tokenₜ l (E1 ∪ E2) ⊢
      meta_tokenₜ l E1 ∗
      meta_tokenₜ l E2.
  Proof.
    intros. apply bi.wand_entails', meta_token_union_1. done.
  Qed.

  Lemma meta_tokenₛ_union_2 l E1 E2 :
    meta_tokenₛ l E1 -∗
    meta_tokenₛ l E2 -∗
    meta_tokenₛ l (E1 ∪ E2).
  Proof.
    apply meta_token_union_2.
  Qed.
  Lemma meta_tokenₜ_union_2 l E1 E2 :
    meta_tokenₜ l E1 -∗
    meta_tokenₜ l E2 -∗
    meta_tokenₜ l (E1 ∪ E2).
  Proof.
    apply meta_token_union_2.
  Qed.

  Lemma meta_tokenₛ_union l E1 E2 :
    E1 ## E2 →
    meta_tokenₛ l (E1 ∪ E2) ⊣⊢
      meta_tokenₛ l E1 ∗
      meta_tokenₛ l E2.
  Proof.
    apply meta_token_union.
  Qed.
  Lemma meta_tokenₜ_union l E1 E2 :
    E1 ## E2 →
    meta_tokenₜ l (E1 ∪ E2) ⊣⊢
      meta_tokenₜ l E1 ∗
      meta_tokenₜ l E2.
  Proof.
    apply meta_token_union.
  Qed.

  Lemma meta_tokenₛ_difference l E1 E2 :
    E1 ⊆ E2 →
    meta_tokenₛ l E2 ⊣⊢
      meta_tokenₛ l E1 ∗
      meta_tokenₛ l (E2 ∖ E1).
  Proof.
    apply meta_token_difference.
  Qed.
  Lemma meta_tokenₜ_difference l E1 E2 :
    E1 ⊆ E2 →
    meta_tokenₜ l E2 ⊣⊢
      meta_tokenₜ l E1 ∗
      meta_tokenₜ l (E2 ∖ E1).
  Proof.
    apply meta_token_difference.
  Qed.

  Lemma metaₛ_agree `{Countable X} l i (x1 x2 : X) :
    metaₛ l i x1 -∗
    metaₛ l i x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    apply meta_agree.
  Qed.
  Lemma metaₜ_agree `{Countable X} l i (x1 x2 : X) :
    metaₜ l i x1 -∗
    metaₜ l i x2 -∗
    ⌜x1 = x2⌝.
  Proof.
    apply meta_agree.
  Qed.

  Lemma metaₛ_set `{Countable X} E l (x : X) N :
    ↑ N ⊆ E →
    meta_tokenₛ l E ⊢ |==>
    metaₛ l N x.
  Proof.
    intros. apply bi.wand_entails', meta_set. done.
  Qed.
  Lemma metaₜ_set `{Countable X} E l (x : X) N :
    ↑ N ⊆ E →
    meta_tokenₜ l E ⊢ |==>
    metaₜ l N x.
  Proof.
    intros. apply bi.wand_entails', meta_set. done.
  Qed.

  Lemma sim_heap_allocₛ σ l v :
    σ !! l = None →
    sim_heap_interpₛ σ ⊢ |==>
      sim_heap_interpₛ (<[l := v]> σ) ∗
      l ↦ₛ v ∗
      meta_tokenₛ l ⊤.
  Proof.
    intros. apply bi.wand_entails', gen_heap_alloc. done.
  Qed.
  Lemma sim_heap_allocₜ σ l v :
    σ !! l = None →
    sim_heap_interpₜ σ ⊢ |==>
      sim_heap_interpₜ (<[l := v]> σ) ∗
      l ↦ₜ v ∗
      meta_tokenₜ l ⊤.
  Proof.
    intros. apply bi.wand_entails', gen_heap_alloc. done.
  Qed.

  Lemma sim_heap_alloc_bigₛ σ σ' :
    σ' ##ₘ σ →
    sim_heap_interpₛ σ ⊢ |==>
      sim_heap_interpₛ (σ' ∪ σ) ∗
      ([∗ map] l ↦ v ∈ σ', l ↦ₛ v) ∗
      ([∗ map] l ↦ _ ∈ σ', meta_tokenₛ l ⊤).
  Proof.
    intros. apply bi.wand_entails', gen_heap_alloc_big. done.
  Qed.
  Lemma sim_heap_alloc_bigₜ σ σ' :
    σ' ##ₘ σ →
    sim_heap_interpₜ σ ⊢ |==>
      sim_heap_interpₜ (σ' ∪ σ) ∗
      ([∗ map] l ↦ v ∈ σ', l ↦ₜ v) ∗
      ([∗ map] l ↦ _ ∈ σ', meta_tokenₜ l ⊤).
  Proof.
    intros. apply bi.wand_entails', gen_heap_alloc_big. done.
  Qed.

  Lemma sim_heap_validₛ σ l dq v :
    sim_heap_interpₛ σ -∗
    l ↦ₛ{dq} v -∗
    ⌜σ !! l = Some v⌝.
  Proof.
    apply gen_heap_valid.
  Qed.
  Lemma sim_heap_validₜ σ l dq v :
    sim_heap_interpₜ σ -∗
    l ↦ₜ{dq} v -∗
    ⌜σ !! l = Some v⌝.
  Proof.
    apply gen_heap_valid.
  Qed.

  Lemma sim_heap_updateₛ σ l v v' :
    sim_heap_interpₛ σ -∗
    l ↦ₛ v' ==∗
      sim_heap_interpₛ (<[l := v]> σ) ∗
      l ↦ₛ v.
  Proof.
    apply gen_heap_update.
  Qed.
  Lemma sim_heap_updateₜ σ l v v' :
    sim_heap_interpₜ σ -∗
    l ↦ₜ v' ==∗
      sim_heap_interpₜ (<[l := v]> σ) ∗
      l ↦ₜ v.
  Proof.
    apply gen_heap_update.
  Qed.
End sim_heap_GS.

Lemma sim_heap_init `{sim_heap_GpreS : SimHeapGpreS Σ locₛ valₛ locₜ valₜ} σₛ σₜ :
  ⊢ |==>
    ∃ sim_heap_GS : SimHeapGS Σ locₛ valₛ locₜ valₜ,
    sim_heap_interpₛ σₛ ∗
    ([∗ map] lₛ ↦ vₛ ∈ σₛ, lₛ ↦ₛ vₛ) ∗
    ([∗ map] lₛ ↦ _ ∈ σₛ, meta_tokenₛ lₛ ⊤) ∗
    sim_heap_interpₜ σₜ ∗
    ([∗ map] lₜ ↦ vₜ ∈ σₜ, lₜ ↦ₜ vₜ) ∗
    ([∗ map] lₜ ↦ _ ∈ σₜ, meta_tokenₜ lₜ ⊤).
Proof.
  iMod (gen_heap_init σₛ) as "(% & Hheapₛ & Hmapstosₛ & Hmetasₛ)".
  iMod (gen_heap_init σₜ) as "(% & Hheapₜ & Hmapstosₜ & Hmetasₜ)".
  iExists (Build_SimHeapGS _ _ _ _ _). iFrame. done.
Qed.

#[global] Opaque mapstoₛ.
#[global] Opaque mapstoₜ.
#[global] Opaque meta_tokenₛ.
#[global] Opaque meta_tokenₜ.
#[global] Opaque metaₛ.
#[global] Opaque metaₜ.
