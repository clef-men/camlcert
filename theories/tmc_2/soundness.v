From Coq Require Import
  Wellfounded.Lexicographic_Product.

From camlcert Require Import
  prelude.
From camlcert.data_lang Require Import
  refinement
  subexpr
  sim.proofmode
  sim.adequacy
  rsim.rules
  rsim.notations.
From camlcert.tmc_2 Require Export
  definition.
From camlcert.tmc_2 Require Import
  metatheory.
From camlcert Require Import
  options.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (tmc : tmc sim_progₛ sim_progₜ).

  Implicit Types func func_dps : data_function.
  Implicit Types annot : data_annotation.
  Implicit Types idx idxₛ idxₜ : data_index.
  Implicit Types l lₛ lₜ dst : loc.
  Implicit Types v vₛ vₜ : data_val.
  Implicit Types e eₛ eₜ : data_expr.
  Implicit Types C : tmc_rctx.

  Fixpoint tmc_chain v C dst idx : iProp Σ :=
    match C with
    | [] =>
        (dst +ₗ idx) ↦ₜ v
    | c :: C =>
        ∃ l,
        (l +ₗ 0) ↦ₜ c.(tmc_rctxi_tag) ∗
        (l +ₗ c.(tmc_rctxi_side)) ↦ₜ v ∗
        (l +ₗ tmc_side_invert c.(tmc_rctxi_side)) ↦ₜ c.(tmc_rctxi_val) ∗
        tmc_chain l C dst idx
    end.

  Lemma tmc_chain_snoc v C l c dst idx :
    tmc_chain v C l c.(tmc_rctxi_side) -∗
    (l +ₗ 0) ↦ₜ c.(tmc_rctxi_tag) -∗
    (l +ₗ tmc_side_invert c.(tmc_rctxi_side)) ↦ₜ c.(tmc_rctxi_val) -∗
    (dst +ₗ idx) ↦ₜ l -∗
    tmc_chain v (C ++ [c]) dst idx.
  Proof.
    iInduction C as [] "IH" forall (v); iSmash.
  Qed.

  #[local] Lemma tmc_chain_spec_aux Ψ Χ Φ eₛ (K : data_ectx) C eₜ :
    SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
      ∃ vₜ,
      ⌜eₜ' = vₜ⌝ ∗
      Ψ eₛ' vₜ
    }} -∗
    ( ∀ eₛ' vₜ vₜ',
      Ψ eₛ' vₜ -∗
      ( ∀ dst idx,
        (dst +ₗ idx) ↦ₜ vₜ' -∗
        tmc_chain vₜ C dst idx
      ) -∗
      SIM eₛ' ≳ K @@ #vₜ' [[ Χ ]] {{ Φ }}
    ) -∗
    SIM eₛ ≳ K @@ (C : tmc_ctx) @@ eₜ [[ Χ ]] {{ Φ }}.
  Proof.
    iIntros "Hsim HΦ".
    iInduction C as [| (tag, side, v) C] "IH" using rev_ind forall (K).
    - iApply sim_bindₜ.
      sim_mono "Hsim".
    - iApply sim_bindₜ.
      setoid_rewrite fmap_snoc. setoid_rewrite foldl_snoc.
      destruct side.
      all: sim_blockₜ.
      + iApply sim_bind_invₜ.
        sim_apply ("IH" $! ([DataEctxiLet _] ++ K) with "Hsim [HΦ]").
        iIntros "%eₛ' %vₜ %vₜ' HΨ Hchain /=".
        iApply sim_bindₜ.
        sim_block_detₜ as lₜ "Hlₜ0" "Hlₜ1" "Hlₜ2".
        iApply sim_bind_invₜ.
        sim_apply ("HΦ" with "HΨ [-]"). iIntros "%dst %idx Hdst".
        iDestruct ("Hchain" $! _ 𝟙 with "Hlₜ1") as "Hchain".
        iApply (tmc_chain_snoc _ _ _ (TmcRctxi tag TmcLeft v) with "Hchain Hlₜ0 Hlₜ2 Hdst").
      + sim_puresₜ.
        iApply sim_bind_invₜ.
        sim_apply ("IH" $! ([DataEctxiLet _] ++ K) with "Hsim [HΦ]").
        iIntros "%eₛ' %vₜ %vₜ' HΨ Hchain /=".
        iApply sim_bindₜ.
        sim_block_detₜ as lₜ "Hlₜ0" "Hlₜ1" "Hlₜ2".
        iApply sim_bind_invₜ.
        sim_apply ("HΦ" with "HΨ [-]"). iIntros "%dst %idx Hdst".
        iDestruct ("Hchain" $! _ 𝟙 with "Hlₜ1") as "Hchain".
        iApply (tmc_chain_snoc _ _ _ (TmcRctxi tag TmcLeft v) with "Hchain Hlₜ0 Hlₜ2 Hdst").
      + sim_puresₜ.
        iApply sim_bind_invₜ.
        sim_apply ("IH" $! ([DataEctxiLet _] ++ K) with "Hsim [HΦ]").
        iIntros "%eₛ' %vₜ %vₜ' HΨ Hchain /=".
        iApply sim_bindₜ.
        sim_block_detₜ as lₜ "Hlₜ0" "Hlₜ1" "Hlₜ2".
        iApply sim_bind_invₜ.
        sim_apply ("HΦ" with "HΨ [-]"). iIntros "%dst %idx Hdst".
        iDestruct ("Hchain" $! _ 𝟚 with "Hlₜ2") as "Hchain".
        iApply (tmc_chain_snoc _ _ _ (TmcRctxi tag TmcRight v) with "Hchain Hlₜ0 Hlₜ1 Hdst").
      + iApply sim_bind_invₜ.
        sim_apply ("IH" $! ([DataEctxiLet _] ++ K) with "Hsim [HΦ]").
        iIntros "%eₛ' %vₜ %vₜ' HΨ Hchain /=".
        iApply sim_bindₜ.
        sim_block_detₜ as lₜ "Hlₜ0" "Hlₜ1" "Hlₜ2".
        iApply sim_bind_invₜ.
        sim_apply ("HΦ" with "HΨ [-]"). iIntros "%dst %idx Hdst".
        iDestruct ("Hchain" $! _ 𝟚 with "Hlₜ2") as "Hchain".
        iApply (tmc_chain_snoc _ _ _ (TmcRctxi tag TmcRight v) with "Hchain Hlₜ0 Hlₜ1 Hdst").
  Qed.
  Lemma tmc_chain_spec Ψ Χ Φ eₛ C eₜ :
    SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
      ∃ vₜ,
      ⌜eₜ' = vₜ⌝ ∗
      Ψ eₛ' vₜ
    }} -∗
    ( ∀ eₛ' vₜ vₜ',
      Ψ eₛ' vₜ -∗
      ( ∀ dst idx,
        (dst +ₗ idx) ↦ₜ vₜ' -∗
        tmc_chain vₜ C dst idx
      ) -∗
      SIM eₛ' ≳ vₜ' [[ Χ ]] {{ Φ }}
    ) -∗
    SIM eₛ ≳ (C : tmc_ctx) @@ eₜ [[ Χ ]] {{ Φ }}.
  Proof.
    apply (tmc_chain_spec_aux _ _ _ _ []).
  Qed.

  Implicit Types Φ : data_val → data_val → iProp Σ.
  Implicit Types Ψ : data_expr → data_expr → iProp Σ.

  Definition tmc_protocol_dir Ψ eₛ eₜ : iProp Σ :=
    ∃ func annot vₛ vₜ,
    ⌜func ∈ dom sim_progₛ⌝ ∗
    ⌜eₛ = (DataFunc func annot) vₛ ∧ eₜ = (DataFunc func annot) vₜ⌝ ∗
    vₛ ≈ vₜ ∗
      ∀ vₛ' vₜ',
      vₛ' ≈ vₜ' -∗
      Ψ vₛ' vₜ'.

  Definition tmc_protocol_dps Ψ eₛ eₜ : iProp Σ :=
    ∃ func annot vₛ func_dps l1 l2 dst idx vₜ,
    ⌜func ∈ dom sim_progₛ ∧ tmc.(tmc_ξ) !! func = Some func_dps⌝ ∗
    ⌜eₛ = (DataFunc func annot) vₛ ∧ eₜ = (DataFunc func_dps annot) l1⌝ ∗
    (l1 +ₗ 1) ↦ₜ l2 ∗ (l1 +ₗ 2) ↦ₜ vₜ ∗
    (l2 +ₗ 1) ↦ₜ dst ∗ (l2 +ₗ 2) ↦ₜ idx ∗
    (dst +ₗ idx) ↦ₜ () ∗
    vₛ ≈ vₜ ∗
      ∀ vₛ' vₜ',
      (dst +ₗ idx) ↦ₜ vₜ' -∗
      vₛ' ≈ vₜ' -∗
      Ψ vₛ' #().

  Definition tmc_protocol Ψ eₛ eₜ : iProp Σ :=
    tmc_protocol_dir Ψ eₛ eₜ ∨
    tmc_protocol_dps Ψ eₛ eₜ.

  Lemma tmc_protocol_dps' Φ func annot vₛ func_dps dst idx vₜ :
    func ∈ dom sim_progₛ →
    tmc.(tmc_ξ) !! func = Some func_dps →
    (dst +ₗ idx) ↦ₜ () -∗
    vₛ ≈ vₜ -∗
    ( ∀ vₛ' vₜ',
      (dst +ₗ idx) ↦ₜ vₜ' -∗
      vₛ' ≈ vₜ' -∗
      Φ vₛ' ()%data_val
    ) -∗
    SIM (DataFunc func annot) vₛ ≳ (DataFunc func_dps annot) (dst, idx, vₜ) [[ tmc_protocol ]] {{# Φ }}.
  Proof.
    rewrite simv_unseal.
    iIntros "%Hfuncₛ %Hξ Hdst #Hv HΦ".
    sim_blockₜ; sim_blockₜ;
      sim_block_detₜ as l2 "Hl20" "Hl21" "Hl22";
      sim_block_detₜ as l1 "Hl10" "Hl11" "Hl12";
      sim_apply (sim_apply_protocol (sim_post_vals' Φ) _ _ ((DataFunc func annot) vₛ) ((DataFunc func_dps annot) l1)); iIntros "%σₛ %σₜ $ !>";
      ( iSplitL;
        [ iRight; repeat iExists _; iFrame "#∗";
          do 2 (iSplit; first done); iIntros "%vₛ' %vₜ' Hdst #Hv'"; iSmash
        | iIntros "%eₛ %eₜ HΦ";
          sim_post
        ]
      ).
  Qed.

  Definition tmc_expr_dir_post :=
    (≈)%I.
  Definition tmc_expr_dir_specification' eₛ eₜ :=
    data_expr_well_formed sim_progₛ eₛ →
    {{{ True }}} eₛ ⩾ eₜ [[ tmc_protocol ]] {{{# tmc_expr_dir_post }}}.
  Definition tmc_expr_dir_specification eₛ eₜ :=
    tmc_expr_dir tmc.(tmc_ξ) eₛ eₜ →
    tmc_expr_dir_specification' eₛ eₜ.

  Definition tmc_expr_dps_post dst idx C vₛ vₜ : iProp Σ :=
    ∃ vₜ',
    ⌜vₜ = ()%data_val⌝ ∗
    tmc_chain vₜ' C dst idx ∗
    vₛ ≈ vₜ'.
  Definition tmc_expr_dps_specification' dst idx C eₛ eₜ :=
    data_expr_well_formed sim_progₛ eₛ →
    {{{ (dst +ₗ idx) ↦ₜ () }}} eₛ ⩾ eₜ [[ tmc_protocol ]] {{{# tmc_expr_dps_post dst idx C }}}.
  Definition tmc_expr_dps_specification dst idx C eₛ eₜ :=
    tmc_expr_dps tmc.(tmc_ξ) dst idx C eₛ eₜ →
    tmc_expr_dps_specification' dst idx C eₛ eₜ.

  Definition tmc_expr_specification eₛ eₜ :=
    tmc_expr_dir_specification eₛ eₜ ∧
    ∀ dst idx C, tmc_expr_dps_specification dst idx C eₛ eₜ.

  Lemma tmc_expr_spec eₛ eₜ :
    tmc_expr_specification eₛ eₜ.
  Proof.
    move: eₛ eₜ.
    cut (
      ∀ C eₛ eₜ,
      tmc_expr_dir_specification eₛ eₜ ∧
      ∀ dst idx, tmc_expr_dps_specification dst idx C eₛ eₜ
    ). {
      intros H. split; [apply (H inhabitant) | naive_solver].
    }
    cut (
      ∀ eₛ eₜ,
      ( (∀ eₛ' eₜ, eₛ' ⊏ eₛ → tmc_expr_dir_specification eₛ' eₜ) →
        (∀ dst idx C eₛ' eₜ, eₛ' ⊏ eₛ → tmc_expr_dps_specification dst idx C eₛ' eₜ) →
        tmc_expr_dir_specification eₛ eₜ
      ) ∧ (
        ∀ dst idx C,
        (∀ eₛ' eₜ, eₛ' ⊏ eₛ → tmc_expr_dir_specification eₛ' eₜ) →
        (∀ dst idx C eₛ' eₜ, eₛ' ⊏ eₛ → tmc_expr_dps_specification dst idx C eₛ' eₜ) →
        (∀ dst idx C' eₜ, length C' < length C → tmc_expr_dps_specification dst idx C' eₛ eₜ) →
        tmc_expr_dps_specification dst idx C eₛ eₜ
      )
    ). {
      intros H C eₛ.
      remember (length C) as len eqn:Hlen.
      change eₛ with (projT1 (existT eₛ len)).
      change len with (projT2 (existT eₛ len)) in Hlen.
      remember (existT eₛ len) as x eqn:Hx. clear Hx len eₛ. move: x C Hlen.
      induction x as [(eₛ, len) IHx] using (well_founded_ind (wf_lexprod _ _ _ _ data_subexpr_wf (λ _, Nat.lt_wf_0))).
      intros C Hlen. split.
      - apply H; clear eₜ.
        + intros eₛ' eₜ ?.
          efeed pose proof (IHx (existT eₛ' len)); [| naive_solver..].
          apply Relation_Operators.left_lex. done.
        + intros dst idx C' eₛ' eₜ ?.
          efeed pose proof (IHx (existT eₛ' (length C'))); [| naive_solver..].
          auto using Relation_Operators.lexprod.
      - intros dst idx.
        apply H; clear dst idx eₜ.
        + intros eₛ' eₜ ?.
          efeed pose proof (IHx (existT eₛ' (length C))); [| naive_solver..].
          auto using Relation_Operators.lexprod.
        + intros dst idx C' eₛ' eₜ' ?.
          efeed pose proof (IHx (existT eₛ' (length C'))); [| naive_solver..].
          auto using Relation_Operators.lexprod.
        + intros dst idx C' eₜ' ?.
          efeed pose proof (IHx (existT eₛ (length C'))); [| naive_solver..].
          apply Relation_Operators.right_lex. naive_solver.
    }
    cut (
      ( ∀ eₛ eₜ,
        tmc_expr_dir tmc.(tmc_ξ) eₛ eₜ →
        (∀ eₛ' eₜ, eₛ' ⊏ eₛ → tmc_expr_dir_specification eₛ' eₜ) →
        (∀ dst idx C eₛ' eₜ, eₛ' ⊏ eₛ → tmc_expr_dps_specification dst idx [] eₛ' eₜ) →
        tmc_expr_dir_specification' eₛ eₜ
      ) ∧ (
        ∀ (dst idx : data_expr) (C : tmc_ctx) eₛ eₜ,
        tmc_expr_dps tmc.(tmc_ξ) dst idx C eₛ eₜ →
        ∀ dst' idx' C',
        dst = dst' →
        idx = idx' →
        C = C' →
        (∀ eₛ' eₜ, eₛ' ⊏ eₛ → tmc_expr_dir_specification eₛ' eₜ) →
        (∀ dst idx C eₛ' eₜ, eₛ' ⊏ eₛ → tmc_expr_dps_specification dst idx C eₛ' eₜ) →
        (∀ dst idx C eₜ, length C < length C' → tmc_expr_dps_specification dst idx C eₛ eₜ) →
        tmc_expr_dps_specification' dst' idx' C' eₛ eₜ
      )
    ). {
      rewrite /tmc_expr_dir_specification /tmc_expr_dps_specification.
      naive_solver.
    }
    apply tmc_expr_ind;
      rewrite /tmc_expr_dir_specification' /tmc_expr_dps_specification';
      intros *;
      [ intros _ _
      | intros _ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir _ IHdirₛ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros _ _ _ _ _ _
      | intros Hdir0 _ Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir1 _ Hdps2 _ IHdirₛ IHdpsₛ
      | intros Hdir1 _ Hdps2 _ IHdirₛ IHdpsₛ
      | intros Hdps1 _ Hdps2 _ -> _ IHdpsₛ
      | intros _ _ _ _ _ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir1 _ Hdir2 _ Hdir3 _ IHdirₛ _
      | intros Hdir IHdir -> dst' idx' C' -> -> -> IHdirₛ IHdpsₛ _
      | intros Hdir1 _ Hdps2 _ dst' idx' C' -> -> -> IHdirₛ IHdpsₛ _
      | intros Hfunc Hdir _ -> dst' idx' C' -> -> <-%(inj tmc_rctx_to_ctx []) IHdirₛ _ _
      | intros Hdir0 _ Hdps1 _ Hdps2 _ dst' idx' C' -> -> -> IHdirₛ IHdpsₛ _
      | intros Hdir1 _ Hdps2 _ -> dst' idx' C' -> -> -> IHdirₛ IHdpsₛ _
      | intros Hdir2 _ Hdps1 _ -> dst' idx' C' -> -> -> IHdirₛ IHdpsₛ _
      | intros Hdps IHdps -> dst' idx' C' -> -> HC _ _ IHC
      ];
      iIntros "%Hwf %Φ Hpre HΦ".
    (* tmc_expr_dir *)
    - iApply rsimv_val; [done | iSmash].
    - iApply rsimv_var. iSmash.
    - iApply rsimv_let;
        iApply IHdirₛ; auto with data_lang.
    - iApply rsimv_call;
        [iApply IHdirₛ; auto with data_lang.. |].
      iIntros "%func %annot %vₛ %vₜ %Hfunc #Hv".
      pose (Ψ := sim_post_vals' tmc_expr_dir_post).
      iApply (sim_apply_protocol Ψ). iIntros "%σₛ %σₜ $ !>". iSplitR.
      { rewrite /Ψ /sim_post_vals'. iSmash. }
      iIntros "% % (%vₛ' & %vₜ' & (-> & ->) & HΨ)".
      sim_post.
    - iApply rsimv_unop; last iSmash.
      iApply IHdirₛ; auto with data_lang.
    - iApply rsimv_binop; last iSmash;
        iApply IHdirₛ; auto with data_lang.
    - iSmash.
    - iApply rsimv_if; last iSplit;
        iApply IHdirₛ; auto with data_lang.
    - iApply rsimv_block; last iSmash;
        iApply IHdirₛ; auto with data_lang.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_blockₛ1.
      sim_apply simv_block_valₜ2.
      { sim_apply IHdirₛ; auto with data_lang. }
      iIntros "%vₛ1 %lₜ %vₜ1 Hlₜ0 Hlₜ1 Hlₜ2 #Hv1".
      sim_apply (IHdpsₛ lₜ 𝟚 [] eₛ2 eₜ2.[#lₜ/] with "Hlₜ2 [Hlₜ0 Hlₜ1 HΦ]"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_expr_dps_subst; eauto; autosubst. }
      { auto with data_lang. }
      iIntros "%vₛ2 % (%vₜ2 & -> & Hlₜ2 & #Hv2)".
      sim_block_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      sim_heap_bij_insert.
      sim_pures.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_blockₛ2.
      sim_apply simv_block_valₜ1.
      { sim_apply IHdirₛ; auto with data_lang. }
      iIntros "%vₛ2 %lₜ %vₜ2 Hlₜ0 Hlₜ1 Hlₜ2 #Hv2".
      sim_apply (IHdpsₛ lₜ 𝟙 [] eₛ1 eₜ1.[#lₜ/] with "Hlₜ1 [Hlₜ0 Hlₜ2 HΦ]"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_expr_dps_subst; eauto; autosubst. }
      { auto with data_lang. }
      iIntros "%vₛ1 % (%vₜ1 & -> & Hlₜ1 & #Hv1)".
      sim_block_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      sim_heap_bij_insert.
      sim_pures.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_blockₛ1.
      rewrite sim_post_vals_unseal.
      sim_apply sim_block_valₜ. iIntros "%lₜ Hlₜ0 Hlₜ1 Hlₜ2". iApply sim_post.
      rewrite -sim_post_vals_unseal.
      sim_apply (IHdpsₛ lₜ 𝟙 [] eₛ1 eₜ1.[#lₜ/] with "Hlₜ1 [Hlₜ0 Hlₜ2 HΦ]"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_expr_dps_subst; first apply Hdps1; autosubst. }
      { auto with data_lang. }
      iIntros "%vₛ1 % (%vₜ1 & -> & Hlₜ1 & #Hv1)".
      sim_apply (IHdpsₛ lₜ 𝟚 [] eₛ2 eₜ2.[#lₜ/] with "Hlₜ2 [Hlₜ0 Hlₜ1 HΦ]"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_expr_dps_subst; first apply Hdps2; autosubst. }
      { auto with data_lang. }
      iIntros "%vₛ2 % (%vₜ2 & -> & Hlₜ2 & #Hv2)".
      sim_block_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      sim_heap_bij_insert.
      sim_pures.
    - iSmash.
    - iApply rsimv_load; last iSmash;
        iApply IHdirₛ; auto with data_lang.
    - iApply rsimv_store; last iSmash;
        iApply IHdirₛ; auto with data_lang.
    (* tmc_expr_dps *)
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply (tmc_chain_spec (λ eₛ vₜ, ∃ vₛ, ⌜eₛ = vₛ⌝ ∗ vₛ ≈ vₜ)%I).
      { iApply (sim_mono _ (sim_post_vals (≈))).
        { rewrite sim_post_vals_unseal. iSmash. }
        sim_apply (IHdir with "[//]"); first auto.
      }
      iIntros "%eₛ' %vₜ %vₜ' (%vₛ & -> & #Hv) Hchain".
      sim_storeₜ.
    - iApply rsimv_let.
      { iApply (IHdirₛ with "[//] []"); auto with data_lang. }
      rewrite tmc_rctx_hsubst in Hdps2.
      iApply (IHdpsₛ with "Hpre [HΦ]"); [auto with data_lang.. |]. iSmash.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply (IHdirₛ with "[//] [Hpre HΦ] [//] HΓ"); [auto with data_lang.. |].
      iIntros "%vₛ %vₜ #Hv".
      sim_apply (tmc_protocol_dps' with "Hpre Hv"); auto with data_lang.
    - iApply rsimv_if.
      { iApply (IHdirₛ with "[//] []"); auto with data_lang. }
      iSplit; iApply (IHdpsₛ with "Hpre [HΦ]"); [auto with data_lang.. | iSmash].
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_blockₛ1.
      sim_apply (IHdirₛ with "[//] [Hpre HΦ] [//] HΓ"); [auto with data_lang.. |].
      iIntros "%vₛ1 %vₜ1 #Hv1".
      sim_pures.
      sim_apply (IHdpsₛ dst' idx' (TmcRctxi _ _ _ :: C') eₛ2 eₜ2.[#vₜ1/] with "Hpre [HΦ] [] HΓ"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_expr_dps_subst; eauto; asimpl; done. }
      { auto with data_lang. }
      iIntros "%vₛ2 % (%vₜ2 & -> & (%lₜ & Hlₜ0 & Hlₜ2 & Hlₜ1 & HC') & #Hv2) /=".
      sim_block_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      sim_heap_bij_insert.
      iSmash.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_blockₛ2.
      sim_apply (IHdirₛ with "[//] [Hpre HΦ] [//] HΓ"); [auto with data_lang.. |].
      iIntros "%vₛ2 %vₜ2 #Hv2".
      sim_pures.
      sim_apply (IHdpsₛ dst' idx' (TmcRctxi _ _ _ :: C') eₛ1 eₜ1.[#vₜ2/] with "Hpre [HΦ] [] HΓ"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_expr_dps_subst; eauto; asimpl; done. }
      { auto with data_lang. }
      iIntros "%vₛ1 % (%vₜ1 & -> & (%lₜ & Hlₜ0 & Hlₜ1 & Hlₜ2 & HC') & #Hv1) /=".
      sim_block_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      sim_heap_bij_insert.
      iSmash.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      rewrite sim_post_vals_unseal.
      destruct C' as [| (tag, side, v) C']; first done. injection HC as -> ->.
      destruct side.
      + sim_apply sim_block_valₜ. iIntros "%lₜ Hlₜ0 Hlₜ1 Hlₜ2".
        sim_post. sim_puresₜ. rewrite tmc_ctx_fill_subst. asimpl.
        sim_apply (tmc_chain_spec (λ eₛ' vₜ, ⌜eₛ' = eₛ.[Γ.ₛ#]⌝ ∗ ⌜vₜ = lₜ⌝)%I).
        { sim_post. }
        iIntros "%eₛ' %vₜ %vₜ' (-> & ->) Hchain".
        sim_post. sim_storeₜ. sim_puresₜ.
        rewrite -sim_post_vals_unseal.
        sim_apply (IHC lₜ 𝟙 [] eₜ.[#lₜ/] with "Hlₜ1 [-] [%]").
        { simpl. lia. }
        { eapply tmc_expr_dps_subst; eauto; autosubst. }
        { split; autosubst. }
      + sim_apply sim_block_valₜ. iIntros "%lₜ Hlₜ0 Hlₜ1 Hlₜ2".
        sim_post. sim_puresₜ. rewrite tmc_ctx_fill_subst. asimpl.
        sim_apply (tmc_chain_spec (λ eₛ' vₜ, ⌜eₛ' = eₛ.[Γ.ₛ#]⌝ ∗ ⌜vₜ = lₜ⌝)%I).
        { sim_post. }
        iIntros "%eₛ' %vₜ %vₜ' (-> & ->) Hchain".
        sim_post. sim_storeₜ. sim_puresₜ.
        rewrite -sim_post_vals_unseal.
        sim_apply (IHC lₜ 𝟚 [] eₜ.[#lₜ/] with "Hlₜ2 [-] [%]").
        { simpl. lia. }
        { eapply tmc_expr_dps_subst; eauto; autosubst. }
        { split; autosubst. }
  Qed.
  Lemma tmc_expr_dir_spec eₛ eₜ :
    tmc_expr_dir_specification eₛ eₜ.
  Proof.
    eapply proj1, tmc_expr_spec.
  Qed.
  Lemma tmc_expr_dps_spec dst idx C eₛ eₜ :
    tmc_expr_dps_specification dst idx C eₛ eₜ.
  Proof.
    move: dst idx C. eapply proj2, tmc_expr_spec.
  Qed.

  Lemma tmc_simv_close Φ eₛ eₜ :
    data_program_valid sim_progₛ →
    SIM eₛ ≳ eₜ [[ tmc_protocol ]] {{# Φ }} -∗
    SIM eₛ ≳ eₜ {{# Φ }}.
  Proof.
    intros (Hprogₛ_wf & Hprogₛ_scoped).
    eapply data_program_scoped_tmc in Hprogₛ_scoped as Hprogₜ_scoped; last done.
    iApply sim_close_pure_head_step. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ [Hprotocol | Hprotocol]".
    - iDestruct "Hprotocol" as "(%func & %annot & %vₛ & %vₜ & %Hfuncₛ & (-> & ->) & #Hv & HΨ)".
      simpl in Hfuncₛ. apply lookup_lookup_total_dom in Hfuncₛ.
      set defₛ := _ !!! _ in Hfuncₛ. set eₛ := defₛ.(data_definition_body).
      edestruct tmc.(tmc_dir) as (eₜ & Hdir & Hfuncₜ); first done.
      iExists _, _. iSplit; first eauto 10 with data_lang. sim_asimpl.
      erewrite (subst_data_program_scoped' ids inhabitant.ₛ# _ sim_progₛ); [| done..].
      erewrite (subst_data_program_scoped' ids inhabitant.ₜ# _ sim_progₜ); [| done..].
      iDestruct (tmc_expr_dir_spec $! tmc_expr_dir_post with "[//] [] [//] []") as "Hsim"; eauto.
      + iApply (bisubst_cons_well_formed with "Hv").
        iApply bisubst_inhabitant_well_formed.
      + rewrite -bisubst_consₛ -bisubst_consₜ.
        sim_mono "Hsim". rewrite sim_post_vals_unseal. iSmash.
    - iDestruct "Hprotocol" as "(%func & %annot & %vₛ & %func_dps & %l1 & %l2 & %dst & %idx & %vₜ & (%Hfuncₛ & %Hξ) & (-> & ->) & Hl11 & Hl12 & Hl21 & Hl22 & Hdst & #Hv & HΨ)".
      simpl in Hfuncₛ. apply lookup_lookup_total_dom in Hfuncₛ.
      set defₛ := _ !!! _ in Hfuncₛ. set eₛ := defₛ.(data_definition_body).
      edestruct tmc.(tmc_dps) as (eₜ & Hdps & Hfunc_dpsₜ); [done.. |].
      iExists _, _. iSplit; first eauto 10 with data_lang. sim_asimpl.
      do 4 sim_loadₜ. sim_pures.
      eapply (tmc_expr_dps_subst _ (ids 0 .: #dst .: #idx .: ren (+1))) in Hdps; [| autosubst..].
      erewrite (subst_data_program_scoped' _ (ren (+1)) _ sim_progₛ) in Hdps; [| done..]. asimpl in Hdps.
      replace eₜ.[#vₜ, #dst, #idx, #l2, #l1/] with eₜ.[ids 0 .: #dst .: #idx .: ren (+1)].[#vₜ, #l2, #l1/] by autosubst.
      erewrite (subst_data_program_scoped' ids inhabitant.ₛ# _ sim_progₛ); [| done..].
      erewrite (subst_data_expr_scoped_1' (#l2 .: #l1 .: ids) inhabitant.ₜ#); last first.
      { eapply data_expr_scoped_tmc_expr_dps; naive_solver. }
      iDestruct (tmc_expr_dps_spec dst idx [] $! (tmc_expr_dps_post dst idx []) with "Hdst [] [//] []") as "Hsim"; eauto.
      + iApply (bisubst_cons_well_formed with "Hv").
        iApply bisubst_inhabitant_well_formed.
      + rewrite -bisubst_consₛ -bisubst_consₜ. asimpl.
        sim_mono "Hsim". rewrite sim_post_vals_unseal. iSmash.
  Qed.
End sim_GS.

Lemma tmc_sound progₛ progₜ :
  data_program_valid progₛ →
  tmc progₛ progₜ →
  data_program_refinement progₛ progₜ.
Proof.
  intros Hwf Htmc.
  pose sim_programs := Build_SimPrograms progₛ progₜ.
  apply: sim_adequacy => sim_GS func defₛ vₛ vₜ Hlookup Hvₛ Hv.
  iApply (tmc_simv_close (sim_programs := sim_programs) Htmc); first done.
  iApply (sim_apply_protocol (sim_post_vals (≈)%I)). iIntros "%σₛ %σₜ $ !>".
  iSplitL.
  - iLeft. iExists func, [], vₛ, vₜ. repeat iSplit; try iSmash.
    + iPureIntro. simpl. eapply elem_of_dom_2. done.
    + iApply data_val_similar_bi_similar; done.
    + rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
  - iIntros "%eₛ %eₜ Hsimilar".
    rewrite sim_post_vals_unseal. sim_post.
Qed.
