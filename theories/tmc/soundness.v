From simuliris Require Import
  prelude.
From simuliris.program_logic Require Import
  sim.adequacy.
From simuliris.data_lang Require Import
  refinement
  subexpr
  sim.proofmode
  rsim.rules
  rsim.notations.
From simuliris.tmc Require Export
  definition.
From simuliris.tmc Require Import
  metatheory.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (tmc : tmc sim_progₛ sim_progₜ).
  Implicit Types func func_dps : data_function.
  Implicit Types idx idxₛ idxₜ : data_index.
  Implicit Types l lₛ lₜ dst : loc.
  Implicit Types v vₛ vₜ : data_val.
  Implicit Types e eₛ eₜ : data_expr.
  Implicit Types Φ : data_val → data_val → iProp Σ.
  Implicit Types Ψ : data_expr → data_expr → iProp Σ.

  Definition tmc_protocol_dir Ψ eₛ eₜ : iProp Σ :=
    ∃ func vₛ vₜ,
    ⌜func ∈ dom sim_progₛ⌝ ∗
    ⌜eₛ = func vₛ ∧ eₜ = func vₜ⌝ ∗
    vₛ ≈ vₜ ∗
      ∀ vₛ' vₜ',
      vₛ' ≈ vₜ' -∗
      Ψ vₛ' vₜ'.
  Definition tmc_protocol_dps Ψ eₛ eₜ : iProp Σ :=
    ∃ func func_dps vₛ l1 l2 dst idx vₜ,
    ⌜func ∈ dom sim_progₛ ∧ tmc.(tmc_ξ) !! func = Some func_dps⌝ ∗
    ⌜eₛ = func vₛ ∧ eₜ = func_dps l1⌝ ∗
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

  Lemma tmc_protocol_dps' Φ func vₛ func_dps dst idx vₜ :
    func ∈ dom sim_progₛ →
    tmc.(tmc_ξ) !! func = Some func_dps →
    (dst +ₗ idx) ↦ₜ () -∗
    vₛ ≈ vₜ -∗
    ( ∀ vₛ' vₜ',
      (dst +ₗ idx) ↦ₜ vₜ' -∗
      vₛ' ≈ vₜ' -∗
      Φ vₛ' ()%data_val
    ) -∗
    SIM func vₛ ≳ func_dps (dst, idx, vₜ) [[ tmc_protocol ]] {{# Φ }}.
  Proof.
    rewrite simv_unseal.
    iIntros "%Hfuncₛ %Hξ Hdst #Hv HΦ".
    sim_constrₜ; sim_constrₜ;
      sim_constr_detₜ as l2 "Hl20" "Hl21" "Hl22";
      sim_constr_detₜ as l1 "Hl10" "Hl11" "Hl12";
      sim_apply (sim_apply_protocol _ (sim_post_vals' Φ) _ (func vₛ) (func_dps l1)); iIntros "%σₛ %σₜ $ !>";
      ( iSplitL;
        [ iRight; iExists func, func_dps, vₛ, l1, l2, dst, idx, vₜ; iFrame "#∗";
          do 2 (iSplit; first done); iIntros "%vₛ' %vₜ' Hdst #Hv'"; iSmash
        | iIntros "%eₛ %eₜ HΦ";
          sim_post
        ]
      ).
  Qed.

  Definition tmc_dir_post :=
    (≈)%I.
  Definition tmc_dps_post dst idx vₛ vₜ : iProp Σ :=
    ∃ vₜ',
    ⌜vₜ = ()%data_val⌝ ∗ (dst +ₗ idx) ↦ₜ vₜ' ∗ vₛ ≈ vₜ'.

  Definition tmc_dir_spec' eₛ eₜ :=
    data_expr_well_formed sim_progₛ eₛ →
    {{{ True }}} eₛ ⩾ eₜ [[ tmc_protocol ]] {{{# tmc_dir_post }}}.
  Definition tmc_dir_spec eₛ eₜ :=
    tmc_dir tmc.(tmc_ξ) eₛ eₜ →
    tmc_dir_spec' eₛ eₜ.
  Definition tmc_dps_spec' dst idx eₛ eₜ :=
    data_expr_well_formed sim_progₛ eₛ →
    {{{ (dst +ₗ idx) ↦ₜ () }}} eₛ ⩾ eₜ [[ tmc_protocol ]] {{{# tmc_dps_post dst idx }}}.
  Definition tmc_dps_spec dst idx eₛ eₜ :=
    tmc_dps tmc.(tmc_ξ) dst idx eₛ eₜ →
    tmc_dps_spec' dst idx eₛ eₜ.
  Definition tmc_spec eₛ eₜ :=
    tmc_dir_spec eₛ eₜ ∧
    ∀ dst idx, tmc_dps_spec dst idx eₛ eₜ.

  Lemma tmc_specification eₛ eₜ :
    tmc_spec eₛ eₜ.
  Proof.
    revert eₜ. induction eₛ as [eₛ IHeₛ] using (well_founded_ind data_subexpr_wf).
    cut (
      ( ∀ eₛ eₜ,
        tmc_dir tmc.(tmc_ξ) eₛ eₜ →
        (∀ eₛ' eₜ', eₛ' ⊏ eₛ → tmc_dir_spec eₛ' eₜ') →
        (∀ dst idx eₛ' eₜ', eₛ' ⊏ eₛ → tmc_dps_spec dst idx eₛ' eₜ') →
        tmc_dir_spec' eₛ eₜ
      ) ∧ (
        ∀ (dst idx : data_expr) eₛ eₜ,
        tmc_dps tmc.(tmc_ξ) dst idx eₛ eₜ →
        (∀ eₛ' eₜ', eₛ' ⊏ eₛ → tmc_dir_spec eₛ' eₜ') →
        (∀ dst idx eₛ' eₜ', eₛ' ⊏ eₛ → tmc_dps_spec dst idx eₛ' eₜ') →
        ∀ dst' idx',
        dst = dst' →
        idx = idx' →
        tmc_dps_spec' dst' idx' eₛ eₜ
      )
    ). {
      rewrite /tmc_spec /tmc_dir_spec /tmc_dps_spec.
      naive_solver.
    }
    clear eₛ IHeₛ. apply tmc_ind;
      rewrite /tmc_dir_spec' /tmc_dps_spec';
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
      | intros _ _ _ _ _ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir1 _ Hdir2 _ Hdir3 _ IHdirₛ _
      | intros Hdir IHdir IHdirₛ IHdpsₛ dst' idx' -> ->
      | intros Hdir1 _ Hdps2 _ IHdirₛ IHdpsₛ dst' idx' -> ->
      | intros Hfunc Hdir _ -> IHdirₛ _ dst' idx' -> ->
      | intros Hdir0 _ Hdps1 _ Hdps2 _ IHdirₛ IHdpsₛ dst' idx' -> ->
      | intros Hdir1 _ Hdps2 _ -> IHdirₛ IHdpsₛ dst' idx' -> ->
      | intros Hdir2 _ Hdps1 _ -> IHdirₛ IHdpsₛ dst' idx' -> ->
      ];
      iIntros "%Hwf %Φ Hpre HΦ".
    (* tmc_dir *)
    - iApply rsimv_val; [done | iSmash].
    - iApply rsimv_var. iSmash.
    - iApply rsim_let;
        iApply IHdirₛ; auto with data_lang.
    - iApply rsim_call;
        [iApply IHdirₛ; auto with data_lang.. |].
      iIntros "%func %vₛ %vₜ %Hfunc #Hv".
      pose (Ψ := sim_post_vals' tmc_dir_post).
      iApply (sim_apply_protocol _ Ψ). iIntros "%σₛ %σₜ $". iSplitR.
      { rewrite /Ψ /sim_post_vals'. iSmash. }
      iIntros "!> % % (%vₛ' & %vₜ' & (-> & ->) & HΨ)".
      sim_post.
    - iApply rsimv_unop; last iSmash.
      iApply IHdirₛ; auto with data_lang.
    - iApply rsimv_binop; last iSmash;
        iApply IHdirₛ; auto with data_lang.
    - iSmash.
    - iApply rsim_if; last iSplit;
        iApply IHdirₛ; auto with data_lang.
    - iApply rsimv_constr; last iSmash;
        iApply IHdirₛ; auto with data_lang.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_constrₛ1.
      sim_apply simv_constr_valₜ1.
      { sim_apply IHdirₛ; auto with data_lang. }
      iIntros "%vₛ1 %lₜ %vₜ1 Hlₜ0 Hlₜ1 Hlₜ2 #Hv1".
      sim_apply (IHdpsₛ lₜ 𝟚 eₛ2 eₜ2.[#lₜ/] with "Hlₜ2 [Hlₜ0 Hlₜ1 HΦ]"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_dps_subst; eauto; autosubst. }
      { auto with data_lang. }
      iIntros "%vₛ2 % (%vₜ2 & -> & Hlₜ2 & #Hv2)".
      sim_constr_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      sim_heap_bij_insert.
      sim_pures.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_constrₛ2.
      sim_apply simv_constr_valₜ2.
      { sim_apply IHdirₛ; auto with data_lang. }
      iIntros "%vₛ2 %lₜ %vₜ2 Hlₜ0 Hlₜ1 Hlₜ2 #Hv2".
      sim_apply (IHdpsₛ lₜ 𝟙 eₛ1 eₜ1.[#lₜ/] with "Hlₜ1 [Hlₜ0 Hlₜ2 HΦ]"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_dps_subst; eauto; autosubst. }
      { auto with data_lang. }
      iIntros "%vₛ1 % (%vₜ1 & -> & Hlₜ1 & #Hv1)".
      sim_constr_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
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
    (* tmc_dps *)
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply (IHdir with "[//] [Hpre HΦ]"); [done.. |]. iIntros "%vₛ %vₜ #Hv".
      sim_storeₜ.
    - iApply rsim_let.
      { iApply (IHdirₛ with "[//] []"); auto with data_lang. }
      iApply (IHdpsₛ with "Hpre [HΦ]"); [auto with data_lang.. |]. iSmash.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply (IHdirₛ with "[//] [Hpre HΦ] [//] HΓ"); [auto with data_lang.. |]. iIntros "%vₛ %vₜ #Hv".
      sim_apply (tmc_protocol_dps' with "Hpre Hv"); auto with data_lang.
    - iApply rsim_if.
      { iApply (IHdirₛ with "[//] []"); auto with data_lang. }
      iSplit; iApply (IHdpsₛ with "Hpre [HΦ]"); [auto with data_lang.. | iSmash].
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_constrₛ1.
      sim_apply simv_constr_valₜ1.
      { sim_apply (IHdirₛ with "[//] [] [//] HΓ"); auto with data_lang. }
      iIntros "%vₛ1 %lₜ %vₜ1 Hlₜ0 Hlₜ1 Hlₜ2 #Hv1".
      sim_storeₜ.
      sim_apply (IHdpsₛ lₜ 𝟚 eₛ2 eₜ2.[#lₜ/] with "Hlₜ2 [Hpre Hlₜ0 Hlₜ1 HΦ] [] HΓ"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_dps_subst; eauto; autosubst. }
      { auto with data_lang. }
      iIntros "%vₛ2 % (%vₜ2 & -> & Hlₜ2 & #Hv2)".
      sim_constr_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      sim_heap_bij_insert.
      iSmash.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_constrₛ2.
      sim_apply simv_constr_valₜ2.
      { sim_apply (IHdirₛ with "[//] [] [//] HΓ"); auto with data_lang. }
      iIntros "%vₛ2 %lₜ %vₜ2 Hlₜ0 Hlₜ1 Hlₜ2 #Hv2".
      sim_storeₜ.
      sim_apply (IHdpsₛ lₜ 𝟙 eₛ1 eₜ1.[#lₜ/] with "Hlₜ1 [Hpre Hlₜ0 Hlₜ2 HΦ] [] HΓ"); first 4 last.
      { autosubst. }
      { auto with data_lang. }
      { eapply tmc_dps_subst; eauto; autosubst. }
      { auto with data_lang. }
      iIntros "%vₛ1 % (%vₜ1 & -> & Hlₜ1 & #Hv1)".
      sim_constr_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      sim_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      sim_heap_bij_insert.
      iSmash.
  Qed.
  Lemma tmc_dir_specification eₛ eₜ :
    tmc_dir_spec eₛ eₜ.
  Proof.
    eapply proj1, tmc_specification.
  Qed.
  Lemma tmc_dps_specification dst idx eₛ eₜ :
    tmc_dps_spec dst idx eₛ eₜ.
  Proof.
    revert dst idx. eapply proj2, tmc_specification.
  Qed.

  Lemma tmc_simv_close Φ eₛ eₜ :
    data_program_valid sim_progₛ →
    SIM eₛ ≳ eₜ [[ tmc_protocol ]] {{# Φ }} -∗
    SIM eₛ ≳ eₜ {{# Φ }}.
  Proof.
    intros (Hprogₛ_wf & Hprogₛ_scope).
    eapply data_program_scope_tmc in Hprogₛ_scope as Hprogₜ_scope; last done.
    iApply sim_close_pure_head_step. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ [Hprotocol | Hprotocol]".
    - iDestruct "Hprotocol" as "(%func & %vₛ & %vₜ & %Hfuncₛ & (-> & ->) & #Hv & HΨ)".
      simpl in Hfuncₛ. apply lookup_lookup_total_dom in Hfuncₛ. set (eₛ := _ !!! _) in Hfuncₛ.
      edestruct tmc.(tmc_dirs) as (eₜ & Hdir & Hfuncₜ); first done.
      iExists eₛ.[#vₛ/], eₜ.[#vₜ/]. iSplit; first auto with data_lang.
      erewrite (subst_data_program_scope' ids inhabitant.ₛ#); last done; last done.
      erewrite (subst_data_program_scope' ids inhabitant.ₜ#); last done; last done.
      iDestruct (tmc_dir_specification $! tmc_dir_post with "[//] [] [//] []") as "Hsim"; eauto.
      + iApply (bisubst_cons_well_formed with "Hv").
        iApply bisubst_inhabitant_well_formed.
      + rewrite -bisubst_consₛ -bisubst_consₜ.
        sim_mono "Hsim". rewrite sim_post_vals_unseal. iSmash.
    - iDestruct "Hprotocol" as "(%func & %func_dps & %vₛ & %l1 & %l2 & %dst & %idx & %vₜ & (%Hfuncₛ & %Hξ) & (-> & ->) & Hl11 & Hl12 & Hl21 & Hl22 & Hdst & #Hv & HΨ)".
      simpl in Hfuncₛ. apply lookup_lookup_total_dom in Hfuncₛ. set (eₛ := _ !!! _) in Hfuncₛ.
      edestruct tmc.(tmc_dpss) as (eₜ & Hdps & Hfunc_dpsₜ); [done.. |].
      iExists eₛ.[#vₛ/], _. iSplit; first auto with data_lang.
      do 4 sim_loadₜ. sim_pures.
      eapply (tmc_dps_subst _ (ids 0 .: #dst .: #idx .: ren (+1))) in Hdps; [| autosubst..].
      erewrite (subst_data_program_scope' _ (ren (+1))) in Hdps; last done; last done. asimpl in Hdps.
      replace eₜ.[#vₜ, #dst, #idx, #l2, #l1/] with eₜ.[ids 0 .: #dst .: #idx .: ren (+1)].[#vₜ, #l2, #l1/] by autosubst.
      erewrite (subst_data_program_scope' ids inhabitant.ₛ#); last done; last done.
      erewrite (subst_data_expr_scope_1' (#l2 .: #l1 .: ids) inhabitant.ₜ#); last first.
      { eapply data_expr_scope_tmc_dps; naive_solver. }
      iDestruct (tmc_dps_specification $! (tmc_dps_post dst idx) with "Hdst [] [//] []") as "Hsim"; eauto.
      + iApply (bisubst_cons_well_formed with "Hv").
        iApply bisubst_inhabitant_well_formed.
      + rewrite -bisubst_consₛ -bisubst_consₜ. asimpl.
        sim_mono "Hsim". rewrite sim_post_vals_unseal. iSmash.
  Qed.
End sim_GS.

Section tmc_sound.
  Context {progₛ progₜ : data_program}.
  Context (Hwf : data_program_valid progₛ).
  Context (tmc : tmc progₛ progₜ).

  Notation Σ := sim_Σ.
  Notation M := (iResUR Σ).

  #[local] Instance tmc_sim_programs : SimPrograms data_ectx_lang data_ectx_lang :=
    Build_SimPrograms progₛ progₜ.

  #[local] Instance tmc_sim_GpreS :
    SimGpreS Σ.
  Proof.
    apply subG_sim_GpreS, subG_refl.
  Qed.

  Lemma tmc_sound :
    data_program_refinement progₛ progₜ.
  Proof.
    rewrite /data_program_refinement map_Forall_lookup => func eₛ Hfuncₛ vₛ vₜ Hvₛ Hv.
    pose proof (sim_adequacy' (M := M)) as Hadequacy. apply Hadequacy.
    iMod (sim_init ∅ ∅) as "(%sim_GS & Hsi & _ & _ & _ & _)".
    iModIntro. iExists _, _. iFrame. iSplitR.
    { clear dependent vₛ vₜ. iIntros "!> %vₛ %vₜ #Hv".
      iApply (data_val_bi_similar_similar with "Hv").
    }
    iApply (tmc_simv_close (sim_programs := tmc_sim_programs) tmc); first done.
    iApply (sim_apply_protocol _ (sim_post_vals (≈)%I)). iIntros "%σₛ %σₜ $ !>".
    iSplitL.
    - iLeft. iExists func, vₛ, vₜ. repeat iSplit; try iSmash.
      + iPureIntro. simpl. eapply elem_of_dom_2. done.
      + iApply data_val_similar_bi_similar; done.
      + rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    - clear dependent vₛ eₛ vₜ. iIntros "%eₛ %eₜ Hsimilar".
      rewrite sim_post_vals_unseal. sim_post.
  Qed.
End tmc_sound.
