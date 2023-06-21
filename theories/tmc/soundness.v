From simuliris Require Import
  prelude.
From simuliris.program_logic Require Import
  sim.adequacy.
From simuliris.language Require Import
  refinement
  subexpr.
From simuliris.tmc Require Export
  definition.
From simuliris.tmc Require Import
  substitution
  sim.proofmode
  csim.rules
  csim.notations.

Section sim.
  Context `{sim_programs : !SimPrograms ectx_language ectx_language}.
  Context `{sim_GS : !SimGS Σ}.
  Context (tmc : tmc sim_progₛ sim_progₜ).
  Implicit Types func func_dps : function.
  Implicit Types idx idxₛ idxₜ : index.
  Implicit Types l lₛ lₜ dst : loc.
  Implicit Types v vₛ vₜ : val.
  Implicit Types e eₛ eₜ : expr.
  Implicit Types Φ : val → val → iProp Σ.
  Implicit Types Ψ : expr → expr → iProp Σ.

  Definition tmc_protocol_dir Ψ eₛ eₜ : iProp Σ :=
    ∃ func vₛ vₜ,
    ⌜func ∈ dom sim_progₛ⌝ ∗
    ⌜eₛ = func vₛ ∧ eₜ = func vₜ⌝ ∗
    vₛ ≈ vₜ ∗
    (∀ vₛ' vₜ', vₛ' ≈ vₜ' -∗ Ψ vₛ' vₜ').
  Definition tmc_protocol_dps Ψ eₛ eₜ : iProp Σ :=
    ∃ func func_dps vₛ dst idx vₜ,
    ⌜func ∈ dom sim_progₛ ∧ tmc.(tmc_ξ) !! func = Some func_dps⌝ ∗
    ⌜eₛ = func vₛ ∧ eₜ = func_dps ((dst, idx), vₜ)%E⌝ ∗
    (dst +ₗ idx) ↦ₜ () ∗
    vₛ ≈ vₜ ∗
    (∀ vₛ' vₜ', (dst +ₗ idx) ↦ₜ vₜ' -∗ vₛ' ≈ vₜ' -∗ Ψ vₛ' #()).
  Definition tmc_protocol Ψ eₛ eₜ : iProp Σ :=
    tmc_protocol_dir Ψ eₛ eₜ ∨
    tmc_protocol_dps Ψ eₛ eₜ.

  Definition tmc_dir_post :=
    (≈)%I.
  Definition tmc_dps_post dst idx vₛ vₜ : iProp Σ :=
    ∃ vₜ',
    ⌜vₜ = ()%V⌝ ∗ (dst +ₗ idx) ↦ₜ vₜ' ∗ vₛ ≈ vₜ'.

  Definition tmc_dir_spec' eₛ eₜ :=
    expr_well_formed' sim_progₛ eₛ →
    [[[ True ]]] eₛ ⩾ eₜ [[ tmc_protocol ]] [[[ tmc_dir_post ]]].
  Definition tmc_dir_spec eₛ eₜ :=
    tmc_dir tmc.(tmc_ξ) eₛ eₜ →
    tmc_dir_spec' eₛ eₜ.
  Definition tmc_dps_spec' dst idx eₛ eₜ :=
    expr_well_formed' sim_progₛ eₛ →
    [[[ (dst +ₗ idx) ↦ₜ () ]]] eₛ ⩾ eₜ [[ tmc_protocol ]] [[[ tmc_dps_post dst idx ]]].
  Definition tmc_dps_spec dst idx eₛ eₜ :=
    tmc_dps tmc.(tmc_ξ) dst idx eₛ eₜ →
    tmc_dps_spec' dst idx eₛ eₜ.
  Definition tmc_spec eₛ eₜ :=
    tmc_dir_spec eₛ eₜ ∧
    ∀ dst idx, tmc_dps_spec dst idx eₛ eₜ.

  Lemma tmc_specification eₛ eₜ :
    tmc_spec eₛ eₜ.
  Proof.
    revert eₜ. induction eₛ as [eₛ IHeₛ] using (well_founded_ind subexpr_wf).
    cut (
      ( ∀ eₛ eₜ,
        tmc_dir tmc.(tmc_ξ) eₛ eₜ →
        (∀ eₛ' eₜ', eₛ' ⊏ eₛ → tmc_dir_spec eₛ' eₜ') →
        (∀ dst idx eₛ' eₜ', eₛ' ⊏ eₛ → tmc_dps_spec dst idx eₛ' eₜ') →
        tmc_dir_spec' eₛ eₜ
      ) ∧ (
        ∀ (dst idx : expr) eₛ eₜ,
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
    - iApply csimv_val; auto with language.
    - iApply csimv_var. done.
    - iApply csimv_let; iApply IHdirₛ; auto with language.
    - iApply csimv_call; [iApply IHdirₛ; auto with language.. |].
      iIntros "%func %vₛ %vₜ %Hfunc #Hv".
      pose Ψ := sim_post_val tmc_dir_post.
      iApply (simv_apply_protocol _ Ψ). iIntros "%σₛ %σₜ $". iSplitR.
      { iLeft. iExists func, vₛ, vₜ. iFrame "#∗". do 2 (iSplitR; first done).
        iIntros "!> %vₛ' %vₜ' #Hv'". iExists vₛ', vₜ'. auto.
      }
      iIntros "!> % % (%vₛ' & %vₜ' & (-> & ->) & HΨ) !>".
      simv_post. iApply ("HΦ" with "HΨ").
    - iApply csimv_unop; [iApply IHdirₛ; auto with language | auto].
    - iApply csimv_binop; [iApply IHdirₛ; auto with language.. | auto].
    - iApply csimv_if; last iSplit; iApply IHdirₛ; auto with language.
    - iApply csimv_constr; [iApply IHdirₛ; auto with language.. | auto].
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      simv_constrₛ1.
      simv_apply simv_constr_valₜ1; first (iApply (IHdirₛ eₛ1); auto with language).
      iIntros "%vₛ1 %lₜ %vₜ1 Hlₜ0 Hlₜ1 Hlₜ2 #Hv1".
      simv_smart_apply (IHdpsₛ lₜ 𝟚 eₛ2 eₜ2.[#lₜ/] with "Hlₜ2 [Hlₜ0 Hlₜ1 HΦ]"); first 4 last.
      { autosubst. }
      { auto with language. }
      { eapply tmc_dps_subst; eauto; autosubst. }
      { auto with language. }
      iIntros "%vₛ2 % (%vₜ2 & -> & Hlₜ2 & #Hv2)".
      simv_constr_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      simv_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      simv_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      simv_heap_bij_insert.
      iApply "HΦ". iFrame "#∗". done.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      simv_constrₛ2.
      simv_apply simv_constr_valₜ2; first (iApply (IHdirₛ eₛ2); auto with language).
      iIntros "%vₛ2 %lₜ %vₜ2 Hlₜ0 Hlₜ1 Hlₜ2 #Hv2".
      simv_smart_apply (IHdpsₛ lₜ 𝟙 eₛ1 eₜ1.[#lₜ/] with "Hlₜ1 [Hlₜ0 Hlₜ2 HΦ]"); first 4 last.
      { autosubst. }
      { auto with language. }
      { eapply tmc_dps_subst; eauto; autosubst. }
      { auto with language. }
      iIntros "%vₛ1 % (%vₜ1 & -> & Hlₜ1 & #Hv1)".
      simv_constr_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      simv_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      simv_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      simv_heap_bij_insert.
      iApply "HΦ". iFrame "#∗". done.
    - auto with language.
    - iApply csimv_load; [iApply IHdirₛ; auto with language.. | auto].
    - iApply csimv_store; [iApply IHdirₛ; auto with language.. |].
      iApply "HΦ". done.
    (* tmc_dps *)
    - iIntros "%Γ % % (-> & ->) #HΓ". simv_simpl.
      simv_apply (IHdir with "[//] [Hpre HΦ]"); [done.. |]. iIntros "%vₛ %vₜ #Hv".
      simv_storeₜ.
      iApply "HΦ". iExists vₜ. iFrame "#∗". done.
    - iApply csimv_let.
      { iApply (IHdirₛ with "[//] []"); auto with language. }
      iApply (IHdpsₛ with "Hpre [HΦ]"); [auto with language.. |]. iIntros "%vₛ % (%vₜ & -> & Hdst' & #Hv)".
      iApply "HΦ". iExists vₜ. auto with iFrame.
    - iIntros "%Γ % % (-> & ->) #HΓ". simv_simpl.
      simv_apply (IHdirₛ with "[//] [Hpre HΦ] [//] HΓ"); [auto with language.. | ]. iIntros "%vₛ %vₜ #Hv".
      simv_pures.
      pose Ψ := sim_post_val (tmc_dps_post dst' idx').
      iApply (simv_apply_protocol _ Ψ). iIntros "%σₛ %σₜ $". iSplitL "Hpre".
      { iRight. iExists func, func_dps, vₛ, dst', idx', vₜ. iFrame "#∗".
        do 2 (iSplitR; first auto with language).
        iIntros "!> %vₛ' %vₜ' Hdst' #Hv'". iExists vₛ', ()%V. iSplit; first done.
        iExists vₜ'. auto with iFrame.
      }
      iIntros "!> % % (%vₛ' & % & (-> & ->) & %vₜ' & -> & Hdst' & #Hv') !>".
      simv_post. iApply "HΦ". iExists vₜ'. iFrame "#∗". done.
    - iApply csimv_if.
      { iApply (IHdirₛ with "[//] []"); auto with language. }
      iSplit;
        iApply (IHdpsₛ with "Hpre [HΦ]"); [auto with language.. |]; iIntros "%vₛ % (%vₜ & -> & Hdst' & #Hv)";
        iApply "HΦ"; iExists vₜ; auto with iFrame.
    - iIntros "%Γ % % (-> & ->) #HΓ". simv_simpl.
      simv_constrₛ1.
      simv_apply simv_constr_valₜ1.
      { simv_apply (IHdirₛ with "[//] [] [//] HΓ"); auto with language. }
      iIntros "%vₛ1 %lₜ %vₜ1 Hlₜ0 Hlₜ1 Hlₜ2 #Hv1".
      simv_storeₜ.
      simv_smart_apply (IHdpsₛ lₜ 𝟚 eₛ2 eₜ2.[#lₜ/] with "Hlₜ2 [Hpre Hlₜ0 Hlₜ1 HΦ] [] HΓ"); first 4 last.
      { autosubst. }
      { auto with language. }
      { eapply tmc_dps_subst; eauto; autosubst. }
      { auto with language. }
      iIntros "%vₛ2 % (%vₜ2 & -> & Hlₜ2 & #Hv2)".
      simv_constr_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      simv_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      simv_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      simv_heap_bij_insert.
      iApply "HΦ". iExists lₜ. iFrame. iSplitR; first done. iFrame "#∗". done.
    - iIntros "%Γ % % (-> & ->) #HΓ". simv_simpl.
      simv_constrₛ2.
      simv_apply simv_constr_valₜ2.
      { simv_apply (IHdirₛ with "[//] [] [//] HΓ"); auto with language. }
      iIntros "%vₛ2 %lₜ %vₜ2 Hlₜ0 Hlₜ1 Hlₜ2 #Hv2".
      simv_storeₜ.
      simv_smart_apply (IHdpsₛ lₜ 𝟙 eₛ1 eₜ1.[#lₜ/] with "Hlₜ1 [Hpre Hlₜ0 Hlₜ2 HΦ] [] HΓ"); first 4 last.
      { autosubst. }
      { auto with language. }
      { eapply tmc_dps_subst; eauto; autosubst. }
      { auto with language. }
      iIntros "%vₛ1 % (%vₜ1 & -> & Hlₜ1 & #Hv1)".
      simv_constr_detₛ as lₛ "Hlₛ0" "Hlₛ1" "Hlₛ2".
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ0 Hlₜ0 [//]") as "Hl0".
      simv_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ1 Hlₜ1 [//]") as "Hl1".
      simv_heap_bij_insert.
      iDestruct (sim_heap_bij_tie_eq_2 with "Hlₛ2 Hlₜ2 [//]") as "Hl2".
      simv_heap_bij_insert.
      iApply "HΦ". iExists lₜ. iFrame. iSplitR; first done. iFrame "#∗". done.
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

  Lemma tmc_simv_close eₛ eₜ Φ :
    SIM eₛ ≳ eₜ [[ tmc_protocol ]] [[ Φ ]] -∗
    SIM eₛ ≳ eₜ [[ Φ ]].
  Proof.
  Admitted.
End sim.

Section tmc_sound.
  Context {progₛ progₜ : program}.
  Context (Hwf : program_well_formed progₛ).
  Context (tmc : tmc progₛ progₜ).

  Notation Σ := sim_Σ.
  Notation M := (iResUR Σ).

  #[local] Instance tmc_sim_programs : SimPrograms ectx_language ectx_language :=
    Build_SimPrograms progₛ progₜ.

  #[local] Instance tmc_sim_GpreS :
    SimGpreS Σ.
  Proof.
    apply subG_sim_GpreS, subG_refl.
  Qed.

  Lemma tmc_sound :
    program_refinement progₛ progₜ.
  Proof.
    rewrite /program_refinement map_Forall_lookup => func eₛ Hfuncₛ vₛ vₜ Hvₛ Hv.
    pose proof (simv_adequacy' (M := M)) as Hadequacy. apply Hadequacy.
    iMod (sim_init ∅ ∅) as "(%sim_GS & Hsi & _ & _ & _ & _)".
    iModIntro. iExists _, _. iFrame. iSplitR.
    { clear dependent vₛ vₜ. iIntros "!> %vₛ %vₜ #Hv".
      iApply (val_bi_similar_similar with "Hv").
    }
    iApply (tmc_simv_close (sim_programs := tmc_sim_programs) tmc).
    iApply (simv_apply_protocol _ (sim_post_val (≈)%I)). iIntros "%σₛ %σₜ $ !>".
    iSplitL.
    - iLeft. iExists func, vₛ, vₜ. repeat iSplit; try done.
      + iPureIntro. simpl. eapply elem_of_dom_2. done.
      + iApply val_similar_bi_similar; done.
      + iIntros "%vₛ' %vₜ' #Hv'". iExists vₛ', vₜ'. auto with iFrame.
    - clear dependent vₛ eₛ vₜ. iIntros "%eₛ %eₜ (%vₛ & %vₜ & (-> & ->) & #Hv) !>".
      simv_post.
  Qed.
End tmc_sound.
