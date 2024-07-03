From camlcert Require Import
  prelude.
From camlcert.iris.program_logic Require Import
  sim.adequacy.
From camlcert.data_lang Require Import
  refinement
  subexpr
  sim.proofmode
  rsim.rules
  rsim.notations.
From camlcert.aps_plus_1 Require Export
  definition.
From camlcert.aps_plus_1 Require Import
  metatheory.
From camlcert Require Import
  options.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (aps_plus : aps_plus sim_progₛ sim_progₜ).

  Implicit Types acc : Z.
  Implicit Types func func_aps : data_function.
  Implicit Types annot : data_annotation.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types v vₛ vₜ : data_val.
  Implicit Types e eₛ eₜ : data_expr.
  Implicit Types Φ Ψ : data_expr → data_expr → iProp Σ.

  Definition aps_plus_protocol_dir Ψ eₛ eₜ : iProp Σ :=
    ∃ func annot vₛ vₜ,
    ⌜func ∈ dom sim_progₛ⌝ ∗
    ⌜eₛ = (DataFunc func annot) vₛ ∧ eₜ = (DataFunc func annot) vₜ⌝ ∗
    vₛ ≈ vₜ ∗
      ∀ vₛ' vₜ',
      vₛ' ≈ vₜ' -∗
      Ψ vₛ' vₜ'.
  Definition aps_plus_protocol_aps Ψ eₛ eₜ : iProp Σ :=
    ∃ func annot vₛ func_aps l acc vₜ,
    ⌜func ∈ dom sim_progₛ ∧ aps_plus.(aps_plus_ξ) !! func = Some func_aps⌝ ∗
    ⌜eₛ = (DataFunc func annot) vₛ ∧ eₜ = (DataFunc func_aps annot) l⌝ ∗
    (l +ₗ 1) ↦ₜ acc ∗ (l +ₗ 2) ↦ₜ vₜ ∗
    vₛ ≈ vₜ ∗
      ∀ vₛ' eₜ',
      ⌜if vₛ' is DataInt n then eₜ' = (acc + n)%Z else strongly_stuck sim_progₜ eₜ'⌝ -∗
      Ψ vₛ' eₜ'.
  Definition aps_plus_protocol Ψ eₛ eₜ : iProp Σ :=
    aps_plus_protocol_dir Ψ eₛ eₜ ∨
    aps_plus_protocol_aps Ψ eₛ eₜ.

  Lemma aps_plus_protocol_aps' Φ func annot vₛ func_aps acc vₜ :
    func ∈ dom sim_progₛ →
    aps_plus.(aps_plus_ξ) !! func = Some func_aps →
    vₛ ≈ vₜ -∗
    ( ∀ vₛ' eₜ',
      ⌜if vₛ' is DataInt n then eₜ' = (acc + n)%Z else strongly_stuck sim_progₜ eₜ'⌝ -∗
      Φ vₛ' eₜ'
    ) -∗
    SIM (DataFunc func annot) vₛ ≳ (DataFunc func_aps annot) (acc, vₜ) [[ aps_plus_protocol ]] {{ Φ }}.
  Proof.
    iIntros "%Hfuncₛ %Hξ #Hv HΦ".
    sim_blockₜ;
      sim_block_detₜ as l "Hl0" "Hl1" "Hl2";
      sim_apply (sim_apply_protocol Φ _ _ ((DataFunc func annot) vₛ) ((DataFunc func_aps annot) l)); iIntros "%σₛ %σₜ $ !>";
      (iSplitL; [iSmash | iIntros "%eₛ %eₜ HΦ"; sim_post]).
  Qed.

  Definition aps_plus_expr_dir_post :=
    sim_post_vals' (≈).
  Definition aps_plus_expr_aps_post acc eₛ eₜ : iProp Σ :=
    ∃ vₛ,
    ⌜eₛ = vₛ⌝ ∗
    ⌜if vₛ is DataInt n then eₜ = (acc + n)%Z else strongly_stuck sim_progₜ eₜ⌝.

  Definition aps_plus_expr_dir_spec' eₛ eₜ :=
    data_expr_well_formed sim_progₛ eₛ →
    {{{ True }}} eₛ ⩾ eₜ [[ aps_plus_protocol ]] {{{ aps_plus_expr_dir_post }}}.
  Definition aps_plus_expr_dir_spec eₛ eₜ :=
    aps_plus_expr_dir aps_plus.(aps_plus_ξ) eₛ eₜ →
    aps_plus_expr_dir_spec' eₛ eₜ.
  Definition aps_plus_expr_aps_spec' acc eₛ eₜ :=
    data_expr_well_formed sim_progₛ eₛ →
    {{{ True }}} eₛ ⩾ eₜ [[ aps_plus_protocol ]] {{{ aps_plus_expr_aps_post acc }}}.
  Definition aps_plus_expr_aps_spec acc eₛ eₜ :=
    aps_plus_expr_aps aps_plus.(aps_plus_ξ) acc eₛ eₜ →
    aps_plus_expr_aps_spec' acc eₛ eₜ.
  Definition aps_plus_expr_spec eₛ eₜ :=
    aps_plus_expr_dir_spec eₛ eₜ ∧
    ∀ acc, aps_plus_expr_aps_spec acc eₛ eₜ.

  Lemma aps_plus_expr_specification eₛ eₜ :
    aps_plus_expr_spec eₛ eₜ.
  Proof.
    revert eₜ. induction eₛ as [eₛ IHeₛ] using (well_founded_ind data_subexpr_wf).
    cut (
      ( ∀ eₛ eₜ,
        aps_plus_expr_dir aps_plus.(aps_plus_ξ) eₛ eₜ →
        (∀ eₛ' eₜ', eₛ' ⊏ eₛ → aps_plus_expr_dir_spec eₛ' eₜ') →
        (∀ acc eₛ' eₜ', eₛ' ⊏ eₛ → aps_plus_expr_aps_spec acc eₛ' eₜ') →
        aps_plus_expr_dir_spec' eₛ eₜ
      ) ∧ (
        ∀ (acc : data_expr) eₛ eₜ,
        aps_plus_expr_aps aps_plus.(aps_plus_ξ) acc eₛ eₜ →
        (∀ eₛ' eₜ', eₛ' ⊏ eₛ → aps_plus_expr_dir_spec eₛ' eₜ') →
        (∀ acc eₛ' eₜ', eₛ' ⊏ eₛ → aps_plus_expr_aps_spec acc eₛ' eₜ') →
        ∀ acc',
        acc = acc' →
        aps_plus_expr_aps_spec' acc' eₛ eₜ
      )
    ). {
      rewrite /aps_plus_expr_spec /aps_plus_expr_dir_spec /aps_plus_expr_aps_spec in IHeₛ |- *.
      naive_solver.
    }
    clear eₛ IHeₛ. apply aps_plus_expr_ind;
      rewrite /aps_plus_expr_dir_spec' /aps_plus_expr_dir_post /sim_post_vals' /aps_plus_expr_aps_spec';
      intros *;
      [ intros _ _
      | intros _ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir _ IHdirₛ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Haps _ _ IHapsₛ
      | intros Haps _ _ IHapsₛ
      | intros _ _ _ _ _ _
      | intros Hdir0 _ Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros _ _ _ _ _ _
      | intros Hdir1 _ Hdir2 _ IHdirₛ _
      | intros Hdir1 _ Hdir2 _ Hdir3 _ IHdirₛ _
      | intros _ IHdir IHdirₛ IHapsₛ acc' ->
      | intros Hdir1 _ Haps2 _ IHdirₛ IHapsₛ acc' ->
      | intros Hfunc Hdir _ -> IHdirₛ _ acc' ->
      | intros Haps _ _ IHapsₛ acc' ->
      | intros Haps _ _ IHapsₛ acc' ->
      | intros Hdir0 _ Haps1 _ Haps2 _ IHdirₛ IHapsₛ acc' ->
      ];
      iIntros "%Hwf %Φ _ HΦ".
    (* aps_plus_expr_dir *)
    - iApply rsim_val; [done | iSmash].
    - iApply rsim_var. iSmash.
    - iApply rsim_let;
        iApply IHdirₛ; auto with data_lang.
    - iApply rsim_call;
        [iApply IHdirₛ; auto with data_lang.. |].
      iIntros "%func %annot %vₛ %vₜ %Hfunc #Hv".
      iApply (sim_apply_protocol aps_plus_expr_dir_post). iIntros "%σₛ %σₜ $ !>". iSplitR.
      { rewrite /aps_plus_expr_dir_post /sim_post_vals'. iSmash. }
      iIntros "% % (%vₛ' & %vₜ' & (-> & ->) & HΨ)".
      sim_post.
    - iApply rsim_unop; last iSmash.
      iApply IHdirₛ; auto with data_lang.
    - iApply rsim_binop; last iSmash;
        iApply IHdirₛ; auto with data_lang.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_binopₛ1.
      sim_apply (IHapsₛ with "[//] [HΦ]"); [auto with data_lang.. |].
      iIntros "% %eₜ' (%vₛ & -> & %Heₜ')".
      destruct vₛ;
        sim_pures;
        iApply sim_strongly_stuck; auto with data_lang.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_binopₛ2.
      sim_apply (IHapsₛ with "[//] [HΦ]"); [auto with data_lang.. |].
      iIntros "% %eₜ' (%vₛ & -> & %Heₜ')".
      destruct vₛ;
        sim_pures;
        iApply sim_strongly_stuck; auto with data_lang.
    - iSmash.
    - iApply rsim_if; last iSplit;
        iApply IHdirₛ; auto with data_lang.
    - iApply rsim_block; last iSmash;
        iApply IHdirₛ; auto with data_lang.
    - iSmash.
    - iApply rsim_load; last iSmash;
       iApply IHdirₛ; auto with data_lang.
    - iApply rsim_store; last iSmash;
        iApply IHdirₛ; auto with data_lang.
    (* aps_plus_expr_aps *)
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_binopₜ;
        (sim_apply (IHdir with "[//] [HΦ]"); [auto with data_lang.. |]);
        iIntros "% % (%vₛ & %vₜ & (-> & ->) & #Hv)";
        destruct vₛ, vₜ; try iDestruct "Hv" as %[];
        sim_pures;
        sim_post; iModIntro;
        iApply "HΦ"; iExists _; auto with data_lang.
    - iApply rsim_let.
      { iApply (IHdirₛ with "[//] []"); auto with data_lang. }
      iApply (IHapsₛ with "[//] [HΦ]"); [auto with data_lang.. | iSmash].
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply (IHdirₛ with "[//] [HΦ] [//] HΓ"); [auto with data_lang.. |].
      iIntros "% % (%vₛ & %vₜ & (-> & ->) & #Hv)".
      sim_apply (aps_plus_protocol_aps' with "Hv"); auto with data_lang.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply sim_binop_valsₜ. sim_post.
      sim_pures.
      sim_binopₛ2.
      sim_apply (IHapsₛ (acc' + n)%Z eₛ eₜ.[#(acc' + n)/] with "[//] [HΦ]"); first 4 last.
      { naive_solver autosubst. }
      { auto with data_lang. }
      { eapply aps_plus_expr_aps_subst; eauto; autosubst. }
      { auto with data_lang. }
      iIntros "% %eₜ' (%vₛ & -> & %Heₜ')".
      sim_pures.
      destruct vₛ; try solve [iApply sim_strongly_stuck; auto with data_lang]. subst eₜ'.
      sim_pures.
      iApply "HΦ". iModIntro. iExists _. iSplit; first iSmash.
      iPureIntro. do 2 f_equal. lia.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply sim_binop_valsₜ. sim_post.
      sim_pures.
      sim_binopₛ1.
      sim_apply (IHapsₛ (acc' + n)%Z eₛ eₜ.[#(acc' + n)/] with "[//] [HΦ]"); first 4 last.
      { naive_solver autosubst. }
      { auto with data_lang. }
      { eapply aps_plus_expr_aps_subst; eauto; autosubst. }
      { auto with data_lang. }
      iIntros "% %eₜ' (%vₛ & -> & %Heₜ')".
      sim_pures.
      destruct vₛ; try solve [iApply sim_strongly_stuck; auto with data_lang]. subst eₜ'.
      sim_pures.
      iApply "HΦ". iModIntro. iExists _. iSplit; first iSmash.
      iPureIntro. do 2 f_equal. lia.
    - iApply rsim_if.
      { iApply (IHdirₛ with "[//] []"); auto with data_lang. }
      iSplit;
        iApply (IHapsₛ with "[//] [HΦ]"); [auto with data_lang.. | iSmash].
  Qed.
  Lemma aps_plus_expr_dir_specification eₛ eₜ :
    aps_plus_expr_dir_spec eₛ eₜ.
  Proof.
    eapply proj1, aps_plus_expr_specification.
  Qed.
  Lemma aps_plus_expr_aps_specification acc eₛ eₜ :
    aps_plus_expr_aps_spec acc eₛ eₜ.
  Proof.
    revert acc. eapply proj2, aps_plus_expr_specification.
  Qed.

  Lemma aps_plus_sim_close Φ eₛ eₜ :
    data_program_valid sim_progₛ →
    SIM eₛ ≳ eₜ [[ aps_plus_protocol ]] {{ Φ }} -∗
    SIM eₛ ≳ eₜ {{ Φ }}.
  Proof.
    intros (Hprogₛ_wf & Hprogₛ_scoped).
    eapply data_program_scoped_aps_plus in Hprogₛ_scoped as Hprogₜ_scoped; last done.
    iApply sim_close_pure_head_step. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ [Hprotocol | Hprotocol]".
    - iDestruct "Hprotocol" as "(%func & %annot & %vₛ & %vₜ & %Hfuncₛ & (-> & ->) & #Hv & HΨ)".
      simpl in Hfuncₛ. apply lookup_lookup_total_dom in Hfuncₛ.
      set defₛ := _ !!! _ in Hfuncₛ. set eₛ := defₛ.(data_definition_body).
      edestruct aps_plus.(aps_plus_dir) as (eₜ & Hdir & Hfuncₜ); first done.
      iExists _, _. iSplit; first eauto 10 with data_lang.
      erewrite (subst_data_program_scoped' ids inhabitant.ₛ# _ sim_progₛ); [| done..].
      erewrite (subst_data_program_scoped' ids inhabitant.ₜ# _ sim_progₜ); [| done..].
      iDestruct (aps_plus_expr_dir_specification $! aps_plus_expr_dir_post with "[//] [] [//] []") as "Hsim"; eauto.
      + iApply (bisubst_cons_well_formed with "Hv").
        iApply bisubst_inhabitant_well_formed.
      + rewrite -bisubst_consₛ -bisubst_consₜ.
        sim_mono "Hsim".
    - iDestruct "Hprotocol" as "(%func & %annot & %vₛ & %func_aps & %l & %acc & %vₜ & (%Hfuncₛ & %Hξ) & (-> & ->) & Hl1 & Hl2 & #Hv & HΨ)".
      simpl in Hfuncₛ. apply lookup_lookup_total_dom in Hfuncₛ.
      set defₛ := _ !!! _ in Hfuncₛ. set eₛ := defₛ.(data_definition_body).
      edestruct aps_plus.(aps_plus_aps) as (eₜ & Haps & Hfunc_apsₜ); [done.. |].
      iExists _, _. iSplit; first eauto 10 with data_lang.
      do 2 sim_loadₜ. sim_pures.
      eapply (aps_plus_expr_aps_subst _ (ids 0 .: #acc .: ren (+1))) in Haps; [| autosubst..].
      erewrite (subst_data_program_scoped' _ (ren (+1)) _ sim_progₛ) in Haps; [| done..]. asimpl in Haps.
      replace eₜ.[#vₜ, #acc, #l/] with eₜ.[ids 0 .: #acc .: ren (+1)].[#vₜ, #l/] by autosubst.
      erewrite (subst_data_program_scoped' ids inhabitant.ₛ# _ sim_progₛ); [| done..].
      erewrite (subst_data_expr_scoped_1' (#l .: ids) inhabitant.ₜ#); last first.
      { eapply data_expr_scoped_aps_plus_expr_aps; naive_solver. }
      iDestruct (aps_plus_expr_aps_specification $! (aps_plus_expr_aps_post acc) with "[//] [] [//] []") as "Hsim"; eauto.
      + iApply (bisubst_cons_well_formed with "Hv").
        iApply bisubst_inhabitant_well_formed.
      + rewrite -bisubst_consₛ -bisubst_consₜ. asimpl.
        sim_mono "Hsim".
  Qed.
End sim_GS.

Section aps_plus_sound.
  Context {progₛ progₜ : data_program}.
  Context (Hwf : data_program_valid progₛ).
  Context (aps_plus : aps_plus progₛ progₜ).

  Notation Σ :=
    sim_Σ.
  Notation M :=
    (iResUR Σ).

  #[local] Instance aps_plus_sim_programs : SimPrograms data_ectx_lang data_ectx_lang :=
    Build_SimPrograms progₛ progₜ.

  #[local] Instance aps_plus_sim_GpreS :
    SimGpreS Σ.
  Proof.
    apply subG_sim_GpreS, subG_refl.
  Qed.

  Lemma aps_plus_sound :
    data_program_refinement progₛ progₜ.
  Proof.
    rewrite /data_program_refinement map_Forall_lookup => func eₛ Hfuncₛ vₛ vₜ Hvₛ Hv.
    pose proof (sim_adequacy' (M := M)) as Hadequacy. apply Hadequacy.
    iMod (sim_init ∅ ∅) as "(%sim_GS & Hsi & _ & _ & _ & _)".
    iModIntro. iExists _, _. iFrame. iSplitR.
    { clear dependent vₛ vₜ. iIntros "!> %vₛ %vₜ #Hv".
      iApply (data_val_bi_similar_similar with "Hv").
    }
    iApply (aps_plus_sim_close (sim_programs := aps_plus_sim_programs) aps_plus); first done.
    iApply (sim_apply_protocol (sim_post_vals (≈)%I)). iIntros "%σₛ %σₜ $ !>".
    iSplitL.
    - iLeft. iExists func, [], vₛ, vₜ. repeat iSplit; try iSmash.
      + iPureIntro. simpl. eapply elem_of_dom_2. done.
      + iApply data_val_similar_bi_similar; done.
      + rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    - clear dependent vₛ eₛ vₜ. iIntros "%eₛ %eₜ Hsimilar".
      rewrite sim_post_vals_unseal. sim_post.
  Qed.
End aps_plus_sound.
