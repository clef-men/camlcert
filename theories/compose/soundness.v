From simuliris Require Import
  prelude.
From simuliris.iris.program_logic Require Import
  sim.adequacy.
From simuliris.data_lang Require Import
  refinement
  subexpr
  sim.proofmode
  rsim.rules
  rsim.notations.
From simuliris.compose Require Export
  definition.
From simuliris.compose Require Import
  metatheory.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context {func1 func2} (compose : compose func1 func2 sim_progₛ sim_progₜ).

  Implicit Types func : data_function.
  Implicit Types annot : data_annotation.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types v vₛ vₜ : data_val.
  Implicit Types e eₛ eₜ : data_expr.
  Implicit Types Φ : data_val → data_val → iProp Σ.
  Implicit Types Ψ : data_expr → data_expr → iProp Σ.

  Definition compose_protocol_dir Ψ eₛ eₜ : iProp Σ :=
    ∃ func annot1 annot2 vₛ vₜ,
    ⌜func ∈ dom sim_progₛ⌝ ∗
    ⌜eₛ = (DataFunc func annot1) vₛ ∧ eₜ = (DataFunc func annot2) vₜ⌝ ∗
    vₛ ≈ vₜ ∗
      ∀ vₛ' vₜ',
      vₛ' ≈ vₜ' -∗
      Ψ vₛ' vₜ'.
  Definition compose_protocol_comp Ψ eₛ eₜ : iProp Σ :=
    ∃ annot1 annot2 vₛ vₜ,
    ⌜eₛ = (DataFunc func2 annot2) ((DataFunc func1 annot1) vₛ) ∧ eₜ = (DataFunc compose.(compose_func) annot1) vₜ⌝ ∗
    vₛ ≈ vₜ ∗
      ∀ vₛ' vₜ',
      vₛ' ≈ vₜ' -∗
      Ψ vₛ' vₜ'.
  Definition compose_protocol Ψ eₛ eₜ : iProp Σ :=
    compose_protocol_dir Ψ eₛ eₜ ∨
    compose_protocol_comp Ψ eₛ eₜ.

  Definition compose_expr_dir_spec eₛ eₜ :=
    compose_expr_dir func1 func2 compose.(compose_func) eₛ eₜ →
    data_expr_well_formed sim_progₛ eₛ →
    {{{ True }}} eₛ ⩾ eₜ [[ compose_protocol ]] {{{# (≈) }}}.

  Lemma compose_expr_dir_specification eₛ eₜ :
    compose_expr_dir_spec eₛ eₜ.
  Proof.
    induction 1 as
      [
      |
      | * Hdir1 IH1 Hdir2 IH2
      | * Hdir1 IH1 Hdir2 IH2
      | * Hdir IH
      | * Hdir IH
      | * Hdir1 IH1 Hdir2 IH2
      |
      | * Hdir0 IH0 Hdir1 IH1 Hdir2 IH2
      | * Hdir1 IH1 Hdir2 IH2
      |
      | * Hdir1 IH1 Hdir2 IH2
      | * Hdir1 IH1 Hdir2 IH2 Hdir3 IH3
      ];
      iIntros "%Hwf %Φ _ HΦ".
    - iApply rsimv_val; [done | iSmash].
    - iApply rsimv_var. iSmash.
    - iApply rsimv_let.
      + iApply IH1; auto with data_lang.
      + iApply IH2; auto with data_lang.
    - iApply rsimv_call.
      + iApply IH1; auto with data_lang.
      + iApply IH2; auto with data_lang.
      + iIntros "%func %annot %vₛ %vₜ %Hfunc #Hv".
        iApply (sim_apply_protocol (sim_post_vals' (≈))). iIntros "%σₛ %σₜ $ !>". iSplitR.
        { rewrite /sim_post_vals'. iSmash. }
        iIntros "% % (%vₛ' & %vₜ' & (-> & ->) & HΨ)".
        sim_post.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply (IH with "[//] [HΦ]"); first auto with data_lang.
      iIntros "%vₛ %vₜ #Hv".
      iApply (sim_apply_protocol (sim_post_vals' (≈))). iIntros "%σₛ %σₜ $ !>". iSplitR.
      { iRight. repeat iExists _. repeat iSplit; try iSmash.
        rewrite /sim_post_vals'. iSmash.
      }
      iIntros "% % (%vₛ' & %vₜ' & (-> & ->) & #Hv')".
      sim_post.
    - iApply rsimv_unop; last iSmash.
      iApply IH; auto with data_lang.
    - iApply rsimv_binop; last iSmash.
      + iApply IH1; auto with data_lang.
      + iApply IH2; auto with data_lang.
    - iSmash.
    - iApply rsimv_if; last iSplit.
      + iApply IH0; auto with data_lang.
      + iApply IH1; auto with data_lang.
      + iApply IH2; auto with data_lang.
    - iApply rsimv_constr; last iSmash.
      + iApply IH1; auto with data_lang.
      + iApply IH2; auto with data_lang.
    - iSmash.
    - iApply rsimv_load; last iSmash.
      + iApply IH1; auto with data_lang.
      + iApply IH2; auto with data_lang.
    - iApply rsimv_store; last iSmash.
      + iApply IH1; auto with data_lang.
      + iApply IH2; auto with data_lang.
      + iApply IH3; auto with data_lang.
  Qed.

  Definition compose_expr_comp_spec annot eₛ eₜ :=
    compose_expr_comp func1 func2 compose.(compose_func) eₛ eₜ →
    data_expr_well_formed sim_progₛ eₛ →
    {{{ True }}} (DataFunc func2 annot) eₛ ⩾ eₜ [[ compose_protocol ]] {{{# (≈) }}}.

  Lemma compose_expr_comp_specification annot eₛ eₜ :
    compose_expr_comp_spec annot eₛ eₜ.
  Proof.
    induction 1 as
      [ * Hdir
      | * Hdir1 Hcomp2 IH2
      | * Hdir
      | * Hdir0 Hcomp1 IH1 Hcomp2 IH2
      ];
      iIntros "%Hwf %Φ _ HΦ".
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply (compose_expr_dir_specification with "[//] [HΦ]").
      iIntros "%vₛ %vₜ #Hv".
      iApply (sim_apply_protocol (sim_post_vals' (≈))). iIntros "%σₛ %σₜ $ !>". iSplitR.
      { pose proof compose.(compose_defined2). rewrite /sim_post_vals'. iSmash. }
      iIntros "% % (%vₛ' & %vₜ' & (-> & ->) & HΨ)".
      sim_post.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply (compose_expr_dir_specification with "[//] [HΦ]"); first auto with data_lang.
      iIntros "%vₛ1 %vₜ1 #Hv1".
      sim_pures.
      erewrite bisubst_consₛ, bisubst_consₜ.
      iApply (IH2 with "[//] [HΦ]"); first 2 last.
      { autosubst. }
      { iApply (bisubst_cons_well_formed with "Hv1 HΓ"). }
      { auto with data_lang. }
      iSmash.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      sim_apply (compose_expr_dir_specification with "[//] [HΦ]"); first auto with data_lang.
      iIntros "%vₛ %vₜ #Hv".
      iApply (sim_apply_protocol (sim_post_vals' (≈))). iIntros "%σₛ %σₜ $ !>". iSplitR.
      { rewrite /sim_post_vals'. iSmash. }
      iIntros "% % (%vₛ' & %vₜ' & (-> & ->) & HΨ)".
      sim_post.
    - iIntros "%Γ % % (-> & ->) #HΓ /=".
      rewrite sim_post_vals_unseal. sim_bindₛ (if: _ then _ else _)%data_expr.
      sim_apply sim_if.
      { rewrite -simv_unseal.
        sim_apply (compose_expr_dir_specification with "[//]"); first auto with data_lang.
      }
      iSplit; sim_post; rewrite -simv_unseal.
      + iApply (IH1 with "[//] [HΦ] [] HΓ"); first 2 last.
        { autosubst. }
        { auto with data_lang. }
        iSmash.
      + iApply (IH2 with "[//] [HΦ] [] HΓ"); first 2 last.
        { autosubst. }
        { auto with data_lang. }
        iSmash.
  Qed.

  Lemma compose_simv_close Φ eₛ eₜ :
    data_program_valid sim_progₛ →
    SIM eₛ ≳ eₜ [[ compose_protocol ]] {{# Φ }} -∗
    SIM eₛ ≳ eₜ {{# Φ }}.
  Proof.
    intros (Hprogₛ_wf & Hprogₛ_scoped).
    eapply data_program_scoped_compose in Hprogₛ_scoped as Hprogₜ_scoped; last done.
    iApply sim_close_pure_step. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ [Hprotocol | Hprotocol]".
    - iDestruct "Hprotocol" as "(%func & %annot1 & %annot2 & %vₛ & %vₜ & %Hfuncₛ & (-> & ->) & #Hv & HΨ)".
      simpl in Hfuncₛ. apply lookup_lookup_total_dom in Hfuncₛ.
      set defₛ := _ !!! _ in Hfuncₛ. set eₛ := defₛ.(data_definition_body).
      edestruct compose.(compose_dir) as (eₜ & Hdir & Hfuncₜ); first done.
      iExists _, _. iSplit; first eauto 10 with data_lang. sim_asimpl.
      erewrite (subst_data_program_scoped' ids inhabitant.ₛ# _ sim_progₛ); [| done..].
      erewrite (subst_data_program_scoped' ids inhabitant.ₜ# _ sim_progₜ); [| done..].
      iDestruct (compose_expr_dir_specification $! (≈)%I with "[//] [] [//] []") as "Hsim"; eauto.
      + iApply (bisubst_cons_well_formed with "Hv").
        iApply bisubst_inhabitant_well_formed.
      + rewrite -bisubst_consₛ -bisubst_consₜ.
        sim_mono "Hsim". rewrite sim_post_vals_unseal. iSmash.
    - iDestruct "Hprotocol" as "(%annot1 & %annot2 & %vₛ & %vₜ & (-> & ->) & #Hv & HΨ)".
      destruct compose.(compose_comp) as (defₛ & eₜ & Hfunc1ₛ & Hcomp & Hfuncₜ).
      pose K := [DataEctxiCall1 (DataFunc func2 annot2)].
      iExists (K @@ _), _. iSplit.
      { iPureIntro. split; last eauto with data_lang.
        change ((DataFunc func2 annot2) ((DataFunc func1 annot1) vₛ)) with (K @@ (DataFunc func1 annot1) vₛ).
        eapply pure_head_step_fill_pure_step. eauto with data_lang.
      }
      rewrite /K. simplify.
      iDestruct (compose_expr_comp_specification $! (≈)%I with "[//] []") as "Hsim"; [auto with data_lang.. | naive_solver | iSmash |].
      erewrite (subst_data_program_scoped' ids inhabitant.ₛ# _ sim_progₛ); [| done..].
      rewrite (subst_data_expr_scoped_1' _ inhabitant.ₜ# vₜ); last first.
      { eapply data_expr_scoped_compose_expr_comp; naive_solver. }
      erewrite bisubst_consₛ, bisubst_consₜ.
      iApply (sim_mono' with "[Hsim] [HΨ]").
      + iApply "Hsim".
        * autosubst.
        * iApply (bisubst_cons_well_formed with "Hv").
          iApply bisubst_inhabitant_well_formed.
      + rewrite sim_post_vals_unseal. iSmash.
  Qed.
End sim_GS.

Section compose_sound.
  Context {progₛ progₜ : data_program}.
  Context (Hwf : data_program_valid progₛ).
  Context {func1 func2} (compose : compose func1 func2 progₛ progₜ).

  Notation Σ :=
    sim_Σ.
  Notation M :=
    (iResUR Σ).

  #[local] Instance compose_sim_programs : SimPrograms data_ectx_lang data_ectx_lang :=
    Build_SimPrograms progₛ progₜ.

  #[local] Instance compose_sim_GpreS :
    SimGpreS Σ.
  Proof.
    apply subG_sim_GpreS, subG_refl.
  Qed.

  Lemma compose_sound :
    data_program_refinement progₛ progₜ.
  Proof.
    rewrite /data_program_refinement map_Forall_lookup => func eₛ Hfuncₛ vₛ vₜ Hvₛ Hv.
    pose proof (sim_adequacy' (M := M)) as Hadequacy. apply Hadequacy.
    iMod (sim_init ∅ ∅) as "(%sim_GS & Hsi & _ & _ & _ & _)".
    iModIntro. iExists _, _. iFrame. iSplitR.
    { clear dependent vₛ vₜ. iIntros "!> %vₛ %vₜ #Hv".
      iApply (data_val_bi_similar_similar with "Hv").
    }
    iApply (compose_simv_close (sim_programs := compose_sim_programs) compose); first done.
    iApply (sim_apply_protocol (sim_post_vals (≈)%I)). iIntros "%σₛ %σₜ $ !>".
    iSplitL.
    - iLeft. iExists func, [], [], vₛ, vₜ. repeat iSplit; try iSmash.
      + iPureIntro. simpl. eapply elem_of_dom_2. done.
      + iApply data_val_similar_bi_similar; done.
      + rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    - clear dependent vₛ eₛ vₜ. iIntros "%eₛ %eₜ Hsimilar".
      rewrite sim_post_vals_unseal. sim_post.
  Qed.
End compose_sound.
