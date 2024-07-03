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
From camlcert.inline Require Export
  definition.
From camlcert.inline Require Import
  metatheory.
From camlcert Require Import
  options.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (inline : inline sim_progₛ sim_progₜ).

  Implicit Types func : data_function.
  Implicit Types annot : data_annotation.
  Implicit Types l lₛ lₜ : loc.
  Implicit Types v vₛ vₜ : data_val.
  Implicit Types e eₛ eₜ : data_expr.
  Implicit Types Φ : data_val → data_val → iProp Σ.
  Implicit Types Ψ : data_expr → data_expr → iProp Σ.

  Definition inline_protocol_dir Ψ eₛ eₜ : iProp Σ :=
    ∃ func annot vₛ vₜ,
    ⌜func ∈ dom sim_progₛ⌝ ∗
    ⌜eₛ = (DataFunc func annot) vₛ ∧ eₜ = (DataFunc func annot) vₜ⌝ ∗
    vₛ ≈ vₜ ∗
      ∀ vₛ' vₜ',
      vₛ' ≈ vₜ' -∗
      Ψ vₛ' vₜ'.
  Definition inline_protocol_inline Ψ eₛ eₜ : iProp Σ :=
    ∃ func annot defₛ e_funcₛ e_funcₜ vₛ vₜ,
    ⌜sim_progₛ !! func = Some defₛ ∧ e_funcₛ = defₛ.(data_definition_body) ∧ inline_expr sim_progₛ e_funcₛ e_funcₜ⌝ ∗
    ⌜eₛ = (DataFunc func annot) vₛ ∧ eₜ = (let: vₜ in e_funcₜ)%data_expr⌝ ∗
    vₛ ≈ vₜ ∗
      ∀ vₛ' vₜ',
      vₛ' ≈ vₜ' -∗
      Ψ vₛ' vₜ'.
  Definition inline_protocol Ψ eₛ eₜ : iProp Σ :=
    inline_protocol_dir Ψ eₛ eₜ ∨
    inline_protocol_inline Ψ eₛ eₜ.

  Definition inline_expr_spec eₛ eₜ :=
    data_program_scoped sim_progₛ →
    inline_expr sim_progₛ eₛ eₜ →
    data_expr_well_formed sim_progₛ eₛ →
    {{{ True }}} eₛ ⩾ eₜ [[ inline_protocol ]] {{{# (≈) }}}.

  Lemma inline_expr_specification eₛ eₜ :
    inline_expr_spec eₛ eₜ.
  Proof.
    intros Hprogₛ_scoped. induction 1 as
      [
      |
      | * Hinline1 IH1 Hinline2 IH2
      | * Hinline1 IH1 Hinline2 IH2
      | * Hfunc -> Hinline_func IHfunc Hinline IH
      | * Hinline IH
      | * Hinline1 IH1 Hinline2 IH2
      |
      | * Hinline0 IH0 Hinline1 IH1 Hinline2 IH2
      | * Hinline1 IH1 Hinline2 IH2
      |
      | * Hinline1 IH1 Hinline2 IH2
      | * Hinline1 IH1 Hinline2 IH2 Hinline3 IH3
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
        - iPureIntro.
          rewrite (subst_data_expr_scoped_1 _ ids); asimpl; try done.
          eapply data_expr_scoped_inline_expr; naive_solver.
        - rewrite /sim_post_vals'. iSmash.
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
    - iApply rsimv_block; last iSmash.
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

  Lemma inline_simv_close Φ eₛ eₜ :
    data_program_valid sim_progₛ →
    SIM eₛ ≳ eₜ [[ inline_protocol ]] {{# Φ }} -∗
    SIM eₛ ≳ eₜ {{# Φ }}.
  Proof.
    intros (Hprogₛ_wf & Hprogₛ_scoped).
    eapply data_program_scoped_inline in Hprogₛ_scoped as Hprogₜ_scoped; last done.
    iApply sim_close_pure_head_step. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ [Hprotocol | Hprotocol]".
    - iDestruct "Hprotocol" as "(%func & %annot & %vₛ & %vₜ & %Hfuncₛ & (-> & ->) & #Hv & HΨ)".
      simpl in Hfuncₛ. apply lookup_lookup_total_dom in Hfuncₛ.
      set defₛ := _ !!! _ in Hfuncₛ. set eₛ := defₛ.(data_definition_body).
      edestruct inline.(inline_transform) as (eₜ & Hdir & Hfuncₜ); first done.
      iExists _, _. iSplit; first eauto 10 with data_lang. sim_asimpl.
      erewrite (subst_data_program_scoped' ids inhabitant.ₛ# _ sim_progₛ); [| done..].
      erewrite (subst_data_program_scoped' ids inhabitant.ₜ# _ sim_progₜ); [| done..].
      iDestruct (inline_expr_specification $! (≈)%I with "[//] [] [//] []") as "Hsim"; eauto.
      + iApply (bisubst_cons_well_formed with "Hv").
        iApply bisubst_inhabitant_well_formed.
      + rewrite -bisubst_consₛ -bisubst_consₜ.
        sim_mono "Hsim". rewrite sim_post_vals_unseal. iSmash.
    - iDestruct "Hprotocol" as "(%func & %annot & %defₛ & %e_funcₛ & %e_funcₜ & %vₛ & %vₜ & (%Hfunc & -> & %Hinline_func) & (-> & ->) & #Hv & HΨ)".
      iExists _, _. iSplit; first eauto 10 with data_lang.
      iDestruct (inline_expr_specification $! (≈)%I with "[//] []") as "Hsim"; [auto with data_lang.. | naive_solver | iSmash |].
      erewrite (subst_data_program_scoped' ids inhabitant.ₛ# _ sim_progₛ); [| done..].
      rewrite (subst_data_expr_scoped_1' _ inhabitant.ₜ# vₜ).
      { eapply data_expr_scoped_inline_expr; [| done |]; naive_solver. }
      erewrite bisubst_consₛ, bisubst_consₜ.
      sim_mono "Hsim".
      + iApply (bisubst_cons_well_formed with "Hv").
        iApply bisubst_inhabitant_well_formed.
      + rewrite sim_post_vals_unseal. iSmash.
  Qed.
End sim_GS.

Section inline_sound.
  Context {progₛ progₜ : data_program}.
  Context (Hwf : data_program_valid progₛ).
  Context (inline : inline progₛ progₜ).

  Notation Σ :=
    sim_Σ.
  Notation M :=
    (iResUR Σ).

  #[local] Instance inline_sim_programs : SimPrograms data_ectx_lang data_ectx_lang :=
    Build_SimPrograms progₛ progₜ.

  #[local] Instance inline_sim_GpreS :
    SimGpreS Σ.
  Proof.
    apply subG_sim_GpreS, subG_refl.
  Qed.

  Lemma inline_sound :
    data_program_refinement progₛ progₜ.
  Proof.
    rewrite /data_program_refinement map_Forall_lookup => func eₛ Hfuncₛ vₛ vₜ Hvₛ Hv.
    pose proof (sim_adequacy' (M := M)) as Hadequacy. apply Hadequacy.
    iMod (sim_init ∅ ∅) as "(%sim_GS & Hsi & _ & _ & _ & _)".
    iModIntro. iExists _, _. iFrame. iSplitR.
    { clear dependent vₛ vₜ. iIntros "!> %vₛ %vₜ #Hv".
      iApply (data_val_bi_similar_similar with "Hv").
    }
    iApply (inline_simv_close (sim_programs := inline_sim_programs) inline); first done.
    iApply (sim_apply_protocol (sim_post_vals (≈)%I)). iIntros "%σₛ %σₜ $ !>".
    iSplitL.
    - iLeft. iExists func, [], vₛ, vₜ. repeat iSplit; try iSmash.
      + iPureIntro. simpl. eapply elem_of_dom_2. done.
      + iApply data_val_similar_bi_similar; done.
      + rewrite sim_post_vals_unseal /sim_post_vals'. iSmash.
    - clear dependent vₛ eₛ vₜ. iIntros "%eₛ %eₜ Hsimilar".
      rewrite sim_post_vals_unseal. sim_post.
  Qed.
End inline_sound.
