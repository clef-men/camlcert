From Paco Require Import
  paco.

From iris.base_logic Require Import
  bi.

From simuliris Require Import
  prelude.
From simuliris.common Require Import
  induction.
From simuliris.program_logic Require Import
  refinement
  idiverges
  bisim.proofmode
  bisim.notations.

Section bisim.
  Context `{!Similar (val Λₛ) (val Λₜ)}.
  Context `{sim_programs : !SimPrograms Λₛ Λₜ}.
  Context {M : ucmra}.
  Notation PROP := (uPredI M).

  Lemma bisim_adequacy_convergesₛ eₛ e_finalₛ σₛ eₜ σₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp σₛ σₜ ∗
        BISIM eₛ ≃ eₜ {{# (≈) }}
    ) →
    let bₛ := behaviour_converges e_finalₛ in
    has_behaviour sim_progₛ eₛ σₛ bₛ →
      ∃ e_finalₜ,
      let bₜ := behaviour_converges e_finalₜ in
      has_behaviour sim_progₜ eₜ σₜ bₜ ∧
      behaviour_refinement bₜ bₛ.
  Proof.
    intros Hbisim bₛ Hbₛ.
    invert Hbₛ as [? σ_finalₛ ((n & Hstepsₛ)%rtc_nsteps & Hirreducibleₛ) |].
    apply (uPred.pure_soundness (M := M)).
    iMod Hbisim as "(%sim_state & % & #val_bi_similar_similar & Hsi & Hbisim)". clear Hbisim.
    iInduction n as [n] "IH" using nat_strong_ind forall (eₛ σₛ eₜ σₜ Hstepsₛ).
    set I : sim_protocol_O PROP Λₛ Λₜ := λ Φ _eₛ eₜ, (
      ∀ σₜ,
      (∀ eₛ eₜ, Φ eₛ eₜ -∗ sim_post_vals (≈) eₛ eₜ) -∗
      ⌜_eₛ = eₛ⌝ -∗
      sim_state_interp σₛ σₜ -∗
      ⌜ ∃ e_finalₜ,
        let bₜ := behaviour_converges e_finalₜ in
        has_behaviour sim_progₜ eₜ σₜ bₜ ∧
        behaviour_refinement bₜ bₛ
      ⌝
    )%I.
    iAssert (I (sim_post_vals (≈)%I) eₛ eₜ) with "[Hbisim]" as "HI"; last first.
    { iApply ("HI" with "[] [//] Hsi"). iSmash. }
    rewrite /bisimv bisim_fixpoint. iApply (bisim_inner_strong_ind with "[] Hbisim"); [solve_proper.. |].
    clear eₜ σₜ. iIntros "!> %Φ % %eₜ Hbisim % Hsimilar -> Hsi".
    iMod ("Hbisim" with "Hsi") as "[Hbisim | [Hbisim | [Hbisim | [Hbisim | Hbisim]]]]".
    - iDestruct "Hbisim" as "(_ & [Hbisim | Hbisim])".
      + iDestruct "Hbisim" as "(%Hstuckₛ & %Hstuckₜ)".
        iPureIntro. exists eₜ. split.
        * econstructor. split; first apply rtc_refl.
          apply stuck_irreducible. done.
        * invert Hstepsₛ as [| n' ? (eₛ', σₛ') ? Hstepₜₛ_]; last first.
          { eelim irreducible_not_reducible_1.
            - apply stuck_irreducible, Hstuckₛ.
            - exists eₛ', σₛ'. apply step_prim_step. done.
          }
          apply behaviour_refinement_stuck; [apply Hstuckₜ | apply Hstuckₛ].
      + rewrite sim_post_vals_unseal.
        iDestruct ("Hsimilar" with "Hbisim") as "(%vₛ & %vₜ & (-> & ->) & Hv)".
        iDestruct ("val_bi_similar_similar" with "Hv") as %Hv.
        iPureIntro. exists (of_val vₜ). split.
        * econstructor. split; [apply rtc_refl | by eapply val_irreducible].
        * invert Hstepsₛ as [| n' ? (eₛ', σₛ') ? Hstepₛ _]; last first.
          { eelim irreducible_not_reducible_1; first last.
            - exists eₛ', σₛ'. apply step_prim_step. done.
            - eapply val_irreducible. done.
          }
          eapply behaviour_refinement_val; done.
    - iDestruct "Hbisim" as "(%Hreducibleₛ & Hbisim)".
      invert Hstepsₛ as [| n' ? (eₛ', σₛ') ? Hstepₛ Hstepsₛ'].
      + eelim irreducible_not_reducible_1; done.
      + apply step_prim_step in Hstepₛ.
        iMod ("Hbisim" with "[//]") as "(Hsi & (_ & Hbisim))".
        rewrite -bisim_fixpoint.
        iDestruct (bisim_mono with "Hsimilar Hbisim") as "Hbisim".
        iApply ("IH" with "[%] [//] Hsi Hbisim"). lia.
    - iDestruct "Hbisim" as "((%eₜ' & %σₜ' & %Hstepₜ) & Hbisim)".
      iMod ("Hbisim" with "[//]") as "(Hsi & (HI & _))".
      iDestruct ("HI" with "Hsimilar [//] Hsi") as %(e_finalₜ & Hbₜ & Hrefinement).
      invert Hbₜ as [? σ_finalₜ (Hstepsₜ' & Hirreducibleₜ) |].
      iPureIntro. exists e_finalₜ. split; last done. econstructor. split; last done.
      eauto using rtc_transitive, rtc_once, prim_step_step.
    - iDestruct "Hbisim" as "((%Hreducibleₛ & (%eₜ' & %σₜ' & %Hstepₜ)) & Hbisim)".
      invert Hstepsₛ as [| n' ? (eₛ', σₛ') ? Hstepₛ Hstepsₛ'].
      + eelim irreducible_not_reducible_1; done.
      + apply step_prim_step in Hstepₛ.
        iMod ("Hbisim" with "[//]") as "(Hsi & Hbisim)".
        iDestruct (bisim_mono with "Hsimilar Hbisim") as "Hbisim".
        iDestruct ("IH" with "[%] [//] Hsi Hbisim") as %(e_finalₜ & Hbₜ & Hrefinement); first lia.
        invert Hbₜ as [? σ_finalₜ (Hstepsₜ' & Hirreducibleₜ) |].
        iPureIntro. exists e_finalₜ. split; last done. econstructor. split; last done.
        eauto using rtc_transitive, rtc_once, prim_step_step.
    - iDestruct "Hbisim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & [] & Hsi & Hbisim)".
  Qed.

  Lemma bisim_adequacy_convergesₜ eₛ σₛ eₜ e_finalₜ σₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp σₛ σₜ ∗
        BISIM eₛ ≃ eₜ {{# (≈) }}
    ) →
    let bₜ := behaviour_converges e_finalₜ in
    has_behaviour sim_progₜ eₜ σₜ bₜ →
      ∃ e_finalₛ,
      let bₛ := behaviour_converges e_finalₛ in
      has_behaviour sim_progₛ eₛ σₛ bₛ ∧
      behaviour_refinement bₛ bₜ.
  Proof.
    intros Hbisim bₜ Hbₜ.
    invert Hbₜ as [? σ_finalₜ ((n & Hstepsₜ)%rtc_nsteps & Hirreducibleₜ) |].
    apply (uPred.pure_soundness (M := M)).
    iMod Hbisim as "(%sim_state & % & #val_bi_similar_similar & Hsi & Hbisim)". clear Hbisim.
    iInduction n as [n] "IH" using nat_strong_ind forall (eₛ σₛ eₜ σₜ Hstepsₜ).
    set I : sim_protocol_O PROP Λₛ Λₜ := λ Φ eₛ _eₜ, (
      ∀ σₛ,
      (∀ eₛ eₜ, Φ eₛ eₜ -∗ sim_post_vals (≈) eₛ eₜ) -∗
      ⌜_eₜ = eₜ⌝ -∗
      sim_state_interp σₛ σₜ -∗
      ⌜ ∃ e_finalₛ,
        let bₛ := behaviour_converges e_finalₛ in
        has_behaviour sim_progₛ eₛ σₛ bₛ ∧
        behaviour_refinement bₛ bₜ
      ⌝
    )%I.
    iAssert (I (sim_post_vals (≈)%I) eₛ eₜ) with "[Hbisim]" as "HI"; last first.
    { iApply ("HI" with "[] [//] Hsi"). iSmash. }
    rewrite /bisimv bisim_fixpoint. iApply (bisim_inner_strong_ind with "[] Hbisim"); [solve_proper.. |].
    clear eₛ σₛ. iIntros "!> %Φ %eₛ % Hbisim % Hsimilar -> Hsi".
    iMod ("Hbisim" with "Hsi") as "[Hbisim | [Hbisim | [Hbisim | [Hbisim | Hbisim]]]]".
    - iDestruct "Hbisim" as "(_ & [Hbisim | Hbisim])".
      + iDestruct "Hbisim" as "(%Hstuckₛ & %Hstuckₜ)".
        iPureIntro. exists eₛ. split.
        * econstructor. split; first apply rtc_refl.
          apply stuck_irreducible. done.
        * invert Hstepsₜ as [| n' ? (eₜ', σₜ') ? Hstepₜ _]; last first.
          { eelim irreducible_not_reducible_1.
            - apply stuck_irreducible, Hstuckₜ.
            - exists eₜ', σₜ'. apply step_prim_step. done.
          }
          apply behaviour_refinement_stuck; [apply Hstuckₛ | apply Hstuckₜ].
      + rewrite sim_post_vals_unseal.
        iDestruct ("Hsimilar" with "Hbisim") as "(%vₛ & %vₜ & (-> & ->) & Hv)".
        iDestruct ("val_bi_similar_similar" with "Hv") as %Hv.
        iPureIntro. exists (of_val vₛ). split.
        * econstructor. split; [apply rtc_refl | by eapply val_irreducible].
        * invert Hstepsₜ as [| n' ? (eₜ', σₜ') ? Hstepₜ _]; last first.
          { eelim irreducible_not_reducible_1; first last.
            - exists eₜ', σₜ'. apply step_prim_step. done.
            - eapply val_irreducible. done.
          }
          eapply behaviour_refinement_val; done.
    - iDestruct "Hbisim" as "((%eₛ' & %σₛ' & %Hstepₛ) & Hbisim)".
      iMod ("Hbisim" with "[//]") as "(Hsi & (HI & _))".
      iDestruct ("HI" with "Hsimilar [//] Hsi") as %(e_finalₛ & Hbₛ & Hrefinement).
      invert Hbₛ as [? σ_finalₛ (Hstepsₛ' & Hirreducibleₛ) |].
      iPureIntro. exists e_finalₛ. split; last done. econstructor. split; last done.
      eauto using rtc_transitive, rtc_once, prim_step_step.
    - iDestruct "Hbisim" as "(%Hreducibleₜ & Hbisim)".
      invert Hstepsₜ as [| n' ? (eₜ', σₜ') ? Hstepₜ Hstepsₜ'].
      + eelim irreducible_not_reducible_1; done.
      + apply step_prim_step in Hstepₜ.
        iMod ("Hbisim" with "[//]") as "(Hsi & (_ & Hbisim))".
        rewrite -bisim_fixpoint.
        iDestruct (bisim_mono with "Hsimilar Hbisim") as "Hbisim".
        iApply ("IH" with "[%] [//] Hsi Hbisim"). lia.
    - iDestruct "Hbisim" as "(((%eₛ' & %σₛ' & %Hstepₛ) & %Hreducibleₜ) & Hbisim)".
      invert Hstepsₜ as [| n' ? (eₜ', σₜ') ? Hstepₜ Hstepsₜ'].
      + eelim irreducible_not_reducible_1; done.
      + apply step_prim_step in Hstepₜ.
        iMod ("Hbisim" with "[//]") as "(Hsi & Hbisim)".
        iDestruct (bisim_mono with "Hsimilar Hbisim") as "Hbisim".
        iDestruct ("IH" with "[%] [//] Hsi Hbisim") as %(e_finalₛ & Hbₛ & Hrefinement); first lia.
        invert Hbₛ as [? σ_finalₛ (Hstepsₛ' & Hirreducibleₛ) |].
        iPureIntro. exists e_finalₛ. split; last done. econstructor. split; last done.
        eauto using rtc_transitive, rtc_once, prim_step_step.
    - iDestruct "Hbisim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & [] & Hsi & Hbisim)".
  Qed.

  Lemma bisim_adequacy_divergesₛ eₛ σₛ eₜ σₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp σₛ σₜ ∗
        BISIM eₛ ≃ eₜ {{# (≈) }}
    ) →
    has_behaviour sim_progₛ eₛ σₛ behaviour_diverges  →
    has_behaviour sim_progₜ eₜ σₜ behaviour_diverges.
  Proof.
    intros Hbisim Hbₛ.
    invert Hbₛ as [| Hdivergesₛ].
    constructor. apply (idiverges_adequacy M).
    iApply bupd_idiverges. iMod Hbisim as "(%sim_state & % & #val_bi_similar_similar & Hsi & Hbisim)". clear Hbisim. iModIntro.
    set I := λ eₜ σₜ, (
      ∃ eₛ σₛ,
      ⌜diverges sim_progₛ eₛ σₛ⌝ ∗
      sim_state_interp σₛ σₜ ∗
      BISIM eₛ ≃ eₜ {{ sim_post_vals (≈) }}
    )%I.
    iAssert (I eₜ σₜ -∗ idiverges sim_progₜ eₜ σₜ)%I as "HI"; last iSmash.
    iApply idiverges_coind. clear dependent eₛ σₛ eₜ σₜ. iIntros "!> %eₜ %σₜ (%eₛ & %σₛ & %Hdivergesₛ & Hsi & Hbisim)".
    set J : sim_protocol_O PROP Λₛ Λₜ := λ Φ eₛ eₜ, (
      ∀ σₛ σₜ,
      ⌜diverges sim_progₛ eₛ σₛ⌝ -∗
      (∀ eₛ eₜ, Φ eₛ eₜ -∗ sim_post_vals (≈) eₛ eₜ) -∗
      sim_state_interp σₛ σₜ ==∗
        ∃ eₜ' σₜ',
        ⌜tc (step sim_progₜ) (eₜ, σₜ) (eₜ', σₜ')⌝ ∗
        I eₜ' σₜ'
    )%I.
    iAssert (BISIM eₛ ≃ eₜ {{ sim_post_vals (≈) }} -∗ J (sim_post_vals (≈)) eₛ eₜ)%I as "HJ"; last first.
    { iApply ("HJ" with "Hbisim [//] [] Hsi"). iSmash. }
    rewrite bisim_fixpoint. iApply (bisim_inner_strong_ind with "[]"); [solve_proper.. |].
    clear dependent eₛ σₛ eₜ σₜ. iIntros "!> %Φ %eₛ %eₜ Hbisim %σₛ %σₜ %Hdivergesₛ Hsimilar Hsi".
    iMod ("Hbisim" with "Hsi") as "[Hbisim | [Hbisim | [Hbisim | [Hbisim | Hbisim]]]]".
    - iDestruct "Hbisim" as "(_ & Hbisim)".
      iAssert ⌜irreducible sim_progₛ eₛ σₛ⌝%I as %[]%irreducible_not_reducible.
      { iDestruct "Hbisim" as "[Hbisim | Hbisim]".
        - iDestruct "Hbisim" as "(%Hstuckₛ & %Hstuckₜ)".
          iPureIntro. apply stuck_irreducible. done.
        - rewrite sim_post_vals_unseal.
          iDestruct ("Hsimilar" with "Hbisim") as "(%vₛ & %vₜ & (-> & ->) & _)".
          iPureIntro. eapply val_irreducible. done.
      }
      apply diverges_reducible. done.
    - iDestruct "Hbisim" as "(%Hreducibleₛ & Hbisim)".
      punfold Hdivergesₛ. invert Hdivergesₛ as [? ? eₛ' σₛ' Hstepₛ [Hdivergesₛ' | []]].
      iMod ("Hbisim" with "[//]") as "(Hsi & (HJ & _))".
      iApply ("HJ" with "[//] Hsimilar Hsi").
    - iDestruct "Hbisim" as "((%eₜ' & %σₜ' & %Hstepₜ) & Hbisim)".
      iMod ("Hbisim" with "[//]") as "(Hsi & (HJ & _))".
      iMod ("HJ" with "[//] Hsimilar Hsi") as "(%eₜ'' & %σₜ'' & %Hstepsₜ & HI)".
      iExists eₜ'', σₜ''. iFrame. eauto using tc_l, prim_step_step.
    - iDestruct "Hbisim" as "((%Hreducibleₛ & (%eₜ' & %σₜ' & %Hstepₜ)) & Hbisim)".
      punfold Hdivergesₛ. invert Hdivergesₛ as [? ? eₛ' σₛ' Hstepₛ [Hdivergesₛ' | []]].
      iMod ("Hbisim" with "[//]") as "(Hsi & Hbisim)".
      iDestruct (bisim_mono with "Hsimilar Hbisim") as "Hbisim".
      iExists eₜ', σₜ'. iSplitR; last iSmash.
      eauto using tc_once, prim_step_step.
    - iDestruct "Hbisim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & [] & Hsi & Hbisim)".
  Qed.

  Lemma bisim_adequacy_divergesₜ eₛ σₛ eₜ σₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp σₛ σₜ ∗
        BISIM eₛ ≃ eₜ {{# (≈) }}
    ) →
    has_behaviour sim_progₜ eₜ σₜ behaviour_diverges  →
    has_behaviour sim_progₛ eₛ σₛ behaviour_diverges.
  Proof.
    intros Hbisim Hbₜ.
    invert Hbₜ as [| Hdivergesₜ].
    constructor. apply (idiverges_adequacy M).
    iApply bupd_idiverges. iMod Hbisim as "(%sim_state & % & #val_bi_similar_similar & Hsi & Hbisim)". clear Hbisim. iModIntro.
    set I := λ eₛ σₛ, (
      ∃ eₜ σₜ,
      ⌜diverges sim_progₜ eₜ σₜ⌝ ∗
      sim_state_interp σₛ σₜ ∗
      BISIM eₛ ≃ eₜ {{ sim_post_vals (≈) }}
    )%I.
    iAssert (I eₛ σₛ -∗ idiverges sim_progₛ eₛ σₛ)%I as "HI"; last iSmash.
    iApply idiverges_coind. clear dependent eₛ σₛ eₜ σₜ. iIntros "!> %eₛ %σₛ (%eₜ & %σₜ & %Hdivergesₜ & Hsi & Hbisim)".
    set J : sim_protocol_O PROP Λₛ Λₜ := λ Φ eₛ eₜ, (
      ∀ σₛ σₜ,
      ⌜diverges sim_progₜ eₜ σₜ⌝ -∗
      (∀ eₛ eₜ, Φ eₛ eₜ -∗ sim_post_vals (≈) eₛ eₜ) -∗
      sim_state_interp σₛ σₜ ==∗
        ∃ eₛ' σₛ',
        ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
        I eₛ' σₛ'
    )%I.
    iAssert (BISIM eₛ ≃ eₜ {{ sim_post_vals (≈) }} -∗ J (sim_post_vals (≈)) eₛ eₜ)%I as "HJ"; last first.
    { iApply ("HJ" with "Hbisim [//] [] Hsi"). iSmash. }
    rewrite bisim_fixpoint. iApply (bisim_inner_strong_ind with "[]"); [solve_proper.. |].
    clear dependent eₛ σₛ eₜ σₜ. iIntros "!> %Φ %eₛ %eₜ Hbisim %σₛ %σₜ %Hdivergesₜ Hsimilar Hsi".
    iMod ("Hbisim" with "Hsi") as "[Hbisim | [Hbisim | [Hbisim | [Hbisim | Hbisim]]]]".
    - iDestruct "Hbisim" as "(_ & Hbisim)".
      iAssert ⌜irreducible sim_progₜ eₜ σₜ⌝%I as %[]%irreducible_not_reducible.
      { iDestruct "Hbisim" as "[Hbisim | Hbisim]".
        - iDestruct "Hbisim" as "(%Hstuckₛ & %Hstuckₜ)".
          iPureIntro. apply stuck_irreducible. done.
        - rewrite sim_post_vals_unseal.
          iDestruct ("Hsimilar" with "Hbisim") as "(%vₛ & %vₜ & (-> & ->) & _)".
          iPureIntro. eapply val_irreducible. done.
      }
      apply diverges_reducible. done.
    - iDestruct "Hbisim" as "((%eₛ' & %σₛ' & %Hstepₛ) & Hbisim)".
      iMod ("Hbisim" with "[//]") as "(Hsi & (HJ & _))".
      iMod ("HJ" with "[//] Hsimilar Hsi") as "(%eₛ'' & %σₛ'' & %Hstepsₛ & HI)".
      iExists eₛ'', σₛ''. iFrame. eauto using tc_l, prim_step_step.
    - iDestruct "Hbisim" as "(%Hreducibleₜ & Hbisim)".
      punfold Hdivergesₜ. invert Hdivergesₜ as [? ? eₜ' σₜ' Hstepₜ [Hdivergesₜ' | []]].
      iMod ("Hbisim" with "[//]") as "(Hsi & (HJ & _))".
      iApply ("HJ" with "[//] Hsimilar Hsi").
    - iDestruct "Hbisim" as "(((%eₛ' & %σₛ' & %Hstepₛ) & %Hreducibleₜ) & Hbisim)".
      punfold Hdivergesₜ. invert Hdivergesₜ as [? ? eₜ' σₜ' Hstepₜ [Hdivergesₜ' | []]].
      iMod ("Hbisim" with "[//]") as "(Hsi & Hbisim)".
      iDestruct (bisim_mono with "Hsimilar Hbisim") as "Hbisim".
      iExists eₛ', σₛ'. iSplitR; last iSmash.
      eauto using tc_once, prim_step_step.
    - iDestruct "Hbisim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & [] & Hsi & Hbisim)".
  Qed.

  Lemma bisim_adequacy σₛ eₛ σₜ eₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp σₛ σₜ ∗
        BISIM eₛ ≃ eₜ {{# (≈) }}
    ) →
      config_refinement sim_progₜ sim_progₛ eₜ σₜ eₛ σₛ ∧
      config_refinement sim_progₛ sim_progₜ eₛ σₛ eₜ σₜ.
  Proof.
    intros Hbisim. split.
    - intros [e_finalₜ |] Hbₜ.
      + edestruct bisim_adequacy_convergesₛ as (e_finalₛ & Hbₛ & Hrefinement); [done.. |].
        exists (behaviour_converges e_finalₛ). split; done.
      + efeed pose proof bisim_adequacy_divergesₛ as Hbₛ; [done.. |].
        exists behaviour_diverges. split; [done | constructor].
    - intros [e_finalₛ |] Hbₛ.
      + edestruct bisim_adequacy_convergesₜ as (e_finalₜ & Hbₜ & Hrefinement); [done.. |].
        exists (behaviour_converges e_finalₜ). split; done.
      + efeed pose proof bisim_adequacy_divergesₜ as Hbₜ; [done.. |].
        exists behaviour_diverges. split; [done | constructor].
  Qed.
  Lemma bisim_adequacy' `{!Empty (state Λₛ)} `{!Empty (state Λₜ)} eₛ eₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp ∅ ∅ ∗
        BISIM eₛ ≃ eₜ {{# (≈) }}
    ) →
      expr_refinement sim_progₜ sim_progₛ eₜ eₛ ∧
      expr_refinement sim_progₛ sim_progₜ eₛ eₜ.
  Proof.
    apply bisim_adequacy.
  Qed.
End bisim.
