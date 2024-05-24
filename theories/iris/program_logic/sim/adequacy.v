From Paco Require Import
  paco.

From iris.base_logic Require Import
  bi.

From camlcert Require Import
  prelude.
From camlcert.common Require Import
  induction.
From camlcert.iris.program_logic Require Import
  refinement
  idiverges
  sim.proofmode
  sim.notations.

Section sim.
  Context `{!Similar (val Λₛ) (val Λₜ)}.
  Context `{sim_programs : !SimPrograms Λₛ Λₜ}.
  Context {M : ucmra}.

  Notation PROP :=
    (uPredI M).

  Lemma sim_adequacy_converges eₛ σₛ eₜ e_finalₜ σₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp σₛ σₜ ∗
        SIM eₛ ≳ eₜ {{# (≈) }}
    ) →
    let bₜ := behaviour_converges e_finalₜ in
    has_behaviour sim_progₜ eₜ σₜ bₜ →
      ∃ e_finalₛ,
      let bₛ := behaviour_converges e_finalₛ in
      has_behaviour sim_progₛ eₛ σₛ bₛ ∧
      behaviour_refinement bₛ bₜ.
  Proof.
    intros Hsim bₜ Hbₜ.
    invert Hbₜ as [? σ_finalₜ ((n & Hstepsₜ)%rtc_nsteps & Hirreducibleₜ) |].
    apply (uPred.pure_soundness (M := M)).
    iMod Hsim as "(%sim_state & % & #val_bi_similar_similar & Hsi & Hsim)". clear Hsim.
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
    iAssert (I (sim_post_vals (≈)%I) eₛ eₜ) with "[Hsim]" as "HI"; last first.
    { iApply ("HI" with "[] [//] Hsi"). iSmash. }
    rewrite /simv sim_fixpoint. iApply (sim_inner_strong_ind with "[] Hsim"); [solve_proper.. |].
    clear eₛ σₛ. iIntros "!> %Φ %eₛ % Hsim % Hsimilar -> Hsi".
    iMod ("Hsim" with "Hsi") as "[Hsim | [Hsim | [Hsim | Hsim]]]".
    - iDestruct "Hsim" as "(_ & [Hsim | Hsim])".
      + iDestruct "Hsim" as "(%Hstuckₛ & %Hstuckₜ)".
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
        iDestruct ("Hsimilar" with "Hsim") as "(%vₛ & %vₜ & (-> & ->) & Hv)".
        iDestruct ("val_bi_similar_similar" with "Hv") as %Hv.
        iPureIntro. exists (of_val vₛ). split.
        * econstructor. split; [apply rtc_refl | by eapply val_irreducible].
        * invert Hstepsₜ as [| n' ? (eₜ', σₜ') ? Hstepₜ _]; last first.
          { eelim irreducible_not_reducible_1; first last.
            - exists eₜ', σₜ'. apply step_prim_step. done.
            - eapply val_irreducible. done.
          }
          eapply behaviour_refinement_val; done.
    - iDestruct "Hsim" as "(%eₛ' & %σₛ' & %Hstepsₛ & Hsi & (HI & _))".
      iDestruct ("HI" with "Hsimilar [//] Hsi") as %(e_finalₛ & Hbₛ & Hrefinement).
      invert Hbₛ as [? σ_finalₛ (Hstepsₛ' & Hirreducibleₛ) |].
      iPureIntro. exists e_finalₛ. split; last done. econstructor. split; last done.
      eauto using rtc_transitive, tc_rtc.
    - iDestruct "Hsim" as "(%Hreducibleₜ & Hsim)".
      invert Hstepsₜ as [| n' ? (eₜ', σₜ') ? Hstepₜ Hstepsₜ'].
      + eelim irreducible_not_reducible_1; done.
      + apply step_prim_step in Hstepₜ.
        iMod ("Hsim" with "[//]") as "[Hsim | Hsim]".
        * iDestruct "Hsim" as "(Hsi & (_ & Hsim))".
          rewrite -sim_fixpoint.
          iDestruct (sim_mono with "Hsimilar Hsim") as "Hsim".
          iApply ("IH" with "[%] [//] Hsi Hsim"). lia.
        * iDestruct "Hsim" as "(%eₛ' & %σₛ' & %Hstepsₛ & Hsi & Hsim)".
          iDestruct (sim_mono with "Hsimilar Hsim") as "Hsim".
          iDestruct ("IH" with "[%] [//] Hsi Hsim") as %(e_finalₛ & Hbₛ & Hrefinement); first lia.
          invert Hbₛ as [? σ_finalₛ (Hstepsₛ' & Hirreducibleₛ) |].
          iPureIntro. exists e_finalₛ. split; last done. econstructor. split; last done.
          eauto using rtc_transitive, tc_rtc.
    - iDestruct "Hsim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & [] & Hsi & Hsim)".
  Qed.

  Lemma sim_adequacy_diverges eₛ σₛ eₜ σₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp σₛ σₜ ∗
        SIM eₛ ≳ eₜ {{# (≈) }}
    ) →
    has_behaviour sim_progₜ eₜ σₜ behaviour_diverges  →
    has_behaviour sim_progₛ eₛ σₛ behaviour_diverges.
  Proof.
    intros Hsim Hbₜ.
    invert Hbₜ as [| Hdivergesₜ].
    constructor. apply (idiverges_adequacy M).
    iApply bupd_idiverges. iMod Hsim as "(%sim_state & % & #val_bi_similar_similar & Hsi & Hsim)". clear Hsim. iModIntro.
    set I := λ eₛ σₛ, (
      ∃ eₜ σₜ,
      ⌜diverges sim_progₜ eₜ σₜ⌝ ∗
      sim_state_interp σₛ σₜ ∗
      SIM eₛ ≳ eₜ {{ sim_post_vals (≈) }}
    )%I.
    iAssert (I eₛ σₛ -∗ idiverges sim_progₛ eₛ σₛ)%I as "HI"; last iSmash.
    iApply idiverges_coind. clear dependent eₛ σₛ eₜ σₜ. iIntros "!> %eₛ %σₛ (%eₜ & %σₜ & %Hdivergesₜ & Hsi & Hsim)".
    set J : sim_protocol_O PROP Λₛ Λₜ := λ Φ eₛ eₜ, (
      ∀ σₛ σₜ,
      ⌜diverges sim_progₜ eₜ σₜ⌝ -∗
      (∀ eₛ eₜ, Φ eₛ eₜ -∗ sim_post_vals (≈) eₛ eₜ) -∗
      sim_state_interp σₛ σₜ ==∗
        ∃ eₛ' σₛ',
        ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
        I eₛ' σₛ'
    )%I.
    iAssert (SIM eₛ ≳ eₜ {{ sim_post_vals (≈) }} -∗ J (sim_post_vals (≈)) eₛ eₜ)%I as "HJ"; last first.
    { iApply ("HJ" with "Hsim [//] [] Hsi"). iSmash. }
    rewrite sim_fixpoint. iApply (sim_inner_strong_ind with "[]"); [solve_proper.. |].
    clear dependent eₛ σₛ eₜ σₜ. iIntros "!> %Φ %eₛ %eₜ Hsim %σₛ %σₜ %Hdivergesₜ Hsimilar Hsi".
    iMod ("Hsim" with "Hsi") as "[Hsim | [Hsim | [Hsim | Hsim]]]".
    - iDestruct "Hsim" as "(_ & Hsim)".
      iAssert ⌜irreducible sim_progₜ eₜ σₜ⌝%I as %[]%irreducible_not_reducible.
      { iDestruct "Hsim" as "[Hsim | Hsim]".
        - iDestruct "Hsim" as "(%Hstuckₛ & %Hstuckₜ)".
          iPureIntro. apply stuck_irreducible. done.
        - rewrite sim_post_vals_unseal.
          iDestruct ("Hsimilar" with "Hsim") as "(%vₛ & %vₜ & (-> & ->) & _)".
          iPureIntro. eapply val_irreducible. done.
      }
      apply diverges_reducible. done.
    - iDestruct "Hsim" as "(%eₛ' & %σₛ' & %Hstepsₜ & Hsi & (_ & Hsim))".
      rewrite -sim_fixpoint.
      iDestruct (sim_mono with "Hsimilar Hsim") as "Hsim". iSmash.
    - iDestruct "Hsim" as "(%Hreducibleₜ & Hsim)".
      punfold Hdivergesₜ. invert Hdivergesₜ as [? ? eₜ' σₜ' Hstepₜ [Hdivergesₜ' | []]].
      iMod ("Hsim" with "[//]") as "[Hsim | Hsim]".
      + iDestruct "Hsim" as "(Hsi & (HJ & _))".
        iApply ("HJ" with "[//] Hsimilar Hsi").
      + iDestruct "Hsim" as "(%eₛ' & %σₛ' & %Hstepsₛ & Hsi & Hsim)".
        iDestruct (sim_mono with "Hsimilar Hsim") as "Hsim". iSmash.
    - iDestruct "Hsim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & [] & Hsi & Hsim)".
  Qed.

  Lemma sim_adequacy σₛ eₛ σₜ eₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp σₛ σₜ ∗
        SIM eₛ ≳ eₜ {{# (≈) }}
    ) →
    config_refinement sim_progₛ sim_progₜ eₛ σₛ eₜ σₜ.
  Proof.
    intros Hsim [e_finalₜ |] Hbₜ.
    - edestruct sim_adequacy_converges as (e_finalₛ & Hbₛ & Hrefinement); [done.. |].
      exists (behaviour_converges e_finalₛ). split; done.
    - efeed pose proof sim_adequacy_diverges as Hbₛ; [done.. |].
      exists behaviour_diverges. split; [done | constructor].
  Qed.
  Lemma sim_adequacy' `{!Empty (state Λₛ)} `{!Empty (state Λₜ)} eₛ eₜ :
    ( ⊢ |==>
        ∃ sim_state : SimState PROP Λₛ Λₜ,
        ∃ (_ : BiSimilar PROP (val Λₛ) (val Λₜ)),
        □ (∀ vₛ vₜ, vₛ ≈ vₜ -∗ ⌜vₛ ≈ vₜ⌝) ∗
        sim_state_interp ∅ ∅ ∗
        SIM eₛ ≳ eₜ {{# (≈) }}
    ) →
    expr_refinement sim_progₛ sim_progₜ eₛ eₜ.
  Proof.
    apply sim_adequacy.
  Qed.
End sim.
