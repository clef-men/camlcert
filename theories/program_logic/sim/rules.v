From iris.bi Require Import
  fixpoint.

From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.base_logic Require Import
  lib.cupd.proofmode.
From simuliris.program_logic Require Export
  sim.definition.
From simuliris.program_logic Require Import
  sim.notations.

#[local] Notation "Φ1 --∗ Φ2" := (∀ x1 x2, Φ1 x1 x2 -∗ Φ2 x1 x2)%I
( at level 99,
  Φ2 at level 200,
  right associativity,
  format "'[' Φ1  --∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 --∗ Φ2" := (⊢ Φ1 --∗ Φ2)
( only parsing
) : stdpp_scope.
#[local] Notation "Φ1 ===∗ Φ2" := (∀ x1 x2, Φ1 x1 x2 -∗ |==> Φ2 x1 x2)%I
( at level 99,
  Φ2 at level 200,
  format "'[' Φ1  ===∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 ===∗ Φ2" := (⊢ Φ1 ===∗ Φ2)
( only parsing
) : stdpp_scope.
#[local] Notation "Φ1 +++∗ Φ2" := (∀ x1 x2, Φ1 x1 x2 -∗ |++> Φ2 x1 x2)%I
( at level 99,
  Φ2 at level 200,
  format "'[' Φ1  +++∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 +++∗ Φ2" := (⊢ Φ1 +++∗ Φ2)
( only parsing
) : stdpp_scope.

#[local] Notation "Φ1 ---∗ Φ2" := (∀ x1 x2 x3, Φ1 x1 x2 x3 -∗ Φ2 x1 x2 x3)%I
( at level 99,
  Φ2 at level 200,
  right associativity,
  format "'[' Φ1  ---∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 ---∗ Φ2" := (⊢ Φ1 ---∗ Φ2)
( only parsing
) : stdpp_scope.
#[local] Notation "Φ1 ====∗ Φ2" := (∀ x1 x2 x3, Φ1 x1 x2 x3 -∗ |==> Φ2 x1 x2 x3)%I
( at level 99,
  Φ2 at level 200,
  format "'[' Φ1  ====∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 ====∗ Φ2" := (⊢ Φ1 ====∗ Φ2)
( only parsing
) : stdpp_scope.
#[local] Notation "Φ1 ++++∗ Φ2" := (∀ x1 x2 x3, Φ1 x1 x2 x3 -∗ |++> Φ2 x1 x2 x3)%I
( at level 99,
  Φ2 at level 200,
  format "'[' Φ1  ++++∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 ++++∗ Φ2" := (⊢ Φ1 ++++∗ Φ2)
( only parsing
) : stdpp_scope.

Section sim_post_vals.
  Context {Λₛ Λₜ : ectx_language}.
  Context `{!BiBUpd PROP, !BiAffine PROP}.
  Implicit Types Φ : val Λₛ → val Λₜ → PROP.

  Lemma sim_post_vals_cupd_mono `{sim_state : !SimState PROP Λₛ Λₜ} Φ1 Φ2 eₛ eₜ :
    (Φ1 +++∗ Φ2) ⊢
    sim_post_vals Φ1 eₛ eₜ ++∗
    sim_post_vals Φ2 eₛ eₜ.
  Proof.
    rewrite sim_post_vals_unseal. iSmash.
  Qed.
  Lemma sim_post_vals_bupd_mono Φ1 Φ2 eₛ eₜ :
    (Φ1 ===∗ Φ2) ⊢
    sim_post_vals Φ1 eₛ eₜ ==∗
    sim_post_vals Φ2 eₛ eₜ.
  Proof.
    rewrite sim_post_vals_unseal. iSmash.
  Qed.
  Lemma sim_post_vals_mono Φ1 Φ2 eₛ eₜ :
    (Φ1 --∗ Φ2) ⊢
    sim_post_vals Φ1 eₛ eₜ -∗
    sim_post_vals Φ2 eₛ eₜ.
  Proof.
    rewrite sim_post_vals_unseal. iSmash.
  Qed.

  Lemma sim_post_vals_cupd `{sim_state : !SimState PROP Λₛ Λₜ} Φ eₛ eₜ :
    sim_post_vals (λ vₛ vₜ, |++> Φ vₛ vₜ) eₛ eₜ ⊢
    |++> sim_post_vals Φ eₛ eₜ.
  Proof.
    iApply sim_post_vals_cupd_mono. iSmash.
  Qed.
  Lemma sim_post_vals_bupd Φ eₛ eₜ :
    sim_post_vals (λ vₛ vₜ, |==> Φ vₛ vₜ) eₛ eₜ ⊢
    |==> sim_post_vals Φ eₛ eₜ.
  Proof.
    iApply sim_post_vals_bupd_mono. iSmash.
  Qed.
End sim_post_vals.

Section sim_state.
  Context `{sim_programs : !SimPrograms Λₛ Λₜ}.
  Context `{!BiBUpd PROP, !BiAffine PROP}.
  Context `{sim_state : !SimState PROP Λₛ Λₜ}.

  Notation sim_protocol := (sim_protocol PROP Λₛ Λₜ).
  Notation sim_protocol_O := (sim_protocol_O PROP Λₛ Λₜ).
  Implicit Types Χ : sim_protocol.
  Implicit Types N M I : sim_protocol_O.

  Section protocol.
    Context Χ.

    Notation sim_body := (sim_body Χ).
    Notation sim_body' := (definition.sim_body' Χ).
    Notation sim_inner := (sim_inner Χ).
    Notation sim_inner' := (definition.sim_inner' Χ).
    Notation sim := (sim Χ).
    Notation simv := (simv Χ).

    Section sim_body.
      #[global] Instance sim_body_ne n :
        Proper (
          ((≡{n}≡) ==> (≡{n}≡)) ==>
          ((≡{n}≡) ==> (≡{n}≡)) ==>
          (≡{n}≡) ==>
          (≡{n}≡) ==>
          (≡{n}≡) ==>
          (≡{n}≡)
        ) sim_body.
      Proof.
        intros N1 N2 HN M1 M2 HM Φ1 Φ2 HΦ eₛ1 eₛ2 ->%leibniz_equiv eₜ1 eₜ2 ->%leibniz_equiv.
        solve_proper_core ltac:(fun _ => f_equiv || apply HN || apply HM || apply HΦ).
      Qed.
      #[global] Instance sim_body_proper :
        Proper (
          ((≡) ==> (≡)) ==>
          ((≡) ==> (≡)) ==>
          (≡) ==>
          (≡) ==>
          (≡) ==>
          (≡)
        ) sim_body.
      Proof.
        intros N1 N2 HN M1 M2 HM Φ1 Φ2 HΦ eₛ1 eₛ2 ->%leibniz_equiv eₜ1 eₜ2 ->%leibniz_equiv.
        rewrite /sim_body. repeat (f_equiv || apply HN || apply HM || apply HΦ).
      Qed.

      Lemma sim_body_strongly_stuck N M Φ eₛ eₜ :
        strongly_stuck sim_progₛ eₛ →
        strongly_stuck sim_progₜ eₜ →
        ⊢ sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "%Hstrongly_stuckₛ %Hstrong_stuckₜ %σₛ %σₜ Hsi !>".
        iLeft. iFrame. auto using strongly_stuck_stuck.
      Qed.
      Lemma sim_body_strongly_head_stuck N M Φ eₛ eₜ :
        strongly_head_stuck sim_progₛ eₛ →
        strongly_head_stuck sim_progₜ eₜ →
        ⊢ sim_body N M Φ eₛ eₜ.
      Proof.
        intros.
        apply sim_body_strongly_stuck; apply strongly_head_stuck_strongly_stuck; done.
      Qed.

      Lemma sim_body_post N M Φ eₛ eₜ :
        Φ eₛ eₜ ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iSmash.
      Qed.

      Lemma cupd_sim_body N M Φ eₛ eₜ :
        (|++> sim_body N M Φ eₛ eₜ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "Hsim %σₛ %σₜ Hsi".
        rewrite sim_cupd_eq. iMod ("Hsim" with "Hsi") as "(Hsi & Hsim)".
        iApply ("Hsim" with "Hsi").
      Qed.
      Lemma bupd_sim_body N M Φ eₛ eₜ :
        (|==> sim_body N M Φ eₛ eₜ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "Hsim".
        iApply cupd_sim_body.
        iMod "Hsim" as "$". iSmash.
      Qed.

      Lemma sim_body_monotone R N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
        (R Φ1 Φ2 -∗ N1 Φ1 +++∗ N2 Φ2) -∗
        (R Φ1 Φ2 -∗ M1 Φ1 +++∗ M2 Φ2) -∗
        (R Φ1 Φ2 -∗ Φ1 +++∗ Φ2) -∗
        R Φ1 Φ2 -∗
        sim_body N1 M1 Φ1 eₛ eₜ -∗
        sim_body N2 M2 Φ2 eₛ eₜ.
      Proof.
        setoid_rewrite sim_cupd_eq.
        iIntros "HN HM HΦ HR Hsim %σₛ %σₜ Hsi".
        iMod ("Hsim" with "Hsi") as "[Hsim | [Hsim | [Hsim | Hsim]]]".
        - iDestruct "Hsim" as "(Hsi & [(%Hstuckₛ & %Hstuckₜ) | HΦ1])"; iLeft.
          + iSmash.
          + iMod ("HΦ" with "HR HΦ1 Hsi") as "(Hsi & HΦ2)". iSmash.
        - iDestruct "Hsim" as "(%eₛ' & %σₛ' & %Hstepsₛ & Hsi & HM1)".
          iRight. iLeft. iExists eₛ', σₛ'. iSplitR; first iSmash.
          iApply ("HM" with "HR HM1 Hsi").
        - iDestruct "Hsim" as "(%Hreducible & Hsim)".
          do 2 iRight. iLeft. iSplitR; first iSmash. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
          iDestruct ("Hsim" with "[//]") as "> [Hsim | Hsim]".
          + iDestruct "Hsim" as "(Hsi & HM1)".
            iLeft.
            iApply ("HM" with "HR HM1 Hsi").
          + iDestruct "Hsim" as "(%eₛ' & %σₛ' & %Hstepsₛ & Hsi & HN1)".
            iRight. iExists eₛ', σₛ'. iSplitR; first iSmash.
            iApply ("HN" with "HR HN1 Hsi").
        - iDestruct "Hsim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & HΧ & Hsi & HM1)".
          do 3 iRight. iExists Kₛ, eₛ', Kₜ, eₜ', Ψ. iFrame. iSplitR; first iSmash. clear eₛ' σₛ eₜ' σₜ. iIntros "!> %eₛ %eₜ HΨ".
          iMod ("HM1" with "HΨ") as "HM1".
          iApply ("HM" with "HR HM1").
      Qed.

      Lemma sim_body_cupd_mono N1 N2 M1 M2 Φ eₛ eₜ :
        (N1 ++++∗ N2) -∗
        (M1 ++++∗ M2) -∗
        sim_body N1 M1 Φ eₛ eₜ -∗
        sim_body N2 M2 Φ eₛ eₜ.
      Proof.
        iIntros "HN HM".
        iApply (sim_body_monotone (λ _ _, True)%I with "[HN] [HM] [] [//]"); iIntros "_"; auto.
      Qed.
      Lemma sim_body_bupd_mono N1 N2 M1 M2 Φ eₛ eₜ :
        (N1 ====∗ N2) -∗
        (M1 ====∗ M2) -∗
        sim_body N1 M1 Φ eₛ eₜ -∗
        sim_body N2 M2 Φ eₛ eₜ.
      Proof.
        iIntros "HN HM".
        iApply (sim_body_cupd_mono with "[HN] [HM]"); iSmash.
      Qed.
      Lemma sim_body_mono N1 N2 M1 M2 Φ eₛ eₜ :
        (N1 ---∗ N2) -∗
        (M1 ---∗ M2) -∗
        sim_body N1 M1 Φ eₛ eₜ -∗
        sim_body N2 M2 Φ eₛ eₜ.
      Proof.
        iIntros "HN HM".
        iApply (sim_body_bupd_mono with "[HN] [HM]"); iSmash.
      Qed.

      Lemma sim_body_strong_cupd_mono N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
        ((Φ1 +++∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
        ((Φ1 +++∗ Φ2) -∗ M1 Φ1 +++∗ M2 Φ2) -∗
        (Φ1 +++∗ Φ2) -∗
        sim_body N1 M1 Φ1 eₛ eₜ -∗
        sim_body N2 M2 Φ2 eₛ eₜ.
      Proof.
        iIntros "HN HM HΦ".
        iApply (sim_body_monotone (λ Φ1 Φ2, Φ1 +++∗ Φ2)%I with "[HN] [HM] [] HΦ"); iSmash+.
      Qed.
      Lemma sim_body_strong_bupd_mono N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
        ((Φ1 ===∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
        ((Φ1 ===∗ Φ2) -∗ M1 Φ1 +++∗ M2 Φ2) -∗
        (Φ1 ===∗ Φ2) -∗
        sim_body N1 M1 Φ1 eₛ eₜ -∗
        sim_body N2 M2 Φ2 eₛ eₜ.
      Proof.
        iIntros "HN HM HΦ".
        iApply (sim_body_monotone (λ Φ1 Φ2, Φ1 ===∗ Φ2)%I with "[HN] [HM] [] HΦ"); iSmash+.
      Qed.
      Lemma sim_body_strong_mono N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
        ((Φ1 --∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
        ((Φ1 --∗ Φ2) -∗ M1 Φ1 +++∗ M2 Φ2) -∗
        (Φ1 --∗ Φ2) -∗
        sim_body N1 M1 Φ1 eₛ eₜ -∗
        sim_body N2 M2 Φ2 eₛ eₜ.
      Proof.
        iIntros "HN HM HΦ".
        iApply (sim_body_monotone (λ Φ1 Φ2, Φ1 --∗ Φ2)%I with "[HN] [HM] [] HΦ"); iSmash+.
      Qed.

      Lemma sim_body_cupd N M Φ eₛ eₜ :
        (N (λ eₛ eₜ, |++> Φ eₛ eₜ) +++∗ N Φ) -∗
        (M (λ eₛ eₜ, |++> Φ eₛ eₜ) +++∗ M Φ) -∗
        sim_body N M (λ eₛ eₜ, |++> Φ eₛ eₜ) eₛ eₜ -∗
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "HN HM".
        iApply (sim_body_strong_cupd_mono with "[HN] [HM]"); iSmash.
      Qed.
      Lemma sim_body_bupd N M Φ eₛ eₜ :
        (N (λ eₛ eₜ, |==> Φ eₛ eₜ) +++∗ N Φ) -∗
        (M (λ eₛ eₜ, |==> Φ eₛ eₜ) +++∗ M Φ) -∗
        sim_body N M (λ eₛ eₜ, |==> Φ eₛ eₜ) eₛ eₜ -∗
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "HN HM".
        iApply (sim_body_strong_bupd_mono with "[HN] [HM]"); iSmash.
      Qed.

      Lemma sim_body_frame_l N M R Φ eₛ eₜ :
        ( ∀ eₛ eₜ,
          R ∗ N Φ eₛ eₜ ++∗
          N (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ
        ) -∗
        ( ∀ eₛ eₜ,
          R ∗ M Φ eₛ eₜ ++∗
          M (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ
        ) -∗
        R ∗ sim_body N M Φ eₛ eₜ -∗
        sim_body N M (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ.
      Proof.
        iIntros "HN HM (HR & Hsim)".
        iApply (sim_body_monotone (λ _ _, R) with "[HN] [HM] [] HR Hsim"); iSmash.
      Qed.
      Lemma sim_body_frame_r N M R Φ eₛ eₜ :
        ( ∀ eₛ eₜ,
          N Φ eₛ eₜ ∗ R ++∗
          N (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ
        ) -∗
        ( ∀ eₛ eₜ,
          M Φ eₛ eₜ ∗ R ++∗
          M (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ
        ) -∗
        sim_body N M Φ eₛ eₜ ∗ R -∗
        sim_body N M (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ.
      Proof.
        iIntros "HN HM (Hsim & HR)".
        iApply (sim_body_monotone (λ _ _, R) with "[HN] [HM] [] HR Hsim"); iSmash.
      Qed.

      (* TODO: sim_body_bind *)
      (* TODO: sim_body_bindₛ *)
      (* TODO: sim_body_bindₜ *)

      (* TODO: sim_body_bind_inv *)
      (* TODO: sim_body_bind_invₛ *)
      (* TODO: sim_body_bind_invₜ *)

      (* TODO: sim_body_decompose *)

      Lemma sim_body_stepsₛ N M Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ∃ eₛ' σₛ',
            ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
            sim_state_interp σₛ' σₜ ∗
            M Φ eₛ' eₜ
        ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iSmash.
      Qed.
      Lemma sim_body_stepₛ N M Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ∃ eₛ' σₛ',
            ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
            sim_state_interp σₛ' σₜ ∗
            M Φ eₛ' eₜ
        ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "HM".
        iApply sim_body_stepsₛ. iIntros "%σₛ %σₜ Hsi".
        iMod ("HM" with "Hsi") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi)".
        iExists eₛ', σₛ'. iFrame. iPureIntro. eapply tc_once, prim_step_step; done.
      Qed.
      Lemma sim_body_head_stepₛ N M Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ∃ eₛ' σₛ',
            ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
            sim_state_interp σₛ' σₜ ∗
            M Φ eₛ' eₜ
        ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "HM".
        iApply sim_body_stepₛ. iIntros "%σₛ %σₜ Hsi".
        iMod ("HM" with "Hsi") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi)".
        iExists eₛ', σₛ'. iFrame. iPureIntro. apply head_step_prim_step. done.
      Qed.
      Lemma sim_body_pure_stepsₛ N M Φ eₛ1 eₛ2 eₜ :
        tc (pure_step sim_progₛ) eₛ1 eₛ2 →
        M Φ eₛ2 eₜ ⊢
        sim_body N M Φ eₛ1 eₜ.
      Proof.
        iIntros "%Hstepsₛ HM".
        iApply sim_body_stepsₛ. iIntros "%σₛ %σₜ Hsi".
        iExists eₛ2, σₛ. iSplitR; last iSmash. iPureIntro.
        eapply (tc_congruence (λ eₛ, (eₛ, σₛ))); last done.
        eauto using prim_step_step, pure_step_prim_step.
      Qed.
      Lemma sim_body_pure_stepₛ N M Φ eₛ1 eₛ2 eₜ :
        pure_step sim_progₛ eₛ1 eₛ2 →
        M Φ eₛ2 eₜ ⊢
        sim_body N M Φ eₛ1 eₜ.
      Proof.
        intros Hstepₛ.
        iApply sim_body_pure_stepsₛ.
        eauto using tc_once.
      Qed.
      Lemma sim_body_pure_head_stepsₛ N M Φ eₛ1 eₛ2 eₜ :
        tc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
        M Φ eₛ2 eₜ ⊢
        sim_body N M Φ eₛ1 eₜ.
      Proof.
        intros Hstepsₛ.
        iApply sim_body_pure_stepsₛ.
        eauto using (tc_congruence id), pure_head_step_pure_step.
      Qed.
      Lemma sim_body_pure_head_stepₛ N M Φ eₛ1 eₛ2 eₜ :
        pure_head_step sim_progₛ eₛ1 eₛ2 →
        M Φ eₛ2 eₜ ⊢
        sim_body N M Φ eₛ1 eₜ.
      Proof.
        intros Hstepₛ.
        iApply sim_body_pure_head_stepsₛ.
        eauto using tc_once.
      Qed.

      Lemma sim_body_stepₜ N M Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                sim_state_interp σₛ σₜ' ∗
                M Φ eₛ eₜ'
        ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iSmash.
      Qed.
      Lemma sim_body_head_stepₜ N M Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                sim_state_interp σₛ σₜ' ∗
                M Φ eₛ eₜ'
        ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "HM".
        iApply sim_body_stepₜ. iIntros "%σₛ %σₜ Hsi".
        iMod ("HM" with "Hsi") as "(%Hreducibleₜ & HM)".
        iSplitR; first auto using head_reducible_reducible. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
        apply head_reducible_prim_step in Hstepₜ; last done.
        iApply "HM". iSmash.
      Qed.
      Lemma sim_body_pure_stepₜ N M Φ eₛ eₜ1 eₜ2 :
        pure_step sim_progₜ eₜ1 eₜ2 →
        M Φ eₛ eₜ2 ⊢
        sim_body N M Φ eₛ eₜ1.
      Proof.
        iIntros "%Hstepₜ HM".
        iApply sim_body_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
        iSplit; eauto using pure_step_safe. iIntros "%eₜ' %σₜ' %Hstepₜ' !>".
        eapply pure_step_det in Hstepₜ; last done. destruct Hstepₜ as (-> & ->).
        iSmash.
      Qed.
      Lemma sim_body_pure_head_stepₜ N M Φ eₛ eₜ1 eₜ2 :
        pure_head_step sim_progₜ eₜ1 eₜ2 →
        M Φ eₛ eₜ2 ⊢
        sim_body N M Φ eₛ eₜ1.
      Proof.
        intros Hstepₜ.
        iApply sim_body_pure_stepₜ.
        eauto using pure_head_step_pure_step.
      Qed.

      Lemma sim_body_steps N M Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                ∃ eₛ' σₛ',
                ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
                sim_state_interp σₛ' σₜ' ∗
                N Φ eₛ' eₜ'
        ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "HN %σₛ %σₜ Hsi".
        do 2 iRight. iLeft.
        iMod ("HN" with "Hsi") as "($ & HN)".
        iIntros "!> %eₜ' %σₜ' %Hstepₜ".
        iRight. iApply ("HN" with "[//]").
      Qed.
      Lemma sim_body_step N M Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                ∃ eₛ' σₛ',
                ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
                sim_state_interp σₛ' σₜ' ∗
                N Φ eₛ' eₜ'
        ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "HN".
        iApply sim_body_steps. iIntros "%σₛ %σₜ Hsi".
        iMod ("HN" with "Hsi") as "(%Hreducibleₜ & HN)".
        iSplitR; first iSmash. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
        iMod ("HN" with "[//]") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi & HN)".
        iExists eₛ', σₛ'. iFrame. eauto using tc_once, prim_step_step.
      Qed.
      Lemma sim_body_head_step N M Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                ∃ eₛ' σₛ',
                ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
                sim_state_interp σₛ' σₜ' ∗
                N Φ eₛ' eₜ'
        ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros "HN".
        iApply sim_body_step. iIntros "%σₛ %σₜ Hsi".
        iMod ("HN" with "Hsi") as "(%Hreducibleₜ & HN)".
        iSplitR; first auto using head_reducible_reducible. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
        apply head_reducible_prim_step in Hstepₜ; last done.
        iMod ("HN" with "[//]") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi & HN)".
        iExists eₛ', σₛ'. iFrame. iPureIntro. apply head_step_prim_step. done.
      Qed.
      Lemma sim_body_pure_steps N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        tc (pure_step sim_progₛ) eₛ1 eₛ2 →
        pure_step sim_progₜ eₜ1 eₜ2 →
        N Φ eₛ2 eₜ2 ⊢
        sim_body N M Φ eₛ1 eₜ1.
      Proof.
        iIntros "%Hstepsₛ %Hstepₜ HN".
        iApply sim_body_steps. iIntros "%σₛ %σₜ Hsi !>".
        iSplit; first eauto using pure_step_safe. iIntros "%_eₜ2 %_σₜ %_Hstepₜ !>".
        eapply pure_step_det in _Hstepₜ as (-> & ->); last done.
        iExists eₛ2, σₛ. iFrame. iPureIntro.
        eapply (tc_congruence (λ eₛ, (eₛ, σₛ))); last done.
        eauto using prim_step_step, pure_step_prim_step.
      Qed.
      Lemma sim_body_pure_step N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        pure_step sim_progₛ eₛ1 eₛ2 →
        pure_step sim_progₜ eₜ1 eₜ2 →
        N Φ eₛ2 eₜ2 ⊢
        sim_body N M Φ eₛ1 eₜ1.
      Proof.
        iIntros "%Hstepₛ %Hstepₜ HN".
        iApply (sim_body_pure_steps with "HN"); first apply tc_once; done.
      Qed.
      Lemma sim_body_pure_head_steps N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        tc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
        pure_head_step sim_progₜ eₜ1 eₜ2 →
        N Φ eₛ2 eₜ2 ⊢
        sim_body N M Φ eₛ1 eₜ1.
      Proof.
        iIntros "%Hstepₛ %Hstepₜ HN".
        iApply (sim_body_pure_steps with "HN");
          eauto using (tc_congruence id), pure_head_step_pure_step.
      Qed.
      Lemma sim_body_pure_head_step N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        pure_head_step sim_progₛ eₛ1 eₛ2 →
        pure_head_step sim_progₜ eₜ1 eₜ2 →
        N Φ eₛ2 eₜ2 ⊢
        sim_body N M Φ eₛ1 eₜ1.
      Proof.
        iIntros "%Hstepₛ %Hstepₜ HN".
        iApply (sim_body_pure_head_steps with "HN"); first apply tc_once; done.
      Qed.

      Lemma sim_body_apply_protocol Ψ Kₛ eₛ' Kₜ eₜ' N M Φ eₛ eₜ :
        eₛ = Kₛ @@ eₛ' →
        eₜ = Kₜ @@ eₜ' →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            Χ Ψ eₛ' eₜ' ∗
            sim_state_interp σₛ σₜ ∗
              ∀ eₛ eₜ,
              Ψ eₛ eₜ ++∗
              M Φ (Kₛ @@ eₛ) (Kₜ @@ eₜ)

        ) ⊢
        sim_body N M Φ eₛ eₜ.
      Proof.
        iIntros (-> ->) "H %σₛ %σₜ Hsi".
        do 3 iRight. iExists Kₛ, eₛ', Kₜ, eₜ', Ψ. iSplitR; first iSmash.
        iApply ("H" with "Hsi").
      Qed.
    End sim_body.

    Section sim_inner.
      #[local] Instance sim_body'_ne n :
        Proper (
          ((≡{n}≡) ==> (≡{n}≡)) ==>
          ((≡{n}≡) ==> (≡{n}≡)) ==>
          (≡{n}≡) ==>
          (≡{n}≡)
        ) sim_body'.
      Proof.
        intros N1 N2 HN M1 M2 HM ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
        simpl in HΦ, Heₛ, Heₜ. subst.
        apply sim_body_ne; done || solve_proper.
      Qed.
      #[local] Instance sim_body'_proper :
        Proper (
          ((≡) ==> (≡)) ==>
          ((≡) ==> (≡)) ==>
          (≡) ==>
          (≡)
        ) sim_body'.
      Proof.
        intros N1 N2 HN M1 M2 HM ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
        simpl in HΦ, Heₛ, Heₜ. subst.
        apply sim_body_proper; done || solve_proper.
      Qed.

      #[local] Instance sim_body'_mono_pred N :
        NonExpansive N →
        BiMonoPred (sim_body' N).
      Proof.
        intros HN. split; last solve_proper.
        iIntros "%M1 %M2 %HM1 %HM2 #HM" (((Φ & eₛ) & eₜ)) "Hsim /=".
        iApply (sim_body_mono with "[] [] Hsim"); iSmash.
      Qed.

      #[global] Instance sim_inner_ne n :
        Proper (
          ((≡{n}≡) ==> (≡{n}≡)) ==>
          (≡{n}≡) ==>
          (≡{n}≡) ==>
          (≡{n}≡) ==>
          (≡{n}≡)
        ) sim_inner.
      Proof.
        rewrite definition.sim_inner_unseal /definition.sim_inner_def /curry3.
        solve_proper.
      Qed.
      #[global] Instance sim_inner_proper :
        Proper (
          ((≡) ==> (≡)) ==>
          (≡) ==>
          (≡) ==>
          (≡) ==>
          (≡)
        ) sim_inner.
      Proof.
        rewrite definition.sim_inner_unseal /definition.sim_inner_def /curry3.
        solve_proper.
      Qed.

      Lemma sim_inner_fixpoint N Φ eₛ eₜ :
        NonExpansive N →
        sim_inner N Φ eₛ eₜ ⊣⊢
        sim_body N (sim_inner N) Φ eₛ eₜ.
      Proof.
        rewrite definition.sim_inner_unseal.
        intros. setoid_rewrite least_fixpoint_unfold; [done | apply _].
      Qed.
      Lemma sim_inner_unfold N Φ eₛ eₜ :
        NonExpansive N →
        sim_inner N Φ eₛ eₜ ⊢
        sim_body N (sim_inner N) Φ eₛ eₜ.
      Proof.
        intros. rewrite sim_inner_fixpoint //.
      Qed.
      Lemma sim_inner_fold N Φ eₛ eₜ :
        NonExpansive N →
        sim_body N (sim_inner N) Φ eₛ eₜ ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros. rewrite sim_inner_fixpoint //.
      Qed.

      Lemma sim_inner_strong_ind I N Φ eₛ eₜ :
        NonExpansive N →
        NonExpansive I →
        □ (sim_body N (λ Φ eₛ eₜ, I Φ eₛ eₜ ∧ sim_inner N Φ eₛ eₜ) ---∗ I) ⊢
        sim_inner N Φ eₛ eₜ -∗
        I Φ eₛ eₜ.
      Proof.
        rewrite definition.sim_inner_unseal.
        iIntros "%HN %HI #Hind Hsim".
        replace (I Φ eₛ eₜ) with ((uncurry3 I) (Φ, eₛ, eₜ)); last done.
        iApply (least_fixpoint_ind with "[] Hsim"). clear Φ eₛ eₜ. iIntros "!>" (((Φ & eₛ) & eₜ)) "Hsim /=".
        iApply ("Hind" with "Hsim").
      Qed.
      Lemma sim_inner_ind I N Φ eₛ eₜ :
        NonExpansive N →
        NonExpansive I →
        □ (sim_body N I ---∗ I) ⊢
        sim_inner N Φ eₛ eₜ -∗
        I Φ eₛ eₜ.
      Proof.
        iIntros "%HN %HI #Hind".
        iApply sim_inner_strong_ind. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ Hsim".
        iApply "Hind".
        iApply (sim_body_mono with "[] [] Hsim"); first iSmash. clear Φ eₛ eₜ. iIntros "%Φ %eₛ %eₜ (HI & _) //".
      Qed.

      Lemma sim_inner_strongly_stuck N Φ eₛ eₜ :
        NonExpansive N →
        strongly_stuck sim_progₛ eₛ →
        strongly_stuck sim_progₜ eₜ →
        ⊢ sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN. rewrite sim_inner_fixpoint. apply sim_body_strongly_stuck.
      Qed.
      Lemma sim_inner_strongly_head_stuck N Φ eₛ eₜ :
        NonExpansive N →
        strongly_head_stuck sim_progₛ eₛ →
        strongly_head_stuck sim_progₜ eₜ →
        ⊢ sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN. rewrite sim_inner_fixpoint. apply sim_body_strongly_head_stuck.
      Qed.

      Lemma sim_inner_post N Φ eₛ eₜ :
        NonExpansive N →
        Φ eₛ eₜ ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN. rewrite sim_inner_fixpoint //. apply sim_body_post.
      Qed.

      Lemma cupd_sim_inner N Φ eₛ eₜ :
        NonExpansive N →
        (|++> sim_inner N Φ eₛ eₜ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN. rewrite sim_inner_fixpoint. apply cupd_sim_body.
      Qed.
      Lemma bupd_sim_inner N Φ eₛ eₜ :
        NonExpansive N →
        (|==> sim_inner N Φ eₛ eₜ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN. rewrite sim_inner_fixpoint. apply bupd_sim_body.
      Qed.

      Lemma sim_inner_monotone R N1 N2 Φ1 Φ2 eₛ eₜ :
        NonExpansive N1 →
        NonExpansive N2 →
        NonExpansive2 R →
        □ (R Φ1 Φ2 -∗ N1 Φ1 +++∗ N2 Φ2) -∗
        □ (R Φ1 Φ2 -∗ Φ1 +++∗ Φ2) -∗
        R Φ1 Φ2 -∗
        sim_inner N1 Φ1 eₛ eₜ -∗
        sim_inner N2 Φ2 eₛ eₜ.
      Proof.
        intros HN1 HN2 HR.
        set I := λ Φ1 eₛ eₜ, (
          □ (R Φ1 Φ2 -∗ N1 Φ1 +++∗ N2 Φ2) -∗
          □ (R Φ1 Φ2 -∗ Φ1 +++∗ Φ2) -∗
          R Φ1 Φ2 -∗
          sim_inner N2 Φ2 eₛ eₜ
        )%I.
        cut (sim_inner N1 Φ1 eₛ eₜ -∗ I Φ1 eₛ eₜ).
        { iIntros "%HI #HN #HΦ HR Hsim".
          iApply (HI with "Hsim HN HΦ HR").
        }
        iApply (sim_inner_ind with "[]"); first solve_proper. clear Φ1 eₛ eₜ. iIntros "!> %Φ1 %eₛ %eₜ Hsim #HN #HΦ HR".
        iApply sim_inner_fixpoint.
        iApply (sim_body_monotone with "HN [] HΦ HR Hsim"). clear eₛ eₜ. iIntros "HR %eₛ %eₜ HI".
        iApply ("HI" with "HN HΦ HR").
      Qed.

      Lemma sim_inner_cupd_mono N1 N2 Φ eₛ eₜ :
        NonExpansive N2 →
        □ (N1 ++++∗ N2) ⊢
        sim_inner N1 Φ eₛ eₜ -∗
        sim_inner N2 Φ eₛ eₜ.
      Proof.
        rewrite definition.sim_inner_unseal.
        iIntros "%HN2 #HN Hsim". rewrite /sim_inner /curry3.
        iApply (least_fixpoint_iter with "[] Hsim"). clear Φ eₛ eₜ. iIntros "!>" (((Φ & eₛ) & eₜ)) "Hsim".
        rewrite least_fixpoint_unfold /sim_body' {1 3}/uncurry3.
        iApply (sim_body_cupd_mono with "[] [] Hsim"); first iSmash. iStep. auto.
      Qed.
      Lemma sim_inner_bupd_mono N1 N2 Φ eₛ eₜ :
        NonExpansive N2 →
        □ (N1 ====∗ N2) ⊢
        sim_inner N1 Φ eₛ eₜ -∗
        sim_inner N2 Φ eₛ eₜ.
      Proof.
        iIntros "%HN2 #HN".
        iApply sim_inner_cupd_mono. iModIntro. iSmash.
      Qed.
      Lemma sim_inner_mono N1 N2 Φ eₛ eₜ :
        NonExpansive N2 →
        □ (N1 ---∗ N2) ⊢
        sim_inner N1 Φ eₛ eₜ -∗
        sim_inner N2 Φ eₛ eₜ.
      Proof.
        iIntros "%HN2 #HN".
        iApply sim_inner_bupd_mono. iModIntro. iSmash.
      Qed.

      Lemma sim_inner_strong_cupd_mono N1 N2 Φ1 Φ2 eₛ eₜ :
        NonExpansive N1 →
        NonExpansive N2 →
        □ ((Φ1 +++∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) ⊢
        (Φ1 +++∗ Φ2) -∗
        sim_inner N1 Φ1 eₛ eₜ -∗
        sim_inner N2 Φ2 eₛ eₜ.
      Proof.
        iIntros "%HN1 %HN2 #HN HΦ".
        iApply (sim_inner_monotone (λ Φ1 Φ2, Φ1 +++∗ Φ2)%I with "HN [] HΦ"); first solve_proper. iModIntro. iSmash.
      Qed.
      Lemma sim_inner_strong_bupd_mono N1 N2 Φ1 Φ2 eₛ eₜ :
        NonExpansive N1 →
        NonExpansive N2 →
        □ ((Φ1 ===∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) ⊢
        (Φ1 ===∗ Φ2) -∗
        sim_inner N1 Φ1 eₛ eₜ -∗
        sim_inner N2 Φ2 eₛ eₜ.
      Proof.
        iIntros "%HN1 %HN2 #HN HΦ".
        iApply (sim_inner_monotone (λ Φ1 Φ2, Φ1 ===∗ Φ2)%I with "HN [] HΦ"); first solve_proper. iModIntro. iSmash.
      Qed.
      Lemma sim_inner_strong_mono N1 N2 Φ1 Φ2 eₛ eₜ :
        NonExpansive N1 →
        NonExpansive N2 →
        □ ((Φ1 --∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) ⊢
        (Φ1 --∗ Φ2) -∗
        sim_inner N1 Φ1 eₛ eₜ -∗
        sim_inner N2 Φ2 eₛ eₜ.
      Proof.
        iIntros "%HN1 %HN2 #HN HΦ".
        iApply (sim_inner_monotone (λ Φ1 Φ2, Φ1 --∗ Φ2)%I with "HN [] HΦ"); first solve_proper. iModIntro. iSmash.
      Qed.

      Lemma sim_inner_cupd N Φ eₛ eₜ :
        NonExpansive N →
        □ (N (λ eₛ eₜ, |++> Φ eₛ eₜ) +++∗ N Φ) ⊢
        sim_inner N (λ eₛ eₜ, |++> Φ eₛ eₜ) eₛ eₜ -∗
        sim_inner N Φ eₛ eₜ.
      Proof.
        iIntros "%HN #HN".
        iApply (sim_inner_strong_cupd_mono with "[HN]"); first iModIntro; iSmash.
      Qed.
      Lemma sim_inner_bupd N Φ eₛ eₜ :
        NonExpansive N →
        □ (N (λ eₛ eₜ, |==> Φ eₛ eₜ) +++∗ N Φ) ⊢
        sim_inner N (λ eₛ eₜ, |==> Φ eₛ eₜ) eₛ eₜ -∗
        sim_inner N Φ eₛ eₜ.
      Proof.
        iIntros "%HN #HN".
        iApply (sim_inner_strong_bupd_mono with "[HN]"); first iModIntro; iSmash.
      Qed.

      Lemma sim_inner_frame_l N R Φ eₛ eₜ :
        NonExpansive N →
        □ (
          ∀ eₛ eₜ,
          R ∗ N Φ eₛ eₜ ++∗
          N (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ
        ) -∗
        R ∗ sim_inner N Φ eₛ eₜ -∗
        sim_inner N (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ.
      Proof.
        iIntros "%HN #HN (HR & Hsim)".
        iApply (sim_inner_monotone (λ _ _, R) with "[HN] [] HR Hsim"); first (by solve_proper_prepare); iModIntro; iSmash.
      Qed.
      Lemma sim_inner_frame_r N R Φ eₛ eₜ :
        NonExpansive N →
        □ (
          ∀ eₛ eₜ,
          N Φ eₛ eₜ ∗ R ++∗
          N (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ
        ) -∗
        sim_inner N Φ eₛ eₜ ∗ R -∗
        sim_inner N (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ.
      Proof.
        iIntros "%HN #HN (Hsim & HR)".
        iApply (sim_inner_monotone (λ _ _, R) with "[HN] [] HR Hsim"); first (by solve_proper_prepare); iModIntro; iSmash.
      Qed.

      Lemma sim_inner_bind' N1 N2 Φ1 Φ2 Kₛ eₛ Kₜ eₜ :
        NonExpansive N1 →
        NonExpansive N2 →
        sim_inner N1 Φ1 eₛ eₜ -∗
        ( ∀ eₛ' eₜ',
          N1 Φ1 eₛ' eₜ' -∗
          N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
        ) -∗
        ( ∀ eₛ' eₜ',
          Φ1 eₛ' eₜ' -∗
          sim_inner N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
        ) -∗
        sim_inner N2 Φ2 (Kₛ @@ eₛ) (Kₜ @@ eₜ).
      Proof.
        intros HN1 HN2.
        set I : sim_protocol_O := λ Φ1 eₛ eₜ, (
          ( ∀ eₛ' eₜ',
            N1 Φ1 eₛ' eₜ' -∗
            N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
          ) -∗
          ( ∀ eₛ' eₜ',
            Φ1 eₛ' eₜ' -∗
            sim_inner N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
          ) -∗
          sim_inner N2 Φ2 (Kₛ @@ eₛ) (Kₜ @@ eₜ)
        )%I.
        assert (NonExpansive I) as HI.
        { solve_proper_prepare. solve_proper_core ltac:(fun _ => apply HN1 || f_equiv). }
        iApply (sim_inner_ind I with "[]"). clear Φ1 eₛ eₜ. iIntros "!> %Φ1 %eₛ %eₜ Hsim1 HN Hsim2".
        rewrite sim_inner_fixpoint. iIntros "%σₛ %σₜ Hsi".
        iMod ("Hsim1" with "Hsi") as "[Hsim1 | [Hsim1 | [Hsim1 | Hsim1]]]".
        - iDestruct "Hsim1" as "(Hsi & [(%Hstuckₛ & %Hstuckₜ) | HΦ1])".
          + iLeft. iFrame. iLeft.
            iPureIntro. split; (apply language_ctx_stuck; [apply _ | done]).
          + iRevert (σₛ σₜ) "Hsi". iApply sim_inner_fixpoint. iApply ("Hsim2" with "HΦ1").
        - iDestruct "Hsim1" as "(%eₛ' & %σₛ' & %Hstepsₛ & Hsi & HI)".
          iRight. iLeft. iExists (Kₛ @@ eₛ'), σₛ'. iFrame. iSplitR.
          { iPureIntro. apply language_ctx_tc_step; [apply _ | done]. }
          iApply ("HI" with "HN Hsim2").
        - iDestruct "Hsim1" as "(%Hreducibleₜ & Hsim1)".
          do 2 iRight. iLeft. iSplitR.
          { iPureIntro. apply language_ctx_reducible; [apply _ | done]. }
          iIntros "!> %eₜ'' %σₜ' %Hstepₜ".
          apply reducible_fill_prim_step in Hstepₜ as (eₜ' & -> & Hstepₜ); last done.
          iMod ("Hsim1" with "[//]") as "[(Hsi & HI) | (%eₛ' & %σₛ' & %Hstepsₛ & Hsi & HN1)]".
          + iLeft. iFrame.
            iApply ("HI" with "HN Hsim2").
          + iRight. iExists (Kₛ @@ eₛ'), σₛ'. iFrame. iSplitR.
            { iPureIntro. apply language_ctx_tc_step; [apply _ | done]. }
            iSmash.
        - iDestruct "Hsim1" as "(%Kₛ' & %eₛ' & %Kₜ' & %eₜ' & %Ψ & (-> & ->) & HΧ & Hsi & HN1)".
          do 3 iRight. iExists (Kₛ ⋅ Kₛ'), eₛ', (Kₜ ⋅ Kₜ'), eₜ', Ψ. iFrame. iSplitR; first rewrite !fill_op //. iIntros "!> %eₛ'' %eₜ'' HΨ".
          rewrite -!fill_op. iApply ("HN1" with "HΨ HN Hsim2").
      Qed.
      Lemma sim_inner_bind N1 N2 Φ Kₛ eₛ Kₜ eₜ :
        NonExpansive N1 →
        NonExpansive N2 →
        sim_inner N1 (λ eₛ' eₜ', sim_inner N2 Φ (Kₛ @@ eₛ') (Kₜ @@ eₜ')) eₛ eₜ -∗
        ( ∀ eₛ' eₜ',
          N1 (λ eₛ' eₜ', sim_inner N2 Φ (Kₛ @@ eₛ') (Kₜ @@ eₜ')) eₛ' eₜ' -∗
          N2 Φ (Kₛ @@ eₛ') (Kₜ @@ eₜ')
        ) -∗
        sim_inner N2 Φ (Kₛ @@ eₛ) (Kₜ @@ eₜ).
      Proof.
        iIntros "%HN1 %HN2 Hsim HN".
        iApply (sim_inner_bind' with "Hsim HN"). iSmash.
      Qed.
      Lemma sim_inner_bindₛ' N1 N2 Φ1 Φ2 K eₛ eₜ :
        NonExpansive N1 →
        NonExpansive N2 →
        sim_inner N1 Φ1 eₛ eₜ -∗
        ( ∀ eₛ' eₜ',
          N1 Φ1 eₛ' eₜ' -∗
          N2 Φ2 (K @@ eₛ') eₜ'
        ) -∗
        ( ∀ eₛ' eₜ',
          Φ1 eₛ' eₜ' -∗
          sim_inner N2 Φ2 (K @@ eₛ') eₜ'
        ) -∗
        sim_inner N2 Φ2 (K @@ eₛ) eₜ.
      Proof.
        iIntros "%HN1 %HN2 Hsim1 HN Hsim2".
        iEval (rewrite -(fill_empty eₜ)).
        iApply (sim_inner_bind' with "Hsim1 [HN] [Hsim2]"); iIntros "%eₛ' %eₜ'";
          rewrite fill_empty; iSmash.
      Qed.
      Lemma sim_inner_bindₛ N1 N2 Φ K eₛ eₜ :
        NonExpansive N1 →
        NonExpansive N2 →
        sim_inner N1 (λ eₛ' eₜ', sim_inner N2 Φ (K @@ eₛ') eₜ') eₛ eₜ -∗
        ( ∀ eₛ' eₜ',
          N1 (λ eₛ' eₜ', sim_inner N2 Φ (K @@ eₛ') eₜ') eₛ' eₜ' -∗
          N2 Φ (K @@ eₛ') eₜ'
        ) -∗
        sim_inner N2 Φ (K @@ eₛ) eₜ.
      Proof.
        iIntros "%HN1 %HN2 Hsim HN".
        iApply (sim_inner_bindₛ' with "Hsim HN"). iSmash.
      Qed.
      Lemma sim_inner_bindₜ' N1 N2 eₛ K eₜ Φ1 Φ2 :
        NonExpansive N1 →
        NonExpansive N2 →
        sim_inner N1 Φ1 eₛ eₜ -∗
        ( ∀ eₛ' eₜ',
          N1 Φ1 eₛ' eₜ' -∗
          N2 Φ2 eₛ' (K @@ eₜ')
        ) -∗
        ( ∀ eₛ' eₜ',
          Φ1 eₛ' eₜ' -∗
          sim_inner N2 Φ2 eₛ' (K @@ eₜ')
        ) -∗
        sim_inner N2 Φ2 eₛ (K @@ eₜ).
      Proof.
        iIntros "%HN1 %HN2 Hsim1 HN Hsim2".
        iEval (rewrite -(fill_empty eₛ)).
        iApply (sim_inner_bind' with "Hsim1 [HN] [Hsim2]"); iIntros "%eₛ' %eₜ'";
          rewrite fill_empty; iSmash.
      Qed.
      Lemma sim_inner_bindₜ N1 N2 Φ eₛ K eₜ :
        NonExpansive N1 →
        NonExpansive N2 →
        sim_inner N1 (λ eₛ' eₜ', sim_inner N2 Φ eₛ' (K @@ eₜ')) eₛ eₜ -∗
        ( ∀ eₛ' eₜ',
          N1 (λ eₛ' eₜ', sim_inner N2 Φ eₛ' (K @@ eₜ')) eₛ' eₜ' -∗
          N2 Φ eₛ' (K @@ eₜ')
        ) -∗
        sim_inner N2 Φ eₛ (K @@ eₜ).
      Proof.
        iIntros "%HN1 %HN2 Hsim HN".
        iApply (sim_inner_bindₜ' with "Hsim HN"). iSmash.
      Qed.

      (* TODO: sim_inner_bind_inv *)
      (* TODO: sim_inner_bind_invₛ *)
      (* TODO: sim_inner_bind_invₜ *)

      (* TODO: sim_inner_decompose *)

      Lemma sim_inner_stepsₛ N Φ eₛ eₜ :
        NonExpansive N →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ∃ eₛ' σₛ',
            ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
            sim_state_interp σₛ' σₜ ∗
            sim_inner N Φ eₛ' eₜ
        ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_stepsₛ.
      Qed.
      Lemma sim_inner_stepₛ N Φ eₛ eₜ :
        NonExpansive N →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ∃ eₛ' σₛ',
            ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
            sim_state_interp σₛ' σₜ ∗
            sim_inner N Φ eₛ' eₜ
        ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_stepₛ.
      Qed.
      Lemma sim_inner_head_stepₛ N Φ eₛ eₜ :
        NonExpansive N →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ∃ eₛ' σₛ',
            ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
            sim_state_interp σₛ' σₜ ∗
            sim_inner N Φ eₛ' eₜ
        ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_head_stepₛ.
      Qed.
      Lemma sim_inner_pure_stepsₛ N Φ eₛ1 eₛ2 eₜ :
        NonExpansive N →
        rtc (pure_step sim_progₛ) eₛ1 eₛ2 →
        sim_inner N Φ eₛ2 eₜ ⊢
        sim_inner N Φ eₛ1 eₜ.
      Proof.
        intros HN [-> | Hstepsₛ]%rtc_tc; first done.
        setoid_rewrite sim_inner_fixpoint at 2; first apply sim_body_pure_stepsₛ; done.
      Qed.
      Lemma sim_inner_pure_stepₛ N Φ eₛ1 eₛ2 eₜ :
        NonExpansive N →
        pure_step sim_progₛ eₛ1 eₛ2 →
        sim_inner N Φ eₛ2 eₜ ⊢
        sim_inner N Φ eₛ1 eₜ.
      Proof.
        intros HN.
        setoid_rewrite sim_inner_fixpoint at 2; [apply sim_body_pure_stepₛ | done].
      Qed.
      Lemma sim_inner_pure_head_stepsₛ N Φ eₛ1 eₛ2 eₜ :
        NonExpansive N →
        rtc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
        sim_inner N Φ eₛ2 eₜ ⊢
        sim_inner N Φ eₛ1 eₜ.
      Proof.
        intros HN [-> | Hstepsₛ]%rtc_tc; first done.
        setoid_rewrite sim_inner_fixpoint at 2; first apply sim_body_pure_head_stepsₛ; done.
      Qed.
      Lemma sim_inner_pure_head_stepₛ N Φ eₛ1 eₛ2 eₜ :
        NonExpansive N →
        pure_head_step sim_progₛ eₛ1 eₛ2 →
        sim_inner N Φ eₛ2 eₜ ⊢
        sim_inner N Φ eₛ1 eₜ.
      Proof.
        intros HN.
        setoid_rewrite sim_inner_fixpoint at 2; [apply sim_body_pure_head_stepₛ | done].
      Qed.

      Lemma sim_inner_stepₜ N Φ eₛ eₜ :
        NonExpansive N →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                sim_state_interp σₛ σₜ' ∗
                sim_inner N Φ eₛ eₜ'
        ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_stepₜ.
      Qed.
      Lemma sim_inner_head_stepₜ N Φ eₛ eₜ :
        NonExpansive N →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                sim_state_interp σₛ σₜ' ∗
                sim_inner N Φ eₛ eₜ'
        ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_head_stepₜ.
      Qed.
      Lemma sim_inner_pure_stepₜ N Φ eₛ eₜ1 eₜ2 :
        NonExpansive N →
        pure_step sim_progₜ eₜ1 eₜ2 →
        sim_inner N Φ eₛ eₜ2 ⊢
        sim_inner N Φ eₛ eₜ1.
      Proof.
        intros HN.
        setoid_rewrite sim_inner_fixpoint at 2; [apply sim_body_pure_stepₜ | done].
      Qed.
      Lemma sim_inner_pure_stepsₜ N Φ eₛ eₜ1 eₜ2 :
        NonExpansive N →
        rtc (pure_step sim_progₜ) eₜ1 eₜ2 →
        sim_inner N Φ eₛ eₜ2 ⊢
        sim_inner N Φ eₛ eₜ1.
      Proof.
        intros HN.
        induction 1 as [| eₜ eₜ' eₜ'' Hstepₜ Hstepsₜ IH]; first done.
        rewrite IH. apply sim_inner_pure_stepₜ; done.
      Qed.
      Lemma sim_inner_pure_head_stepₜ N Φ eₛ eₜ1 eₜ2 :
        NonExpansive N →
        pure_head_step sim_progₜ eₜ1 eₜ2 →
        sim_inner N Φ eₛ eₜ2 ⊢
        sim_inner N Φ eₛ eₜ1.
      Proof.
        intros HN.
        setoid_rewrite sim_inner_fixpoint at 2; [apply sim_body_pure_head_stepₜ | done].
      Qed.
      Lemma sim_inner_pure_head_stepsₜ N Φ eₛ eₜ1 eₜ2 :
        NonExpansive N →
        rtc (pure_head_step sim_progₜ) eₜ1 eₜ2 →
        sim_inner N Φ eₛ eₜ2 ⊢
        sim_inner N Φ eₛ eₜ1.
      Proof.
        intros HN.
        induction 1 as [| eₜ eₜ' eₜ'' Hstepₜ Hstepsₜ IH]; first done.
        rewrite IH. apply sim_inner_pure_head_stepₜ; done.
      Qed.

      Lemma sim_inner_steps N Φ eₛ eₜ :
        NonExpansive N →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                ∃ eₛ' σₛ',
                ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
                sim_state_interp σₛ' σₜ' ∗
                N Φ eₛ' eₜ'
        ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_steps.
      Qed.
      Lemma sim_inner_step N Φ eₛ eₜ :
        NonExpansive N →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                ∃ eₛ' σₛ',
                ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
                sim_state_interp σₛ' σₜ' ∗
                N Φ eₛ' eₜ'
        ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_step.
      Qed.
      Lemma sim_inner_head_step N Φ eₛ eₜ :
        NonExpansive N →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                ∃ eₛ' σₛ',
                ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
                sim_state_interp σₛ' σₜ' ∗
                N Φ eₛ' eₜ'
        ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_head_step.
      Qed.
      Lemma sim_inner_pure_steps N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        NonExpansive N →
        tc (pure_step sim_progₛ) eₛ1 eₛ2 →
        pure_step sim_progₜ eₜ1 eₜ2 →
        N Φ eₛ2 eₜ2 ⊢
        sim_inner N Φ eₛ1 eₜ1.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_pure_steps.
      Qed.
      Lemma sim_inner_pure_step N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        NonExpansive N →
        pure_step sim_progₛ eₛ1 eₛ2 →
        pure_step sim_progₜ eₜ1 eₜ2 →
        N Φ eₛ2 eₜ2 ⊢
        sim_inner N Φ eₛ1 eₜ1.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_pure_step.
      Qed.
      Lemma sim_inner_pure_head_steps N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        NonExpansive N →
        tc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
        pure_head_step sim_progₜ eₜ1 eₜ2 →
        N Φ eₛ2 eₜ2 ⊢
        sim_inner N Φ eₛ1 eₜ1.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_pure_head_steps.
      Qed.
      Lemma sim_inner_pure_head_step N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        NonExpansive N →
        pure_head_step sim_progₛ eₛ1 eₛ2 →
        pure_head_step sim_progₜ eₜ1 eₜ2 →
        N Φ eₛ2 eₜ2 ⊢
        sim_inner N Φ eₛ1 eₜ1.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_pure_head_step.
      Qed.

      Lemma sim_inner_apply_protocol Ψ Kₛ eₛ' Kₜ eₜ' N Φ eₛ eₜ :
        NonExpansive N →
        eₛ = Kₛ @@ eₛ' →
        eₜ = Kₜ @@ eₜ' →
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            Χ Ψ eₛ' eₜ' ∗
            sim_state_interp σₛ σₜ ∗
              ∀ eₛ eₜ,
              Ψ eₛ eₜ ++∗
              sim_inner N Φ (Kₛ @@ eₛ) (Kₜ @@ eₜ)

        ) ⊢
        sim_inner N Φ eₛ eₜ.
      Proof.
        intros HN.
        rewrite sim_inner_fixpoint. apply sim_body_apply_protocol.
      Qed.
    End sim_inner.

    Section sim.
      #[local] Instance sim_inner'_ne n :
        Proper (
          ((≡{n}≡) ==> (≡{n}≡)) ==>
          (≡{n}≡) ==>
          (≡{n}≡)
        ) sim_inner'.
      Proof.
        intros N1 N2 HN ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
        simpl in HΦ, Heₛ, Heₜ. subst.
        apply sim_inner_ne; done || solve_proper.
      Qed.
      #[local] Instance sim_inner'_proper :
        Proper (
          ((≡) ==> (≡)) ==>
          (≡) ==>
          (≡)
        ) sim_inner'.
      Proof.
        intros N1 N2 HN ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
        simpl in HΦ, Heₛ, Heₜ. subst.
        apply sim_inner_proper; done || solve_proper.
      Qed.
      #[local] Instance sim_inner'_mono_pred :
        BiMonoPred sim_inner'.
      Proof.
        split.
        - iIntros "%N1 %N2 %HN1 %HN2 #HN" (((Φ & eₛ) & eₜ)) "Hsim".
          iApply (sim_inner_mono with "[] Hsim"); first solve_proper. iModIntro. iSmash.
        - intros N HN n ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
          rewrite /sim_inner' /=.
          apply sim_inner_ne; solve_proper.
      Qed.

      #[global] Instance sim_ne n :
        Proper ((≡{n}≡) ==> (=) ==> (=) ==> (≡{n}≡)) sim.
      Proof.
        rewrite definition.sim_unseal.
        solve_proper.
      Qed.
      #[global] Instance sim_proper :
        Proper ((≡) ==> (=) ==> (=) ==> (≡)) sim.
      Proof.
        rewrite definition.sim_unseal.
        solve_proper.
      Qed.

      Lemma sim_fixpoint Φ eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ⊣⊢
        sim_inner sim Φ eₛ eₜ.
      Proof.
        rewrite definition.sim_unseal.
        setoid_rewrite greatest_fixpoint_unfold; [done | apply _].
      Qed.
      Lemma sim_unfold Φ eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}  ⊢
        sim_inner sim Φ eₛ eₜ.
      Proof.
        rewrite sim_fixpoint //.
      Qed.
      Lemma sim_fold Φ eₛ eₜ :
        sim_inner sim Φ eₛ eₜ ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint //.
      Qed.

      Lemma sim_eq Φ eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ⊣⊢
        sim_body sim sim Φ eₛ eₜ.
      Proof.
        rewrite sim_fixpoint.
        setoid_rewrite sim_inner_fixpoint; last solve_proper.
        rewrite /sim_body. setoid_rewrite <- sim_fixpoint. done.
      Qed.

      Lemma sim_strong_coind I Φ eₛ eₜ :
        NonExpansive I →
        □ (I ---∗ sim_inner (λ Φ eₛ eₜ, I Φ eₛ eₜ ∨ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }})) ⊢
        I Φ eₛ eₜ -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite definition.sim_unseal.
        iIntros "%HI #Hind HI".
        replace (I Φ eₛ eₜ) with ((uncurry3 I) (Φ, eₛ, eₜ)); last done.
        iApply (greatest_fixpoint_coind with "[] HI"). clear Φ eₛ eₜ. iIntros "!>" (((Φ & eₛ) & eₜ)) "HI /=".
        iSmash.
      Qed.
      Lemma sim_coind I Φ eₛ eₜ :
        NonExpansive I →
        □ (I ---∗ sim_inner I) ⊢
        I Φ eₛ eₜ -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        iIntros "%HI #Hind".
        iApply sim_strong_coind. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ HI".
        iApply (sim_inner_mono with "[] (Hind HI)"); first solve_proper. iModIntro. iSmash.
      Qed.

      Lemma sim_strongly_stuck Φ eₛ eₜ :
        strongly_stuck sim_progₛ eₛ →
        strongly_stuck sim_progₜ eₜ →
        ⊢ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint. apply sim_inner_strongly_stuck. solve_proper.
      Qed.
      Lemma sim_strongly_head_stuck Φ eₛ eₜ :
        strongly_head_stuck sim_progₛ eₛ →
        strongly_head_stuck sim_progₜ eₜ →
        ⊢ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint. apply sim_inner_strongly_head_stuck. solve_proper.
      Qed.

      Lemma sim_post Φ eₛ eₜ :
        Φ eₛ eₜ ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint. apply sim_inner_post. solve_proper.
      Qed.

      Lemma cupd_sim Φ eₛ eₜ :
        (|++> SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint. apply cupd_sim_inner. solve_proper.
      Qed.
      Lemma bupd_sim Φ eₛ eₜ :
        (|==> SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint. apply bupd_sim_inner. solve_proper.
      Qed.

      Lemma sim_cupd_mono Φ1 Φ2 eₛ eₜ :
        (Φ1 +++∗ Φ2) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}.
      Proof.
        set I : sim_protocol_O := λ Φ2 eₛ eₜ, (
          ∃ Φ1,
          (Φ1 +++∗ Φ2) ∗
          SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }}
        )%I.
        assert (NonExpansive I) by solve_proper.
        cut (I Φ2 eₛ eₜ -∗ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}).
        { iIntros "%HI HΦ Hsim".
          iApply HI. iExists Φ1. iFrame.
        }
        iApply (sim_coind with "[]"). clear Φ1 Φ2 eₛ eₜ. iIntros "!> %Φ2 %eₛ %eₜ (%Φ1 & HΦ & Hsim)".
        rewrite sim_fixpoint.
        iApply (sim_inner_strong_cupd_mono with "[] HΦ Hsim"); first solve_proper. clear eₛ eₜ. iIntros "!> HΦ %eₛ %eₜ Hsim".
        iExists Φ1. iFrame. iSmash.
      Qed.
      Lemma sim_bupd_mono Φ1 Φ2 eₛ eₜ :
        (Φ1 ===∗ Φ2) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}.
      Proof.
        rewrite -sim_cupd_mono. iSmash.
      Qed.
      Lemma sim_mono Φ1 Φ2 eₛ eₜ :
        (Φ1 --∗ Φ2) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}.
      Proof.
        rewrite -sim_bupd_mono. iSmash.
      Qed.
      Lemma sim_mono' Φ1 Φ2 eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} ⊢
        (Φ1 --∗ Φ2) -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}.
      Proof.
        rewrite sim_mono. iSmash.
      Qed.

      Lemma sim_cupd Φ eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }} ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        iApply (sim_cupd_mono with "[]"). iSmash.
      Qed.
      Lemma sim_bupd Φ eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }} ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        iApply (sim_bupd_mono with "[]"). iSmash.
      Qed.

      Lemma sim_frame_l R Φ eₛ eₜ :
        R ∗ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, R ∗ Φ eₛ eₜ }}.
      Proof.
        iIntros "(HR & Hsim)".
        iApply (sim_mono with "[HR] Hsim"). iSmash.
      Qed.
      Lemma sim_frame_r R Φ eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ∗ R ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, Φ eₛ eₜ ∗ R }}.
      Proof.
        iIntros "(Hsim & HR)".
        iApply (sim_mono with "[HR] Hsim"). iSmash.
      Qed.

      Lemma sim_bind Φ Kₛ eₛ Kₜ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          SIM Kₛ @@ eₛ' ≳ Kₜ @@ eₜ' [[ Χ ]] {{ Φ }}
        }} ⊢
        SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        set I : sim_protocol_O := λ Φ eₛ'' eₜ'', (
          ∃ Kₛ eₛ Kₜ eₜ,
          ⌜eₛ'' = Kₛ @@ eₛ ∧ eₜ'' = Kₜ @@ eₜ⌝ ∗
          SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
            SIM Kₛ @@ eₛ' ≳ Kₜ @@ eₜ' [[ Χ ]] {{ Φ }}
          }}
        )%I.
        assert (NonExpansive I) as HI by solve_proper+.
        enough (∀ eₛ eₜ, I Φ eₛ eₜ -∗ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}) as H.
        { iIntros "Hsim". iApply H. iSmash. }
        clear eₛ eₜ. iIntros "%eₛ %eₜ".
        iApply (sim_coind with "[]"). clear Φ Kₛ eₛ Kₜ eₜ. iIntros "!> %Φ %eₛ'' %eₜ'' (%Kₛ & %eₛ & %Kₜ & %eₜ & (-> & ->) & Hsim)".
        rewrite sim_fixpoint. iApply (sim_inner_bind' with "Hsim"); first solve_proper.
        - iSmash.
        - iIntros "%eₛ' %eₜ' Hsim".
          rewrite sim_fixpoint. iApply (sim_inner_mono with "[] Hsim"). clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ Hsim".
          iExists ∅, eₛ, ∅, eₜ. iSplit; first rewrite !fill_empty //.
          iApply sim_post. rewrite !fill_empty //.
      Qed.
      Lemma sim_bind' Φ1 Φ2 Kₛ eₛ Kₜ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} -∗
        ( ∀ eₛ' eₜ',
          Φ1 eₛ' eₜ' -∗
          SIM Kₛ @@ eₛ' ≳ Kₜ @@ eₜ' [[ Χ ]] {{ Φ2 }}
        ) -∗
        SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ Χ ]] {{ Φ2 }}.
      Proof.
        iIntros "Hsim HΦ1".
        iApply sim_bind. iApply (sim_mono with "HΦ1 Hsim").
      Qed.
      Lemma sim_bindₛ Φ K eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          SIM K @@ eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}
        }} ⊢
        SIM K @@ eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite -{2}(fill_empty eₜ) -(sim_bind ∅).
        iApply (sim_mono with "[]").
        setoid_rewrite fill_empty. iSmash.
      Qed.
      Lemma sim_bindₜ Φ eₛ K eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          SIM eₛ' ≳ K @@ eₜ' [[ Χ ]] {{ Φ }}
        }} ⊢
        SIM eₛ ≳ K @@ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite -{2}(fill_empty eₛ) -(sim_bind ∅).
        iApply (sim_mono with "[]").
        setoid_rewrite fill_empty. iSmash.
      Qed.

      Lemma sim_bind_inv Φ Kₛ eₛ Kₜ eₜ :
        SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          SIM Kₛ @@ eₛ' ≳ Kₜ @@ eₜ' [[ Χ ]] {{ Φ }}
        }}.
      Proof.
        iIntros "Hsim". iApply sim_post. iSmash.
      Qed.
      Lemma sim_bind_invₛ Φ K eₛ eₜ :
        SIM K @@ eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          SIM K @@ eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}
        }}.
      Proof.
        iIntros "Hsim". iApply sim_post. iSmash.
      Qed.
      Lemma sim_bind_invₜ Φ eₛ K eₜ :
        SIM eₛ ≳ K @@ eₜ [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          SIM eₛ' ≳ K @@ eₜ' [[ Χ ]] {{ Φ }}
        }}.
      Proof.
        iIntros "Hsim". iApply sim_post. iSmash.
      Qed.

      Lemma sim_decompose Φ1 Φ2 eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} -∗
        ( ∀ eₛ' eₜ',
          Φ1 eₛ' eₜ' -∗
          SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Φ2 }}
        ) -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}.
      Proof.
        iIntros "Hsim1 Hsim2".
        iEval (rewrite -(fill_empty eₛ) -(fill_empty eₜ)). iApply sim_bind.
        iApply (sim_mono' with "Hsim1 [Hsim2]").
        setoid_rewrite fill_empty. iSmash.
      Qed.

      Lemma sim_stepsₛ Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ∃ eₛ' σₛ',
            ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
            sim_state_interp σₛ' σₜ ∗
            SIM eₛ' ≳ eₜ [[ Χ ]] {{ Φ }}
        ) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        setoid_rewrite sim_fixpoint. apply sim_inner_stepsₛ. solve_proper.
      Qed.
      Lemma sim_stepₛ Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ∃ eₛ' σₛ',
            ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
            sim_state_interp σₛ' σₜ ∗
            SIM eₛ' ≳ eₜ [[ Χ ]] {{ Φ }}
        ) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        setoid_rewrite sim_fixpoint. apply sim_inner_stepₛ. solve_proper.
      Qed.
      Lemma sim_head_stepₛ Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ∃ eₛ' σₛ',
            ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
            sim_state_interp σₛ' σₜ ∗
            SIM eₛ' ≳ eₜ [[ Χ ]] {{ Φ }}
        ) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        setoid_rewrite sim_fixpoint. apply sim_inner_head_stepₛ. solve_proper.
      Qed.
      Lemma sim_pure_stepsₛ Φ eₛ1 eₛ2 eₜ :
        rtc (pure_step sim_progₛ) eₛ1 eₛ2 →
        SIM eₛ2 ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ1 ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite !sim_fixpoint. apply sim_inner_pure_stepsₛ. solve_proper.
      Qed.
      Lemma sim_pure_stepₛ Φ eₛ1 eₛ2 eₜ :
        pure_step sim_progₛ eₛ1 eₛ2 →
        SIM eₛ2 ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ1 ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite !sim_fixpoint. apply sim_inner_pure_stepₛ. solve_proper.
      Qed.
      Lemma sim_pure_head_stepsₛ Φ eₛ1 eₛ2 eₜ :
        rtc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
        SIM eₛ2 ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ1 ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite !sim_fixpoint. apply sim_inner_pure_head_stepsₛ. solve_proper.
      Qed.
      Lemma sim_pure_head_stepₛ Φ eₛ1 eₛ2 eₜ :
        pure_head_step sim_progₛ eₛ1 eₛ2 →
        SIM eₛ2 ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ1 ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite !sim_fixpoint. apply sim_inner_pure_head_stepₛ. solve_proper.
      Qed.

      Lemma sim_stepₜ Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                sim_state_interp σₛ σₜ' ∗
                SIM eₛ ≳ eₜ' [[ Χ ]] {{ Φ }}
        ) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        setoid_rewrite sim_fixpoint. apply sim_inner_stepₜ. solve_proper.
      Qed.
      Lemma sim_head_stepₜ Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                sim_state_interp σₛ σₜ' ∗
                SIM eₛ ≳ eₜ' [[ Χ ]] {{ Φ }}
        ) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        setoid_rewrite sim_fixpoint. apply sim_inner_head_stepₜ. solve_proper.
      Qed.
      Lemma sim_pure_stepsₜ Φ eₛ eₜ1 eₜ2 :
        rtc (pure_step sim_progₜ) eₜ1 eₜ2 →
        SIM eₛ ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ ≳ eₜ1 [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite !sim_fixpoint. apply sim_inner_pure_stepsₜ. solve_proper.
      Qed.
      Lemma sim_pure_stepₜ Φ eₛ eₜ1 eₜ2 :
        pure_step sim_progₜ eₜ1 eₜ2 →
        SIM eₛ ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ ≳ eₜ1 [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite !sim_fixpoint. apply sim_inner_pure_stepₜ. solve_proper.
      Qed.
      Lemma sim_pure_head_stepsₜ Φ eₛ eₜ1 eₜ2 :
        rtc (pure_head_step sim_progₜ) eₜ1 eₜ2 →
        SIM eₛ ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ ≳ eₜ1 [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite !sim_fixpoint. apply sim_inner_pure_head_stepsₜ. solve_proper.
      Qed.
      Lemma sim_pure_head_stepₜ Φ eₛ eₜ1 eₜ2 :
        pure_head_step sim_progₜ eₜ1 eₜ2 →
        SIM eₛ ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ ≳ eₜ1 [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite !sim_fixpoint. apply sim_inner_pure_head_stepₜ. solve_proper.
      Qed.

      Lemma sim_steps Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                ∃ eₛ' σₛ',
                ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
                sim_state_interp σₛ' σₜ' ∗
                SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}
        ) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint. apply sim_inner_steps. solve_proper.
      Qed.
      Lemma sim_step Φ eₛ eₜ :
        ( ∀ σₛ σₜ, sim_state_interp σₛ σₜ ==∗
            ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                ∃ eₛ' σₛ',
                ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
                sim_state_interp σₛ' σₜ' ∗
                SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}
        ) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint. apply sim_inner_step. solve_proper.
      Qed.
      Lemma sim_head_step Φ eₛ eₜ :
        ( ∀ σₛ σₜ, sim_state_interp σₛ σₜ ==∗
            ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
              ∀ eₜ' σₜ',
              ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
                ∃ eₛ' σₛ',
                ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
                sim_state_interp σₛ' σₜ' ∗
                SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}
        ) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint. apply sim_inner_head_step. solve_proper.
      Qed.
      Lemma sim_pure_steps Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        rtc (pure_step sim_progₛ) eₛ1 eₛ2 →
        rtc (pure_step sim_progₜ) eₜ1 eₜ2 →
        SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }}.
      Proof.
        intros. rewrite sim_pure_stepsₛ // sim_pure_stepsₜ //.
      Qed.
      Lemma sim_pure_step Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        pure_step sim_progₛ eₛ1 eₛ2 →
        pure_step sim_progₜ eₜ1 eₜ2 →
        SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }}.
      Proof.
        intros. rewrite sim_pure_stepₛ // sim_pure_stepₜ //.
      Qed.
      Lemma sim_pure_head_steps Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        rtc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
        rtc (pure_head_step sim_progₜ) eₜ1 eₜ2 →
        SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }}.
      Proof.
        intros. rewrite sim_pure_head_stepsₛ // sim_pure_head_stepsₜ //.
      Qed.
      Lemma sim_pure_head_step Φ eₛ1 eₛ2 eₜ1 eₜ2 :
        pure_head_step sim_progₛ eₛ1 eₛ2 →
        pure_head_step sim_progₜ eₜ1 eₜ2 →
        SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
        SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }}.
      Proof.
        intros. rewrite sim_pure_head_stepₛ // sim_pure_head_stepₜ //.
      Qed.

      Lemma sim_apply_protocol Ψ Φ eₛ eₜ :
        ( ∀ σₛ σₜ,
          sim_state_interp σₛ σₜ ==∗
            Χ Ψ eₛ eₜ ∗
            sim_state_interp σₛ σₜ ∗
              ∀ eₛ eₜ,
              Ψ eₛ eₜ -∗
              SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}
        ) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
      Proof.
        rewrite sim_fixpoint. iIntros "Hsim".
        iApply (sim_inner_apply_protocol Ψ ∅ _ ∅); [solve_proper | rewrite fill_empty //.. |]. iIntros "%σₛ %σₜ Hsi".
        iMod ("Hsim" with "Hsi") as "($ & $ & Hsim)". iIntros "!> %eₛ' %eₜ' HΨ !>".
        rewrite !fill_empty -sim_fixpoint. iSmash.
      Qed.
    End sim.

    Section simv.
      Lemma simv_post Φ vₛ vₜ eₛ eₜ :
        eₛ = of_val vₛ →
        eₜ = of_val vₜ →
        Φ vₛ vₜ ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}.
      Proof.
        rewrite simv_unseal -sim_post. iSmash.
      Qed.

      Lemma simv_cupd_mono Φ1 Φ2 eₛ eₜ :
        (Φ1 +++∗ Φ2) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ1 }} -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ2 }}.
      Proof.
        rewrite -sim_cupd_mono. setoid_rewrite <- sim_post_vals_cupd_mono. iSmash.
      Qed.
      Lemma simv_bupd_mono Φ1 Φ2 eₛ eₜ :
        (Φ1 ===∗ Φ2) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ1 }} -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ2 }}.
      Proof.
        rewrite -sim_bupd_mono. setoid_rewrite <- sim_post_vals_bupd_mono. iSmash.
      Qed.
      Lemma simv_mono Φ1 Φ2 eₛ eₜ :
        (Φ1 --∗ Φ2) ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ1 }} -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ2 }}.
      Proof.
        rewrite -sim_mono. setoid_rewrite <- sim_post_vals_mono. iSmash.
      Qed.
      Lemma simv_mono' Φ1 Φ2 eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ1 }} ⊢
        (Φ1 --∗ Φ2) -∗
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ2 }}.
      Proof.
        rewrite simv_mono. iSmash.
      Qed.

      Lemma simv_cupd Φ eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, |++> Φ eₛ eₜ }} ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}.
      Proof.
        apply bi.wand_entails. rewrite -simv_cupd_mono. iSmash.
      Qed.
      Lemma simv_bupd Φ eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, |==> Φ eₛ eₜ }} ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}.
      Proof.
        apply bi.wand_entails. rewrite -simv_bupd_mono. iSmash.
      Qed.

      Lemma simv_frame_l R Φ eₛ eₜ :
        R ∗ SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }} ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, R ∗ Φ eₛ eₜ }}.
      Proof.
        rewrite simv_mono'. iSmash.
      Qed.
      Lemma simv_frame_r R Φ eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }} ∗ R ⊢
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, Φ eₛ eₜ ∗ R }}.
      Proof.
        rewrite simv_mono'. iSmash.
      Qed.

      Lemma simv_bind Φ Kₛ eₛ Kₜ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ vₛ vₜ,
          SIM Kₛ @@ of_val vₛ ≳ Kₜ @@ of_val vₜ [[ Χ ]] {{# Φ }}
        }} ⊢
        SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ Χ ]] {{# Φ }}.
      Proof.
        rewrite !simv_unseal -sim_bind sim_mono'. iSmash.
      Qed.
      Lemma simv_bindₛ Φ K eₛ eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ vₛ vₜ,
          SIM K @@ of_val vₛ ≳ of_val vₜ [[ Χ ]] {{# Φ }}
        }} ⊢
        SIM K @@ eₛ ≳ eₜ [[ Χ ]] {{# Φ }}.
      Proof.
        rewrite !simv_unseal -sim_bindₛ sim_mono'. iSmash.
      Qed.
      Lemma simv_bindₜ Φ eₛ K eₜ :
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ vₛ vₜ,
          SIM of_val vₛ ≳ K @@ of_val vₜ [[ Χ ]] {{# Φ }}
        }} ⊢
        SIM eₛ ≳ K @@ eₜ [[ Χ ]] {{# Φ }}.
      Proof.
        rewrite !simv_unseal -sim_bindₜ sim_mono'. iSmash.
      Qed.
    End simv.
  End protocol.

  Section protocol.
    Context Χ.

    Lemma sim_close Φ eₛ eₜ :
      □ (
        ∀ Ψ eₛ eₜ,
        Χ Ψ eₛ eₜ -∗
        sim_inner ⊥ (λ _, sim Χ Ψ) (λ _ _, False) eₛ eₜ
      ) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} -∗
      SIM eₛ ≳ eₜ {{ Φ }}.
    Proof.
      iIntros "#H".
      iApply (sim_coind with "[]"); first solve_proper. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ".
      rewrite sim_fixpoint. iApply (sim_inner_ind with "[]"); first solve_proper.
      { solve_proper_prepare. apply sim_inner_ne; done || solve_proper. }
      clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ Hsim".
      setoid_rewrite sim_inner_fixpoint at 2; last solve_proper.
      iIntros "%σₛ %σₜ Hsi".
      iMod ("Hsim" with "Hsi") as "[Hsim | [Hsim | [Hsim | Hsim]]]"; auto.
      iDestruct "Hsim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & HΧ & Hsi & Hsim)".
      iDestruct ("H" with "HΧ") as "HΨ". iClear "H".
      iRevert (σₛ σₜ) "Hsi". setoid_rewrite <- sim_inner_fixpoint; last solve_proper.
      iApply (sim_inner_bind' with "HΨ [Hsim]"); [solve_proper | iIntros "%eₛ %eₜ HΨ" | iIntros "%eₛ %eₜ []"].
      iApply (sim_bind' with "HΨ"). clear eₛ eₜ. iIntros "%eₛ %eₜ HΨ".
      iApply cupd_sim.
      rewrite sim_fixpoint.
      admit.
    Admitted.
    Lemma sim_close_steps Φ eₛ eₜ :
      □ (
        ∀ Ψ eₛ σₛ eₜ σₜ,
        Χ Ψ eₛ eₜ -∗
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              ∃ eₛ' σₛ',
              ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
              sim_state_interp σₛ' σₜ' ∗
              SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Ψ }}
      ) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} -∗
      SIM eₛ ≳ eₜ {{ Φ }}.
    Proof.
      iIntros "#H".
      iApply sim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
      iApply sim_inner_steps. iIntros "%σₛ %σₜ".
      iApply ("H" with "HΧ").
    Qed.
    Lemma sim_close_step Φ eₛ eₜ :
      □ (
        ∀ Ψ eₛ σₛ eₜ σₜ,
        Χ Ψ eₛ eₜ -∗
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              ∃ eₛ' σₛ',
              ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
              sim_state_interp σₛ' σₜ' ∗
              SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Ψ }}
      ) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} -∗
      SIM eₛ ≳ eₜ {{ Φ }}.
    Proof.
      iIntros "#H".
      iApply sim_close_steps. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %σₛ %eₜ %σₜ HΧ Hsi".
      iMod ("H" with "HΧ Hsi") as "(%Hreducibleₜ & Hsim)". iClear "H".
      iSplitR; first done. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
      iMod ("Hsim" with "[//]") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi & Hsim)".
      iExists eₛ', σₛ'. iFrame. eauto using tc_once, prim_step_step.
    Qed.
    Lemma sim_close_head_step Φ eₛ eₜ :
      □ (
        ∀ Ψ eₛ σₛ eₜ σₜ,
        Χ Ψ eₛ eₜ -∗
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              ∃ eₛ' σₛ',
              ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
              sim_state_interp σₛ' σₜ' ∗
              SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Ψ }}
      ) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} -∗
      SIM eₛ ≳ eₜ {{ Φ }}.
    Proof.
      iIntros "#H".
      iApply sim_close_step. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %σₛ %eₜ %σₜ HΧ Hsi".
      iMod ("H" with "HΧ Hsi") as "(%Hreducibleₜ & Hsim)". iClear "H".
      iSplitR; first auto using head_reducible_reducible. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
      apply head_reducible_prim_step in Hstepₜ; last done.
      iMod ("Hsim" with "[//]") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi & Hsim)".
      iExists eₛ', σₛ'. iFrame. iPureIntro. apply head_step_prim_step. done.
    Qed.
    Lemma sim_close_pure_steps Φ eₛ eₜ :
      □ (
        ∀ Ψ eₛ eₜ,
        Χ Ψ eₛ eₜ -∗
          ∃ eₛ' eₜ',
          ⌜tc (pure_step sim_progₛ) eₛ eₛ' ∧ pure_step sim_progₜ eₜ eₜ'⌝ ∗
          SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Ψ }}
      ) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} -∗
      SIM eₛ ≳ eₜ {{ Φ }}.
    Proof.
      iIntros "#H".
      iApply sim_close_steps. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %σₛ %eₜ %σₜ HΧ Hsi !>".
      iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepsₛ & %Hstepₜ) & Hsim)".
      iSplit; first eauto using pure_step_safe. iIntros "%_eₜ' %_σₜ %_Hstepₜ !>".
      eapply pure_step_det in _Hstepₜ as (-> & ->); last done.
      iExists eₛ', σₛ. iFrame. iPureIntro.
      eapply (tc_congruence (λ eₛ, (eₛ, σₛ))); last done.
      eauto using prim_step_step, pure_step_prim_step.
    Qed.
    Lemma sim_close_pure_step Φ eₛ eₜ :
      □ (
        ∀ Ψ eₛ eₜ,
        Χ Ψ eₛ eₜ -∗
          ∃ eₛ' eₜ',
          ⌜pure_step sim_progₛ eₛ eₛ' ∧ pure_step sim_progₜ eₜ eₜ'⌝ ∗
          SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Ψ }}
      ) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} -∗
      SIM eₛ ≳ eₜ {{ Φ }}.
    Proof.
      iIntros "#H".
      iApply sim_close_pure_steps. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
      iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepₛ & %Hstepₜ) & Hsim)". iClear "H".
      iExists eₛ', eₜ'. iFrame. auto using tc_once.
    Qed.
    Lemma sim_close_pure_head_steps Φ eₛ eₜ :
      □ (
        ∀ Ψ eₛ eₜ,
        Χ Ψ eₛ eₜ -∗
          ∃ eₛ' eₜ',
          ⌜tc (pure_head_step sim_progₛ) eₛ eₛ' ∧ pure_head_step sim_progₜ eₜ eₜ'⌝ ∗
          SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Ψ }}
      ) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} -∗
      SIM eₛ ≳ eₜ {{ Φ }}.
    Proof.
      iIntros "#H".
      iApply sim_close_pure_steps. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
      iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepₛ & %Hstepsₜ) & Hsim)". iClear "H".
      iExists eₛ', eₜ'. iFrame. eauto 10 using (tc_congruence id), pure_head_step_pure_step.
    Qed.
    Lemma sim_close_pure_head_step Φ eₛ eₜ :
      □ (
        ∀ Ψ eₛ eₜ,
        Χ Ψ eₛ eₜ -∗
          ∃ eₛ' eₜ',
          ⌜pure_head_step sim_progₛ eₛ eₛ' ∧ pure_head_step sim_progₜ eₜ eₜ'⌝ ∗
          SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Ψ }}
      ) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} -∗
      SIM eₛ ≳ eₜ {{ Φ }}.
    Proof.
      iIntros "#H".
      iApply sim_close_pure_head_steps. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
      iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepₛ & %Hstepₜ) & Hsim)". iClear "H".
      iExists eₛ', eₜ'. iFrame. auto using tc_once.
    Qed.
  End protocol.
End sim_state.
