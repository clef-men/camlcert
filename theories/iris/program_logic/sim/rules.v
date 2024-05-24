From iris.bi Require Import
  fixpoint.

From camlcert Require Import
  prelude.
From camlcert.iris.base_logic Require Import
  lib.cupd.proofmode.
From camlcert.iris.program_logic Require Export
  sim.definition.
From camlcert.iris.program_logic Require Import
  sim.notations.

#[local] Notation "Φ1 --∗ Φ2" :=
  (∀ x1 x2, Φ1 x1 x2 -∗ Φ2 x1 x2)%I
( at level 99,
  Φ2 at level 200,
  right associativity,
  format "'[' Φ1  --∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 --∗ Φ2" := (
  ⊢ Φ1 --∗ Φ2
)(only parsing
) : stdpp_scope.
#[local] Notation "Φ1 ===∗ Φ2" :=
  (∀ x1 x2, Φ1 x1 x2 -∗ |==> Φ2 x1 x2)%I
( at level 99,
  Φ2 at level 200,
  format "'[' Φ1  ===∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 ===∗ Φ2" := (
  ⊢ Φ1 ===∗ Φ2
)(only parsing
) : stdpp_scope.
#[local] Notation "Φ1 +++∗ Φ2" :=
  (∀ x1 x2, Φ1 x1 x2 -∗ |++> Φ2 x1 x2)%I
( at level 99,
  Φ2 at level 200,
  format "'[' Φ1  +++∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 +++∗ Φ2" := (
  ⊢ Φ1 +++∗ Φ2
)(only parsing
) : stdpp_scope.

#[local] Notation "Φ1 ---∗ Φ2" :=
  (∀ x1 x2 x3, Φ1 x1 x2 x3 -∗ Φ2 x1 x2 x3)%I
( at level 99,
  Φ2 at level 200,
  right associativity,
  format "'[' Φ1  ---∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 ---∗ Φ2" := (
  ⊢ Φ1 ---∗ Φ2
)(only parsing
) : stdpp_scope.
#[local] Notation "Φ1 ====∗ Φ2" :=
  (∀ x1 x2 x3, Φ1 x1 x2 x3 -∗ |==> Φ2 x1 x2 x3)%I
( at level 99,
  Φ2 at level 200,
  format "'[' Φ1  ====∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 ====∗ Φ2" := (
  ⊢ Φ1 ====∗ Φ2
)(only parsing
) : stdpp_scope.
#[local] Notation "Φ1 ++++∗ Φ2" :=
  (∀ x1 x2 x3, Φ1 x1 x2 x3 -∗ |++> Φ2 x1 x2 x3)%I
( at level 99,
  Φ2 at level 200,
  format "'[' Φ1  ++++∗  '/' '[' Φ2 ']' ']'"
) : bi_scope.
#[local] Notation "Φ1 ++++∗ Φ2" := (
  ⊢ Φ1 ++++∗ Φ2
)(only parsing
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

  Notation sim_protocol :=
    (sim_protocol PROP Λₛ Λₜ).
  Notation sim_protocol_O :=
    (sim_protocol_O PROP Λₛ Λₜ).

  Implicit Types Χ : sim_protocol.
  Implicit Types N M I : sim_protocol_O.

  Section sim_body.
    #[global] Instance sim_body_ne Χ n :
      Proper (
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) (sim_body Χ).
    Proof.
      intros N1 N2 HN M1 M2 HM Φ1 Φ2 HΦ eₛ1 eₛ2 ->%leibniz_equiv eₜ1 eₜ2 ->%leibniz_equiv.
      solve_proper_core ltac:(fun _ => f_equiv || apply HΧ || apply HN || apply HM || apply HΦ).
    Qed.
    #[global] Instance sim_body_proper Χ :
      Proper (
        ((≡) ==> (≡)) ==>
        ((≡) ==> (≡)) ==>
        (≡) ==>
        (≡) ==>
        (≡) ==>
        (≡)
      ) (sim_body Χ).
    Proof.
      intros N1 N2 HN M1 M2 HM Φ1 Φ2 HΦ eₛ1 eₛ2 ->%leibniz_equiv eₜ1 eₜ2 ->%leibniz_equiv.
      rewrite /sim_body. repeat (f_equiv || apply HΧ || apply HN || apply HM || apply HΦ).
    Qed.

    Lemma sim_body_strongly_stuck Χ N M Φ eₛ eₜ :
      strongly_stuck sim_progₛ eₛ →
      strongly_stuck sim_progₜ eₜ →
      ⊢ sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "%Hstrongly_stuckₛ %Hstrong_stuckₜ %σₛ %σₜ Hsi !>".
      iLeft. iFrame. auto using strongly_stuck_stuck.
    Qed.
    Lemma sim_body_strongly_head_stuck Χ N M Φ eₛ eₜ :
      strongly_head_stuck sim_progₛ eₛ →
      strongly_head_stuck sim_progₜ eₜ →
      ⊢ sim_body Χ N M Φ eₛ eₜ.
    Proof.
      intros.
      apply sim_body_strongly_stuck; apply strongly_head_stuck_strongly_stuck; done.
    Qed.

    Lemma sim_body_post Χ N M Φ eₛ eₜ :
      Φ eₛ eₜ ⊢
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iSmash.
    Qed.

    Lemma cupd_sim_body Χ N M Φ eₛ eₜ :
      (|++> sim_body Χ N M Φ eₛ eₜ) ⊢
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "Hsim %σₛ %σₜ Hsi".
      rewrite sim_cupd_eq. iMod ("Hsim" with "Hsi") as "(Hsi & Hsim)".
      iApply ("Hsim" with "Hsi").
    Qed.
    Lemma bupd_sim_body Χ N M Φ eₛ eₜ :
      (|==> sim_body Χ N M Φ eₛ eₜ) ⊢
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "Hsim".
      iApply cupd_sim_body.
      iMod "Hsim" as "$". iSmash.
    Qed.

    Lemma sim_body_monotone R Χ1 Χ2 N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
      (Χ1 ++++∗ Χ2) -∗
      (R Φ1 Φ2 -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      (R Φ1 Φ2 -∗ M1 Φ1 +++∗ M2 Φ2) -∗
      (R Φ1 Φ2 -∗ Φ1 +++∗ Φ2) -∗
      R Φ1 Φ2 -∗
      sim_body Χ1 N1 M1 Φ1 eₛ eₜ -∗
      sim_body Χ2 N2 M2 Φ2 eₛ eₜ.
    Proof.
      setoid_rewrite sim_cupd_eq.
      iIntros "HΧ HN HM HΦ HR Hsim %σₛ %σₜ Hsi".
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
      - iDestruct "Hsim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & HΧ1 & Hsi & HM1)".
        iMod ("HΧ" with "HΧ1 Hsi") as "(Hsi & HΧ2)".
        do 3 iRight. iExists Kₛ, eₛ', Kₜ, eₜ', Ψ. iFrame. iSplitR; first iSmash. iIntros "!> %eₛ %eₜ HΨ".
        iMod ("HM1" with "HΨ") as "HM1".
        iApply ("HM" with "HR HM1").
    Qed.

    Lemma sim_body_cupd_mono Χ1 Χ2 N1 N2 M1 M2 Φ eₛ eₜ :
      (Χ1 ++++∗ Χ2) -∗
      (N1 ++++∗ N2) -∗
      (M1 ++++∗ M2) -∗
      sim_body Χ1 N1 M1 Φ eₛ eₜ -∗
      sim_body Χ2 N2 M2 Φ eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM".
      iApply (sim_body_monotone (λ _ _, True)%I with "HΧ [HN] [HM] [] [//]"); iSmash.
    Qed.
    Lemma sim_body_bupd_mono Χ1 Χ2 N1 N2 M1 M2 Φ eₛ eₜ :
      (Χ1 ====∗ Χ2) -∗
      (N1 ====∗ N2) -∗
      (M1 ====∗ M2) -∗
      sim_body Χ1 N1 M1 Φ eₛ eₜ -∗
      sim_body Χ2 N2 M2 Φ eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM".
      iApply (sim_body_cupd_mono with "[HΧ] [HN] [HM]"); iSmash.
    Qed.
    Lemma sim_body_mono Χ1 Χ2 N1 N2 M1 M2 Φ eₛ eₜ :
      (Χ1 ---∗ Χ2) -∗
      (N1 ---∗ N2) -∗
      (M1 ---∗ M2) -∗
      sim_body Χ1 N1 M1 Φ eₛ eₜ -∗
      sim_body Χ2 N2 M2 Φ eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM".
      iApply (sim_body_bupd_mono with "[HΧ] [HN] [HM]"); iSmash.
    Qed.

    Lemma sim_body_strong_cupd_mono Χ1 Χ2 N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
      (Χ1 ++++∗ Χ2) -∗
      ((Φ1 +++∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      ((Φ1 +++∗ Φ2) -∗ M1 Φ1 +++∗ M2 Φ2) -∗
      (Φ1 +++∗ Φ2) -∗
      sim_body Χ1 N1 M1 Φ1 eₛ eₜ -∗
      sim_body Χ2 N2 M2 Φ2 eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM HΦ".
      iApply (sim_body_monotone (λ Φ1 Φ2, Φ1 +++∗ Φ2)%I with "HΧ [HN] [HM] [] HΦ"); iSmash+.
    Qed.
    Lemma sim_body_strong_bupd_mono Χ1 Χ2 N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
      (Χ1 ====∗ Χ2) -∗
      ((Φ1 ===∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      ((Φ1 ===∗ Φ2) -∗ M1 Φ1 +++∗ M2 Φ2) -∗
      (Φ1 ===∗ Φ2) -∗
      sim_body Χ1 N1 M1 Φ1 eₛ eₜ -∗
      sim_body Χ2 N2 M2 Φ2 eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM HΦ".
      iApply (sim_body_monotone (λ Φ1 Φ2, Φ1 ===∗ Φ2)%I with "[HΧ] [HN] [HM] [] HΦ"); iSmash+.
    Qed.
    Lemma sim_body_strong_mono Χ1 Χ2 N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
      (Χ1 ---∗ Χ2) -∗
      ((Φ1 --∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      ((Φ1 --∗ Φ2) -∗ M1 Φ1 +++∗ M2 Φ2) -∗
      (Φ1 --∗ Φ2) -∗
      sim_body Χ1 N1 M1 Φ1 eₛ eₜ -∗
      sim_body Χ2 N2 M2 Φ2 eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM HΦ".
      iApply (sim_body_monotone (λ Φ1 Φ2, Φ1 --∗ Φ2)%I with "[HΧ] [HN] [HM] [] HΦ"); iSmash+.
    Qed.

    Lemma sim_body_cupd Χ N M Φ eₛ eₜ :
      (N (λ eₛ eₜ, |++> Φ eₛ eₜ) +++∗ N Φ) -∗
      (M (λ eₛ eₜ, |++> Φ eₛ eₜ) +++∗ M Φ) -∗
      sim_body Χ N M (λ eₛ eₜ, |++> Φ eₛ eₜ) eₛ eₜ -∗
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HN HM".
      iApply (sim_body_strong_cupd_mono with "[] [HN] [HM]"); iSmash.
    Qed.
    Lemma sim_body_bupd Χ N M Φ eₛ eₜ :
      (N (λ eₛ eₜ, |==> Φ eₛ eₜ) +++∗ N Φ) -∗
      (M (λ eₛ eₜ, |==> Φ eₛ eₜ) +++∗ M Φ) -∗
      sim_body Χ N M (λ eₛ eₜ, |==> Φ eₛ eₜ) eₛ eₜ -∗
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HN HM".
      iApply (sim_body_strong_bupd_mono with "[] [HN] [HM]"); iSmash.
    Qed.

    Lemma sim_body_frame_l Χ N M R Φ eₛ eₜ :
      ( ∀ eₛ eₜ,
        R ∗ N Φ eₛ eₜ ++∗
        N (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ
      ) -∗
      ( ∀ eₛ eₜ,
        R ∗ M Φ eₛ eₜ ++∗
        M (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ
      ) -∗
      R ∗ sim_body Χ N M Φ eₛ eₜ -∗
      sim_body Χ N M (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ.
    Proof.
      iIntros "HN HM (HR & Hsim)".
      iApply (sim_body_monotone (λ _ _, R) with "[] [HN] [HM] [] HR Hsim"); iSmash.
    Qed.
    Lemma sim_body_frame_r Χ N M R Φ eₛ eₜ :
      ( ∀ eₛ eₜ,
        N Φ eₛ eₜ ∗ R ++∗
        N (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ
      ) -∗
      ( ∀ eₛ eₜ,
        M Φ eₛ eₜ ∗ R ++∗
        M (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ
      ) -∗
      sim_body Χ N M Φ eₛ eₜ ∗ R -∗
      sim_body Χ N M (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ.
    Proof.
      iIntros "HN HM (Hsim & HR)".
      iApply (sim_body_monotone (λ _ _, R) with "[] [HN] [HM] [] HR Hsim"); iSmash.
    Qed.

    (* TODO: sim_body_bind *)
    (* TODO: sim_body_bindₛ *)
    (* TODO: sim_body_bindₜ *)

    (* TODO: sim_body_bind_inv *)
    (* TODO: sim_body_bind_invₛ *)
    (* TODO: sim_body_bind_invₜ *)

    (* TODO: sim_body_decompose *)

    Lemma sim_body_stepsₛ Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ∃ eₛ' σₛ',
          ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
          sim_state_interp σₛ' σₜ ∗
          M Φ eₛ' eₜ
      ) ⊢
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iSmash.
    Qed.
    Lemma sim_body_stepₛ Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ∃ eₛ' σₛ',
          ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
          sim_state_interp σₛ' σₜ ∗
          M Φ eₛ' eₜ
      ) ⊢
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HM".
      iApply sim_body_stepsₛ. iIntros "%σₛ %σₜ Hsi".
      iMod ("HM" with "Hsi") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi)".
      iExists eₛ', σₛ'. iFrame. iPureIntro. eapply tc_once, prim_step_step; done.
    Qed.
    Lemma sim_body_head_stepₛ Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ∃ eₛ' σₛ',
          ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
          sim_state_interp σₛ' σₜ ∗
          M Φ eₛ' eₜ
      ) ⊢
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HM".
      iApply sim_body_stepₛ. iIntros "%σₛ %σₜ Hsi".
      iMod ("HM" with "Hsi") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi)".
      iExists eₛ', σₛ'. iFrame. iPureIntro. apply head_step_prim_step. done.
    Qed.
    Lemma sim_body_pure_stepsₛ Χ N M Φ eₛ1 eₛ2 eₜ :
      tc (pure_step sim_progₛ) eₛ1 eₛ2 →
      M Φ eₛ2 eₜ ⊢
      sim_body Χ N M Φ eₛ1 eₜ.
    Proof.
      iIntros "%Hstepsₛ HM".
      iApply sim_body_stepsₛ. iIntros "%σₛ %σₜ Hsi".
      iExists eₛ2, σₛ. iSplitR; last iSmash. iPureIntro.
      eapply (tc_congruence (λ eₛ, (eₛ, σₛ))); last done.
      eauto using prim_step_step, pure_step_prim_step.
    Qed.
    Lemma sim_body_pure_stepₛ Χ N M Φ eₛ1 eₛ2 eₜ :
      pure_step sim_progₛ eₛ1 eₛ2 →
      M Φ eₛ2 eₜ ⊢
      sim_body Χ N M Φ eₛ1 eₜ.
    Proof.
      intros Hstepₛ.
      iApply sim_body_pure_stepsₛ.
      eauto using tc_once.
    Qed.
    Lemma sim_body_pure_head_stepsₛ Χ N M Φ eₛ1 eₛ2 eₜ :
      tc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
      M Φ eₛ2 eₜ ⊢
      sim_body Χ N M Φ eₛ1 eₜ.
    Proof.
      intros Hstepsₛ.
      iApply sim_body_pure_stepsₛ.
      eauto using (tc_congruence id), pure_head_step_pure_step.
    Qed.
    Lemma sim_body_pure_head_stepₛ Χ N M Φ eₛ1 eₛ2 eₜ :
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      M Φ eₛ2 eₜ ⊢
      sim_body Χ N M Φ eₛ1 eₜ.
    Proof.
      intros Hstepₛ.
      iApply sim_body_pure_head_stepsₛ.
      eauto using tc_once.
    Qed.

    Lemma sim_body_stepₜ Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              M Φ eₛ eₜ'
      ) ⊢
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iSmash.
    Qed.
    Lemma sim_body_head_stepₜ Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              M Φ eₛ eₜ'
      ) ⊢
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HM".
      iApply sim_body_stepₜ. iIntros "%σₛ %σₜ Hsi".
      iMod ("HM" with "Hsi") as "(%Hreducibleₜ & HM)".
      iSplitR; first auto using head_reducible_reducible. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
      apply head_reducible_prim_step in Hstepₜ; last done.
      iApply "HM". iSmash.
    Qed.
    Lemma sim_body_pure_stepₜ Χ N M Φ eₛ eₜ1 eₜ2 :
      pure_step sim_progₜ eₜ1 eₜ2 →
      M Φ eₛ eₜ2 ⊢
      sim_body Χ N M Φ eₛ eₜ1.
    Proof.
      iIntros "%Hstepₜ HM".
      iApply sim_body_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
      iSplit; eauto using pure_step_safe. iIntros "%eₜ' %σₜ' %Hstepₜ' !>".
      eapply pure_step_det in Hstepₜ; last done. destruct Hstepₜ as (-> & ->).
      iSmash.
    Qed.
    Lemma sim_body_pure_head_stepₜ Χ N M Φ eₛ eₜ1 eₜ2 :
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      M Φ eₛ eₜ2 ⊢
      sim_body Χ N M Φ eₛ eₜ1.
    Proof.
      intros Hstepₜ.
      iApply sim_body_pure_stepₜ.
      eauto using pure_head_step_pure_step.
    Qed.

    Lemma sim_body_steps Χ N M Φ eₛ eₜ :
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
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HN %σₛ %σₜ Hsi".
      do 2 iRight. iLeft.
      iMod ("HN" with "Hsi") as "($ & HN)".
      iIntros "!> %eₜ' %σₜ' %Hstepₜ".
      iRight. iApply ("HN" with "[//]").
    Qed.
    Lemma sim_body_step Χ N M Φ eₛ eₜ :
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
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HN".
      iApply sim_body_steps. iIntros "%σₛ %σₜ Hsi".
      iMod ("HN" with "Hsi") as "(%Hreducibleₜ & HN)".
      iSplitR; first iSmash. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
      iMod ("HN" with "[//]") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi & HN)".
      iExists eₛ', σₛ'. iFrame. eauto using tc_once, prim_step_step.
    Qed.
    Lemma sim_body_head_step Χ N M Φ eₛ eₜ :
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
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HN".
      iApply sim_body_step. iIntros "%σₛ %σₜ Hsi".
      iMod ("HN" with "Hsi") as "(%Hreducibleₜ & HN)".
      iSplitR; first auto using head_reducible_reducible. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
      apply head_reducible_prim_step in Hstepₜ; last done.
      iMod ("HN" with "[//]") as "(%eₛ' & %σₛ' & %Hstepₛ & Hsi & HN)".
      iExists eₛ', σₛ'. iFrame. iPureIntro. apply head_step_prim_step. done.
    Qed.
    Lemma sim_body_pure_steps Χ N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      tc (pure_step sim_progₛ) eₛ1 eₛ2 →
      pure_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      sim_body Χ N M Φ eₛ1 eₜ1.
    Proof.
      iIntros "%Hstepsₛ %Hstepₜ HN".
      iApply sim_body_steps. iIntros "%σₛ %σₜ Hsi !>".
      iSplit; first eauto using pure_step_safe. iIntros "%_eₜ2 %_σₜ %_Hstepₜ !>".
      eapply pure_step_det in _Hstepₜ as (-> & ->); last done.
      iExists eₛ2, σₛ. iFrame. iPureIntro.
      eapply (tc_congruence (λ eₛ, (eₛ, σₛ))); last done.
      eauto using prim_step_step, pure_step_prim_step.
    Qed.
    Lemma sim_body_pure_step Χ N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      pure_step sim_progₛ eₛ1 eₛ2 →
      pure_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      sim_body Χ N M Φ eₛ1 eₜ1.
    Proof.
      iIntros "%Hstepₛ %Hstepₜ HN".
      iApply (sim_body_pure_steps with "HN"); first apply tc_once; done.
    Qed.
    Lemma sim_body_pure_head_steps Χ N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      tc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      sim_body Χ N M Φ eₛ1 eₜ1.
    Proof.
      iIntros "%Hstepₛ %Hstepₜ HN".
      iApply (sim_body_pure_steps with "HN");
        eauto using (tc_congruence id), pure_head_step_pure_step.
    Qed.
    Lemma sim_body_pure_head_step Χ N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      sim_body Χ N M Φ eₛ1 eₜ1.
    Proof.
      iIntros "%Hstepₛ %Hstepₜ HN".
      iApply (sim_body_pure_head_steps with "HN"); first apply tc_once; done.
    Qed.

    Lemma sim_body_apply_protocol Ψ Kₛ eₛ' Kₜ eₜ' Χ N M Φ eₛ eₜ :
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
      sim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros (-> ->) "H %σₛ %σₜ Hsi".
      do 3 iRight. iExists Kₛ, eₛ', Kₜ, eₜ', Ψ. iSplitR; first iSmash.
      iApply ("H" with "Hsi").
    Qed.
  End sim_body.

  Section sim_inner.
    #[local] Instance sim_body'_ne Χ n :
      Proper (
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) (definition.sim_body' Χ).
    Proof.
      intros N1 N2 HN M1 M2 HM ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
      simpl in HΦ, Heₛ, Heₜ. subst.
      apply sim_body_ne; done || solve_proper.
    Qed.
    #[local] Instance sim_body'_proper Χ :
      Proper (
        ((≡) ==> (≡)) ==>
        ((≡) ==> (≡)) ==>
        (≡) ==>
        (≡)
      ) (definition.sim_body' Χ).
    Proof.
      intros N1 N2 HN M1 M2 HM ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
      simpl in HΦ, Heₛ, Heₜ. subst.
      apply sim_body_proper; done || solve_proper.
    Qed.

    #[local] Instance sim_body'_mono_pred Χ N :
      NonExpansive N →
      BiMonoPred (definition.sim_body' Χ N).
    Proof.
      intros HN. split; last solve_proper.
      iIntros "%M1 %M2 %HM1 %HM2 #HM" (((Φ & eₛ) & eₜ)) "Hsim /=".
      iApply (sim_body_mono with "[] [] [] Hsim"); iSmash.
    Qed.

    #[global] Instance sim_inner_ne Χ n :
      Proper (
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) (sim_inner Χ).
    Proof.
      rewrite definition.sim_inner_unseal /definition.sim_inner_def /curry3.
      solve_proper.
    Qed.
    #[global] Instance sim_inner_proper Χ :
      Proper (
        ((≡) ==> (≡)) ==>
        (≡) ==>
        (≡) ==>
        (≡) ==>
        (≡)
      ) (sim_inner Χ).
    Proof.
      rewrite definition.sim_inner_unseal /definition.sim_inner_def /curry3.
      solve_proper.
    Qed.

    Lemma sim_inner_fixpoint Χ N Φ eₛ eₜ :
      NonExpansive N →
      sim_inner Χ N Φ eₛ eₜ ⊣⊢
      sim_body Χ N (sim_inner Χ N) Φ eₛ eₜ.
    Proof.
      rewrite definition.sim_inner_unseal.
      intros. setoid_rewrite least_fixpoint_unfold; [done | apply _].
    Qed.
    Lemma sim_inner_unfold Χ N Φ eₛ eₜ :
      NonExpansive N →
      sim_inner Χ N Φ eₛ eₜ ⊢
      sim_body Χ N (sim_inner Χ N) Φ eₛ eₜ.
    Proof.
      intros. rewrite sim_inner_fixpoint //.
    Qed.
    Lemma sim_inner_fold Χ N Φ eₛ eₜ :
      NonExpansive N →
      sim_body Χ N (sim_inner Χ N) Φ eₛ eₜ ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros. rewrite sim_inner_fixpoint //.
    Qed.

    Lemma sim_inner_strong_ind I Χ N Φ eₛ eₜ :
      NonExpansive N →
      NonExpansive I →
      □ (sim_body Χ N (λ Φ eₛ eₜ, I Φ eₛ eₜ ∧ sim_inner Χ N Φ eₛ eₜ) ---∗ I) ⊢
      sim_inner Χ N Φ eₛ eₜ -∗
      I Φ eₛ eₜ.
    Proof.
      rewrite definition.sim_inner_unseal.
      iIntros "%HN %HI #Hind Hsim".
      replace (I Φ eₛ eₜ) with ((uncurry3 I) (Φ, eₛ, eₜ)); last done.
      iApply (least_fixpoint_ind with "[] Hsim"). clear Φ eₛ eₜ. iIntros "!>" (((Φ & eₛ) & eₜ)) "Hsim /=".
      iApply ("Hind" with "Hsim").
    Qed.
    Lemma sim_inner_ind I Χ N Φ eₛ eₜ :
      NonExpansive N →
      NonExpansive I →
      □ (sim_body Χ N I ---∗ I) ⊢
      sim_inner Χ N Φ eₛ eₜ -∗
      I Φ eₛ eₜ.
    Proof.
      iIntros "%HN %HI #Hind".
      iApply sim_inner_strong_ind. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ Hsim".
      iApply "Hind".
      iApply (sim_body_mono with "[] [] [] Hsim"); [iSmash.. |]. clear Φ eₛ eₜ. iIntros "%Φ %eₛ %eₜ (HI & _) //".
    Qed.

    Lemma sim_inner_strongly_stuck Χ N Φ eₛ eₜ :
      NonExpansive N →
      strongly_stuck sim_progₛ eₛ →
      strongly_stuck sim_progₜ eₜ →
      ⊢ sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite sim_inner_fixpoint. apply sim_body_strongly_stuck.
    Qed.
    Lemma sim_inner_strongly_head_stuck Χ N Φ eₛ eₜ :
      NonExpansive N →
      strongly_head_stuck sim_progₛ eₛ →
      strongly_head_stuck sim_progₜ eₜ →
      ⊢ sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite sim_inner_fixpoint. apply sim_body_strongly_head_stuck.
    Qed.

    Lemma sim_inner_post Χ N Φ eₛ eₜ :
      NonExpansive N →
      Φ eₛ eₜ ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite sim_inner_fixpoint //. apply sim_body_post.
    Qed.

    Lemma cupd_sim_inner Χ N Φ eₛ eₜ :
      NonExpansive N →
      (|++> sim_inner Χ N Φ eₛ eₜ) ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite sim_inner_fixpoint. apply cupd_sim_body.
    Qed.
    Lemma bupd_sim_inner Χ N Φ eₛ eₜ :
      NonExpansive N →
      (|==> sim_inner Χ N Φ eₛ eₜ) ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite sim_inner_fixpoint. apply bupd_sim_body.
    Qed.

    Lemma sim_inner_monotone R Χ1 Χ2 N1 N2 Φ1 Φ2 eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      NonExpansive2 R →
      □ (Χ1 ++++∗ Χ2) -∗
      □ (R Φ1 Φ2 -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      □ (R Φ1 Φ2 -∗ Φ1 +++∗ Φ2) -∗
      R Φ1 Φ2 -∗
      sim_inner Χ1 N1 Φ1 eₛ eₜ -∗
      sim_inner Χ2 N2 Φ2 eₛ eₜ.
    Proof.
      intros HN1 HN2 HR.
      set I := λ Φ1 eₛ eₜ, (
        □ (Χ1 ++++∗ Χ2) -∗
        □ (R Φ1 Φ2 -∗ N1 Φ1 +++∗ N2 Φ2) -∗
        □ (R Φ1 Φ2 -∗ Φ1 +++∗ Φ2) -∗
        R Φ1 Φ2 -∗
        sim_inner Χ2 N2 Φ2 eₛ eₜ
      )%I.
      cut (sim_inner Χ1 N1 Φ1 eₛ eₜ -∗ I Φ1 eₛ eₜ).
      { iIntros "%HI #HΧ #HN #HΦ HR Hsim".
        iApply (HI with "Hsim HΧ HN HΦ HR").
      }
      iApply (sim_inner_ind with "[]"); first solve_proper. clear Φ1 eₛ eₜ. iIntros "!> %Φ1 %eₛ %eₜ Hsim #HΧ #HN #HΦ HR".
      iApply sim_inner_fixpoint.
      iApply (sim_body_monotone with "HΧ HN [] HΦ HR Hsim"). clear eₛ eₜ. iIntros "HR %eₛ %eₜ HI".
      iApply ("HI" with "HΧ HN HΦ HR").
    Qed.

    Lemma sim_inner_cupd_mono Χ1 Χ2 N1 N2 Φ eₛ eₜ :
      NonExpansive N2 →
      □ (Χ1 ++++∗ Χ2) -∗
      □ (N1 ++++∗ N2) -∗
      sim_inner Χ1 N1 Φ eₛ eₜ -∗
      sim_inner Χ2 N2 Φ eₛ eₜ.
    Proof.
      rewrite !definition.sim_inner_unseal.
      iIntros "%HN2 #HΧ #HN Hsim". rewrite /sim_inner /curry3.
      iApply (least_fixpoint_iter with "[] Hsim"). clear Φ eₛ eₜ. iIntros "!>" (((Φ & eₛ) & eₜ)) "Hsim".
      rewrite least_fixpoint_unfold /definition.sim_body' {1 3}/uncurry3.
      iApply (sim_body_cupd_mono with "[] [] [] Hsim"); [iSmash.. |]. iStep. auto.
    Qed.
    Lemma sim_inner_bupd_mono Χ1 Χ2 N1 N2 Φ eₛ eₜ :
      NonExpansive N2 →
      □ (Χ1 ====∗ Χ2) -∗
      □ (N1 ====∗ N2) -∗
      sim_inner Χ1 N1 Φ eₛ eₜ -∗
      sim_inner Χ2 N2 Φ eₛ eₜ.
    Proof.
      iIntros "%HN2 #HΧ #HN".
      iApply sim_inner_cupd_mono; iModIntro; iSmash.
    Qed.
    Lemma sim_inner_mono Χ1 Χ2 N1 N2 Φ eₛ eₜ :
      NonExpansive N2 →
      □ (Χ1 ---∗ Χ2) -∗
      □ (N1 ---∗ N2) -∗
      sim_inner Χ1 N1 Φ eₛ eₜ -∗
      sim_inner Χ2 N2 Φ eₛ eₜ.
    Proof.
      iIntros "%HN2 #HΧ #HN".
      iApply sim_inner_bupd_mono; iModIntro; iSmash.
    Qed.

    Lemma sim_inner_strong_cupd_mono Χ1 Χ2 N1 N2 Φ1 Φ2 eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      □ (Χ1 ++++∗ Χ2) -∗
      □ ((Φ1 +++∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      (Φ1 +++∗ Φ2) -∗
      sim_inner Χ1 N1 Φ1 eₛ eₜ -∗
      sim_inner Χ2 N2 Φ2 eₛ eₜ.
    Proof.
      iIntros "%HN1 %HN2 #HΧ #HN HΦ".
      iApply (sim_inner_monotone (λ Φ1 Φ2, Φ1 +++∗ Φ2)%I with "HΧ HN [] HΦ"); first solve_proper. iModIntro. iSmash.
    Qed.
    Lemma sim_inner_strong_bupd_mono Χ1 Χ2 N1 N2 Φ1 Φ2 eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      □ (Χ1 ====∗ Χ2) -∗
      □ ((Φ1 ===∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      (Φ1 ===∗ Φ2) -∗
      sim_inner Χ1 N1 Φ1 eₛ eₜ -∗
      sim_inner Χ2 N2 Φ2 eₛ eₜ.
    Proof.
      iIntros "%HN1 %HN2 #HΧ #HN HΦ".
      iApply (sim_inner_monotone (λ Φ1 Φ2, Φ1 ===∗ Φ2)%I with "[HΧ] HN [] HΦ"); first solve_proper; iModIntro; iSmash.
    Qed.
    Lemma sim_inner_strong_mono Χ1 Χ2 N1 N2 Φ1 Φ2 eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      □ (Χ1 ---∗ Χ2) -∗
      □ ((Φ1 --∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      (Φ1 --∗ Φ2) -∗
      sim_inner Χ1 N1 Φ1 eₛ eₜ -∗
      sim_inner Χ2 N2 Φ2 eₛ eₜ.
    Proof.
      iIntros "%HN1 %HN2 #HΧ #HN HΦ".
      iApply (sim_inner_monotone (λ Φ1 Φ2, Φ1 --∗ Φ2)%I with "[HΧ] HN [] HΦ"); first solve_proper; iModIntro; iSmash.
    Qed.

    Lemma sim_inner_cupd Χ N Φ eₛ eₜ :
      NonExpansive N →
      □ (N (λ eₛ eₜ, |++> Φ eₛ eₜ) +++∗ N Φ) ⊢
      sim_inner Χ N (λ eₛ eₜ, |++> Φ eₛ eₜ) eₛ eₜ -∗
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      iIntros "%HN #HN".
      iApply (sim_inner_strong_cupd_mono with "[HN]"); try iModIntro; iSmash.
    Qed.
    Lemma sim_inner_bupd Χ N Φ eₛ eₜ :
      NonExpansive N →
      □ (N (λ eₛ eₜ, |==> Φ eₛ eₜ) +++∗ N Φ) ⊢
      sim_inner Χ N (λ eₛ eₜ, |==> Φ eₛ eₜ) eₛ eₜ -∗
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      iIntros "%HN #HN".
      iApply (sim_inner_strong_bupd_mono with "[HN]"); try iModIntro; iSmash.
    Qed.

    Lemma sim_inner_frame_l Χ N R Φ eₛ eₜ :
      NonExpansive N →
      □ (
        ∀ eₛ eₜ,
        R ∗ N Φ eₛ eₜ ++∗
        N (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ
      ) -∗
      R ∗ sim_inner Χ N Φ eₛ eₜ -∗
      sim_inner Χ N (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ.
    Proof.
      iIntros "%HN #HN (HR & Hsim)".
      iApply (sim_inner_monotone (λ _ _, R) with "[] [HN] [] HR Hsim"); first (by solve_proper_prepare); iModIntro; iSmash.
    Qed.
    Lemma sim_inner_frame_r Χ N R Φ eₛ eₜ :
      NonExpansive N →
      □ (
        ∀ eₛ eₜ,
        N Φ eₛ eₜ ∗ R ++∗
        N (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ
      ) -∗
      sim_inner Χ N Φ eₛ eₜ ∗ R -∗
      sim_inner Χ N (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ.
    Proof.
      iIntros "%HN #HN (Hsim & HR)".
      iApply (sim_inner_monotone (λ _ _, R) with "[] [HN] [] HR Hsim"); first (by solve_proper_prepare); iModIntro; iSmash.
    Qed.

    Lemma sim_inner_bind' Χ N1 N2 Φ1 Φ2 Kₛ eₛ Kₜ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      sim_inner Χ N1 Φ1 eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 Φ1 eₛ' eₜ' -∗
        N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
      ) -∗
      ( ∀ eₛ' eₜ',
        Φ1 eₛ' eₜ' -∗
        sim_inner Χ N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
      ) -∗
      sim_inner Χ N2 Φ2 (Kₛ @@ eₛ) (Kₜ @@ eₜ).
    Proof.
      intros HN1 HN2.
      set I : sim_protocol_O := λ Φ1 eₛ eₜ, (
        ( ∀ eₛ' eₜ',
          N1 Φ1 eₛ' eₜ' -∗
          N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
        ) -∗
        ( ∀ eₛ' eₜ',
          Φ1 eₛ' eₜ' -∗
          sim_inner Χ N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
        ) -∗
        sim_inner Χ N2 Φ2 (Kₛ @@ eₛ) (Kₜ @@ eₜ)
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
    Lemma sim_inner_bind Χ N1 N2 Φ Kₛ eₛ Kₜ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      sim_inner Χ N1 (λ eₛ' eₜ', sim_inner Χ N2 Φ (Kₛ @@ eₛ') (Kₜ @@ eₜ')) eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 (λ eₛ' eₜ', sim_inner Χ N2 Φ (Kₛ @@ eₛ') (Kₜ @@ eₜ')) eₛ' eₜ' -∗
        N2 Φ (Kₛ @@ eₛ') (Kₜ @@ eₜ')
      ) -∗
      sim_inner Χ N2 Φ (Kₛ @@ eₛ) (Kₜ @@ eₜ).
    Proof.
      iIntros "%HN1 %HN2 Hsim HN".
      iApply (sim_inner_bind' with "Hsim HN"). iSmash.
    Qed.
    Lemma sim_inner_bindₛ' Χ N1 N2 Φ1 Φ2 K eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      sim_inner Χ N1 Φ1 eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 Φ1 eₛ' eₜ' -∗
        N2 Φ2 (K @@ eₛ') eₜ'
      ) -∗
      ( ∀ eₛ' eₜ',
        Φ1 eₛ' eₜ' -∗
        sim_inner Χ N2 Φ2 (K @@ eₛ') eₜ'
      ) -∗
      sim_inner Χ N2 Φ2 (K @@ eₛ) eₜ.
    Proof.
      iIntros "%HN1 %HN2 Hsim1 HN Hsim2".
      iEval (rewrite -(fill_empty eₜ)).
      iApply (sim_inner_bind' with "Hsim1 [HN] [Hsim2]"); iIntros "%eₛ' %eₜ'";
        rewrite fill_empty; iSmash.
    Qed.
    Lemma sim_inner_bindₛ Χ N1 N2 Φ K eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      sim_inner Χ N1 (λ eₛ' eₜ', sim_inner Χ N2 Φ (K @@ eₛ') eₜ') eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 (λ eₛ' eₜ', sim_inner Χ N2 Φ (K @@ eₛ') eₜ') eₛ' eₜ' -∗
        N2 Φ (K @@ eₛ') eₜ'
      ) -∗
      sim_inner Χ N2 Φ (K @@ eₛ) eₜ.
    Proof.
      iIntros "%HN1 %HN2 Hsim HN".
      iApply (sim_inner_bindₛ' with "Hsim HN"). iSmash.
    Qed.
    Lemma sim_inner_bindₜ' Χ N1 N2 eₛ K eₜ Φ1 Φ2 :
      NonExpansive N1 →
      NonExpansive N2 →
      sim_inner Χ N1 Φ1 eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 Φ1 eₛ' eₜ' -∗
        N2 Φ2 eₛ' (K @@ eₜ')
      ) -∗
      ( ∀ eₛ' eₜ',
        Φ1 eₛ' eₜ' -∗
        sim_inner Χ N2 Φ2 eₛ' (K @@ eₜ')
      ) -∗
      sim_inner Χ N2 Φ2 eₛ (K @@ eₜ).
    Proof.
      iIntros "%HN1 %HN2 Hsim1 HN Hsim2".
      iEval (rewrite -(fill_empty eₛ)).
      iApply (sim_inner_bind' with "Hsim1 [HN] [Hsim2]"); iIntros "%eₛ' %eₜ'";
        rewrite fill_empty; iSmash.
    Qed.
    Lemma sim_inner_bindₜ Χ N1 N2 Φ eₛ K eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      sim_inner Χ N1 (λ eₛ' eₜ', sim_inner Χ N2 Φ eₛ' (K @@ eₜ')) eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 (λ eₛ' eₜ', sim_inner Χ N2 Φ eₛ' (K @@ eₜ')) eₛ' eₜ' -∗
        N2 Φ eₛ' (K @@ eₜ')
      ) -∗
      sim_inner Χ N2 Φ eₛ (K @@ eₜ).
    Proof.
      iIntros "%HN1 %HN2 Hsim HN".
      iApply (sim_inner_bindₜ' with "Hsim HN"). iSmash.
    Qed.

    (* TODO: sim_inner_bind_inv *)
    (* TODO: sim_inner_bind_invₛ *)
    (* TODO: sim_inner_bind_invₜ *)

    (* TODO: sim_inner_decompose *)

    Lemma sim_inner_stepsₛ Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ∃ eₛ' σₛ',
          ⌜tc (step sim_progₛ) (eₛ, σₛ) (eₛ', σₛ')⌝ ∗
          sim_state_interp σₛ' σₜ ∗
          sim_inner Χ N Φ eₛ' eₜ
      ) ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_stepsₛ.
    Qed.
    Lemma sim_inner_stepₛ Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ∃ eₛ' σₛ',
          ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
          sim_state_interp σₛ' σₜ ∗
          sim_inner Χ N Φ eₛ' eₜ
      ) ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_stepₛ.
    Qed.
    Lemma sim_inner_head_stepₛ Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ∃ eₛ' σₛ',
          ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ∗
          sim_state_interp σₛ' σₜ ∗
          sim_inner Χ N Φ eₛ' eₜ
      ) ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_head_stepₛ.
    Qed.
    Lemma sim_inner_pure_stepsₛ Χ N Φ eₛ1 eₛ2 eₜ :
      NonExpansive N →
      rtc (pure_step sim_progₛ) eₛ1 eₛ2 →
      sim_inner Χ N Φ eₛ2 eₜ ⊢
      sim_inner Χ N Φ eₛ1 eₜ.
    Proof.
      intros HN [-> | Hstepsₛ]%rtc_tc; first done.
      setoid_rewrite sim_inner_fixpoint at 2; first apply sim_body_pure_stepsₛ; done.
    Qed.
    Lemma sim_inner_pure_stepₛ Χ N Φ eₛ1 eₛ2 eₜ :
      NonExpansive N →
      pure_step sim_progₛ eₛ1 eₛ2 →
      sim_inner Χ N Φ eₛ2 eₜ ⊢
      sim_inner Χ N Φ eₛ1 eₜ.
    Proof.
      intros HN.
      setoid_rewrite sim_inner_fixpoint at 2; [apply sim_body_pure_stepₛ | done].
    Qed.
    Lemma sim_inner_pure_head_stepsₛ Χ N Φ eₛ1 eₛ2 eₜ :
      NonExpansive N →
      rtc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
      sim_inner Χ N Φ eₛ2 eₜ ⊢
      sim_inner Χ N Φ eₛ1 eₜ.
    Proof.
      intros HN [-> | Hstepsₛ]%rtc_tc; first done.
      setoid_rewrite sim_inner_fixpoint at 2; first apply sim_body_pure_head_stepsₛ; done.
    Qed.
    Lemma sim_inner_pure_head_stepₛ Χ N Φ eₛ1 eₛ2 eₜ :
      NonExpansive N →
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      sim_inner Χ N Φ eₛ2 eₜ ⊢
      sim_inner Χ N Φ eₛ1 eₜ.
    Proof.
      intros HN.
      setoid_rewrite sim_inner_fixpoint at 2; [apply sim_body_pure_head_stepₛ | done].
    Qed.

    Lemma sim_inner_stepₜ Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              sim_inner Χ N Φ eₛ eₜ'
      ) ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_stepₜ.
    Qed.
    Lemma sim_inner_head_stepₜ Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              sim_inner Χ N Φ eₛ eₜ'
      ) ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_head_stepₜ.
    Qed.
    Lemma sim_inner_pure_stepₜ Χ N Φ eₛ eₜ1 eₜ2 :
      NonExpansive N →
      pure_step sim_progₜ eₜ1 eₜ2 →
      sim_inner Χ N Φ eₛ eₜ2 ⊢
      sim_inner Χ N Φ eₛ eₜ1.
    Proof.
      intros HN.
      setoid_rewrite sim_inner_fixpoint at 2; [apply sim_body_pure_stepₜ | done].
    Qed.
    Lemma sim_inner_pure_stepsₜ Χ N Φ eₛ eₜ1 eₜ2 :
      NonExpansive N →
      rtc (pure_step sim_progₜ) eₜ1 eₜ2 →
      sim_inner Χ N Φ eₛ eₜ2 ⊢
      sim_inner Χ N Φ eₛ eₜ1.
    Proof.
      intros HN.
      induction 1 as [| eₜ eₜ' eₜ'' Hstepₜ Hstepsₜ IH]; first done.
      rewrite IH. apply sim_inner_pure_stepₜ; done.
    Qed.
    Lemma sim_inner_pure_head_stepₜ Χ N Φ eₛ eₜ1 eₜ2 :
      NonExpansive N →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      sim_inner Χ N Φ eₛ eₜ2 ⊢
      sim_inner Χ N Φ eₛ eₜ1.
    Proof.
      intros HN.
      setoid_rewrite sim_inner_fixpoint at 2; [apply sim_body_pure_head_stepₜ | done].
    Qed.
    Lemma sim_inner_pure_head_stepsₜ Χ N Φ eₛ eₜ1 eₜ2 :
      NonExpansive N →
      rtc (pure_head_step sim_progₜ) eₜ1 eₜ2 →
      sim_inner Χ N Φ eₛ eₜ2 ⊢
      sim_inner Χ N Φ eₛ eₜ1.
    Proof.
      intros HN.
      induction 1 as [| eₜ eₜ' eₜ'' Hstepₜ Hstepsₜ IH]; first done.
      rewrite IH. apply sim_inner_pure_head_stepₜ; done.
    Qed.

    Lemma sim_inner_steps Χ N Φ eₛ eₜ :
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
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_steps.
    Qed.
    Lemma sim_inner_step Χ N Φ eₛ eₜ :
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
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_step.
    Qed.
    Lemma sim_inner_head_step Χ N Φ eₛ eₜ :
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
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_head_step.
    Qed.
    Lemma sim_inner_pure_steps Χ N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      NonExpansive N →
      tc (pure_step sim_progₛ) eₛ1 eₛ2 →
      pure_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      sim_inner Χ N Φ eₛ1 eₜ1.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_pure_steps.
    Qed.
    Lemma sim_inner_pure_step Χ N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      NonExpansive N →
      pure_step sim_progₛ eₛ1 eₛ2 →
      pure_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      sim_inner Χ N Φ eₛ1 eₜ1.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_pure_step.
    Qed.
    Lemma sim_inner_pure_head_steps Χ N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      NonExpansive N →
      tc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      sim_inner Χ N Φ eₛ1 eₜ1.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_pure_head_steps.
    Qed.
    Lemma sim_inner_pure_head_step Χ N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      NonExpansive N →
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      sim_inner Χ N Φ eₛ1 eₜ1.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_pure_head_step.
    Qed.

    Lemma sim_inner_apply_protocol Ψ Kₛ eₛ' Kₜ eₜ' Χ N Φ eₛ eₜ :
      NonExpansive N →
      eₛ = Kₛ @@ eₛ' →
      eₜ = Kₜ @@ eₜ' →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          Χ Ψ eₛ' eₜ' ∗
          sim_state_interp σₛ σₜ ∗
            ∀ eₛ eₜ,
            Ψ eₛ eₜ ++∗
            sim_inner Χ N Φ (Kₛ @@ eₛ) (Kₜ @@ eₜ)

      ) ⊢
      sim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite sim_inner_fixpoint. apply sim_body_apply_protocol.
    Qed.
  End sim_inner.

  Section sim.
    #[local] Instance sim_inner'_ne Χ n :
      Proper (
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) (definition.sim_inner' Χ).
    Proof.
      intros N1 N2 HN ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
      simpl in HΦ, Heₛ, Heₜ. subst.
      apply sim_inner_ne; done || solve_proper.
    Qed.
    #[local] Instance sim_inner'_proper Χ :
      Proper (
        ((≡) ==> (≡)) ==>
        (≡) ==>
        (≡)
      ) (definition.sim_inner' Χ).
    Proof.
      intros N1 N2 HN ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
      simpl in HΦ, Heₛ, Heₜ. subst.
      apply sim_inner_proper; done || solve_proper.
    Qed.
    #[local] Instance sim_inner'_mono_pred Χ :
      BiMonoPred (definition.sim_inner' Χ).
    Proof.
      split.
      - iIntros "%N1 %N2 %HN1 %HN2 #HN" (((Φ & eₛ) & eₜ)) "Hsim".
        iApply (sim_inner_mono with "[] [] Hsim"); first solve_proper; iModIntro; iSmash.
      - intros N HN n ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
        rewrite /definition.sim_inner' /=.
        apply sim_inner_ne; solve_proper.
    Qed.

    #[global] Instance sim_ne Χ n :
      Proper ((≡{n}≡) ==> (=) ==> (=) ==> (≡{n}≡)) (sim Χ).
    Proof.
      rewrite definition.sim_unseal.
      solve_proper.
    Qed.
    #[global] Instance sim_proper Χ :
      Proper ((≡) ==> (=) ==> (=) ==> (≡)) (sim Χ).
    Proof.
      rewrite definition.sim_unseal.
      solve_proper.
    Qed.

    Lemma sim_fixpoint Χ Φ eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ⊣⊢
      sim_inner Χ (sim Χ) Φ eₛ eₜ.
    Proof.
      rewrite definition.sim_unseal.
      setoid_rewrite greatest_fixpoint_unfold; [done | apply _].
    Qed.
    Lemma sim_unfold Χ Φ eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
      sim_inner Χ (sim Χ) Φ eₛ eₜ.
    Proof.
      rewrite sim_fixpoint //.
    Qed.
    Lemma sim_fold Χ Φ eₛ eₜ :
      sim_inner Χ (sim Χ) Φ eₛ eₜ ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite sim_fixpoint //.
    Qed.

    Lemma sim_eq Χ Φ eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ⊣⊢
      sim_body Χ (sim Χ) (sim Χ) Φ eₛ eₜ.
    Proof.
      rewrite sim_fixpoint.
      setoid_rewrite sim_inner_fixpoint; last solve_proper.
      rewrite /sim_body. setoid_rewrite <- sim_fixpoint. done.
    Qed.

    Lemma sim_strong_coind Χ I Φ eₛ eₜ :
      NonExpansive I →
      □ (I ---∗ sim_inner Χ (λ Φ eₛ eₜ, I Φ eₛ eₜ ∨ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }})) ⊢
      I Φ eₛ eₜ -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite definition.sim_unseal.
      iIntros "%HI #Hind HI".
      replace (I Φ eₛ eₜ) with ((uncurry3 I) (Φ, eₛ, eₜ)); last done.
      iApply (greatest_fixpoint_coind with "[] HI"). clear Φ eₛ eₜ. iIntros "!>" (((Φ & eₛ) & eₜ)) "HI /=".
      iSmash.
    Qed.
    Lemma sim_coind Χ I Φ eₛ eₜ :
      NonExpansive I →
      □ (I ---∗ sim_inner Χ I) ⊢
      I Φ eₛ eₜ -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "%HI #Hind".
      iApply sim_strong_coind. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ HI".
      iApply (sim_inner_mono with "[] [] (Hind HI)"); first solve_proper; iModIntro; iSmash.
    Qed.

    Lemma sim_strongly_stuck Χ Φ eₛ eₜ :
      strongly_stuck sim_progₛ eₛ →
      strongly_stuck sim_progₜ eₜ →
      ⊢ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite sim_fixpoint. apply sim_inner_strongly_stuck. solve_proper.
    Qed.
    Lemma sim_strongly_head_stuck Χ Φ eₛ eₜ :
      strongly_head_stuck sim_progₛ eₛ →
      strongly_head_stuck sim_progₜ eₜ →
      ⊢ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite sim_fixpoint. apply sim_inner_strongly_head_stuck. solve_proper.
    Qed.

    Lemma sim_post Χ Φ eₛ eₜ :
      Φ eₛ eₜ ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite sim_fixpoint. apply sim_inner_post. solve_proper.
    Qed.

    Lemma cupd_sim Χ Φ eₛ eₜ :
      (|++> SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite sim_fixpoint. apply cupd_sim_inner. solve_proper.
    Qed.
    Lemma bupd_sim Χ Φ eₛ eₜ :
      (|==> SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite sim_fixpoint. apply bupd_sim_inner. solve_proper.
    Qed.

    Lemma sim_strong_cupd_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ++++∗ Χ2) -∗
      (Φ1 +++∗ Φ2) -∗
      SIM eₛ ≳ eₜ [[ Χ1 ]] {{ Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ2 ]] {{ Φ2 }}.
    Proof.
      set I : sim_protocol_O := λ Φ2 eₛ eₜ, (
        ∃ Φ1,
        □ (Χ1 ++++∗ Χ2) ∗
        (Φ1 +++∗ Φ2) ∗
        SIM eₛ ≳ eₜ [[ Χ1 ]] {{ Φ1 }}
      )%I.
      assert (NonExpansive I) by solve_proper.
      cut (I Φ2 eₛ eₜ -∗ SIM eₛ ≳ eₜ [[ Χ2 ]] {{ Φ2 }}).
      { iIntros "%HI #HΧ HΦ Hsim1".
        iApply HI. iExists Φ1. iFrame "#∗".
      }
      iApply (sim_coind with "[]"). clear Φ1 Φ2 eₛ eₜ. iIntros "!> %Φ2 %eₛ %eₜ (%Φ1 & #HΧ & HΦ & Hsim1)".
      rewrite sim_fixpoint.
      iApply (sim_inner_strong_cupd_mono with "HΧ [] HΦ Hsim1"); first solve_proper. clear eₛ eₜ. iIntros "!> HΦ %eₛ %eₜ Hsim1".
      iExists Φ1. iFrame "#∗". iSmash.
    Qed.
    Lemma sim_strong_bupd_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ====∗ Χ2) -∗
      (Φ1 ===∗ Φ2) -∗
      SIM eₛ ≳ eₜ [[ Χ1 ]] {{ Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ2 ]] {{ Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hsim1".
      iApply (sim_strong_cupd_mono with "[] [HΦ] Hsim1"); first iModIntro; iSmash.
    Qed.
    Lemma sim_strong_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ---∗ Χ2) -∗
      (Φ1 --∗ Φ2) -∗
      SIM eₛ ≳ eₜ [[ Χ1 ]] {{ Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ2 ]] {{ Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hsim1".
      iApply (sim_strong_bupd_mono with "[] [HΦ] Hsim1"); first iModIntro; iSmash.
    Qed.

    Lemma sim_cupd_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 +++∗ Φ2) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      iIntros "HΦ Hsim1".
      iApply (sim_strong_cupd_mono with "[] HΦ Hsim1"). iModIntro. iSmash.
    Qed.
    Lemma sim_bupd_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 ===∗ Φ2) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      rewrite -sim_cupd_mono. iSmash.
    Qed.
    Lemma sim_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 --∗ Φ2) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      rewrite -sim_bupd_mono. iSmash.
    Qed.
    Lemma sim_mono' Χ Φ1 Φ2 eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }} ⊢
      (Φ1 --∗ Φ2) -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      rewrite sim_mono. iSmash.
    Qed.

    Lemma sim_cupd Χ Φ eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }} ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iApply (sim_cupd_mono with "[]"). iSmash.
    Qed.
    Lemma sim_bupd Χ Φ eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }} ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iApply (sim_bupd_mono with "[]"). iSmash.
    Qed.

    Lemma sim_frame_l Χ R Φ eₛ eₜ :
      R ∗ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, R ∗ Φ eₛ eₜ }}.
    Proof.
      iIntros "(HR & Hsim)".
      iApply (sim_mono with "[HR] Hsim"). iSmash.
    Qed.
    Lemma sim_frame_r Χ R Φ eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ∗ R ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, Φ eₛ eₜ ∗ R }}.
    Proof.
      iIntros "(Hsim & HR)".
      iApply (sim_mono with "[HR] Hsim"). iSmash.
    Qed.

    Lemma sim_bind Χ Φ Kₛ eₛ Kₜ eₜ :
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
        rewrite sim_fixpoint. iApply (sim_inner_mono with "[] [] Hsim"); first auto. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ Hsim".
        iExists ∅, eₛ, ∅, eₜ. iSplit; first rewrite !fill_empty //.
        iApply sim_post. rewrite !fill_empty //.
    Qed.
    Lemma sim_bind' Χ Φ1 Φ2 Kₛ eₛ Kₜ eₜ :
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
    Lemma sim_bindₛ Χ Φ K eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        SIM K @@ eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}
      }} ⊢
      SIM K @@ eₛ ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite -{2}(fill_empty eₜ) -(sim_bind ∅).
      iApply (sim_mono with "[]").
      setoid_rewrite fill_empty. iSmash.
    Qed.
    Lemma sim_bindₜ Χ Φ eₛ K eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        SIM eₛ' ≳ K @@ eₜ' [[ Χ ]] {{ Φ }}
      }} ⊢
      SIM eₛ ≳ K @@ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite -{2}(fill_empty eₛ) -(sim_bind ∅).
      iApply (sim_mono with "[]").
      setoid_rewrite fill_empty. iSmash.
    Qed.

    Lemma sim_bind_inv Χ Φ Kₛ eₛ Kₜ eₜ :
      SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        SIM Kₛ @@ eₛ' ≳ Kₜ @@ eₜ' [[ Χ ]] {{ Φ }}
      }}.
    Proof.
      iIntros "Hsim". iApply sim_post. iSmash.
    Qed.
    Lemma sim_bind_invₛ Χ Φ K eₛ eₜ :
      SIM K @@ eₛ ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        SIM K @@ eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}
      }}.
    Proof.
      iIntros "Hsim". iApply sim_post. iSmash.
    Qed.
    Lemma sim_bind_invₜ Χ Φ eₛ K eₜ :
      SIM eₛ ≳ K @@ eₜ [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        SIM eₛ' ≳ K @@ eₜ' [[ Χ ]] {{ Φ }}
      }}.
    Proof.
      iIntros "Hsim". iApply sim_post. iSmash.
    Qed.

    Lemma sim_decompose Χ Φ1 Φ2 eₛ eₜ :
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

    Lemma sim_stepsₛ Χ Φ eₛ eₜ :
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
    Lemma sim_stepₛ Χ Φ eₛ eₜ :
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
    Lemma sim_head_stepₛ Χ Φ eₛ eₜ :
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
    Lemma sim_pure_stepsₛ Χ Φ eₛ1 eₛ2 eₜ :
      rtc (pure_step sim_progₛ) eₛ1 eₛ2 →
      SIM eₛ2 ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ1 ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !sim_fixpoint. apply sim_inner_pure_stepsₛ. solve_proper.
    Qed.
    Lemma sim_pure_stepₛ Χ Φ eₛ1 eₛ2 eₜ :
      pure_step sim_progₛ eₛ1 eₛ2 →
      SIM eₛ2 ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ1 ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !sim_fixpoint. apply sim_inner_pure_stepₛ. solve_proper.
    Qed.
    Lemma sim_pure_head_stepsₛ Χ Φ eₛ1 eₛ2 eₜ :
      rtc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
      SIM eₛ2 ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ1 ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !sim_fixpoint. apply sim_inner_pure_head_stepsₛ. solve_proper.
    Qed.
    Lemma sim_pure_head_stepₛ Χ Φ eₛ1 eₛ2 eₜ :
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      SIM eₛ2 ≳ eₜ [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ1 ≳ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !sim_fixpoint. apply sim_inner_pure_head_stepₛ. solve_proper.
    Qed.

    Lemma sim_stepₜ Χ Φ eₛ eₜ :
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
    Lemma sim_head_stepₜ Χ Φ eₛ eₜ :
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
    Lemma sim_pure_stepsₜ Χ Φ eₛ eₜ1 eₜ2 :
      rtc (pure_step sim_progₜ) eₜ1 eₜ2 →
      SIM eₛ ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ ≳ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !sim_fixpoint. apply sim_inner_pure_stepsₜ. solve_proper.
    Qed.
    Lemma sim_pure_stepₜ Χ Φ eₛ eₜ1 eₜ2 :
      pure_step sim_progₜ eₜ1 eₜ2 →
      SIM eₛ ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ ≳ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !sim_fixpoint. apply sim_inner_pure_stepₜ. solve_proper.
    Qed.
    Lemma sim_pure_head_stepsₜ Χ Φ eₛ eₜ1 eₜ2 :
      rtc (pure_head_step sim_progₜ) eₜ1 eₜ2 →
      SIM eₛ ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ ≳ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !sim_fixpoint. apply sim_inner_pure_head_stepsₜ. solve_proper.
    Qed.
    Lemma sim_pure_head_stepₜ Χ Φ eₛ eₜ1 eₜ2 :
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      SIM eₛ ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ ≳ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !sim_fixpoint. apply sim_inner_pure_head_stepₜ. solve_proper.
    Qed.

    Lemma sim_steps Χ Φ eₛ eₜ :
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
    Lemma sim_step Χ Φ eₛ eₜ :
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
    Lemma sim_head_step Χ Φ eₛ eₜ :
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
    Lemma sim_pure_steps Χ Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      rtc (pure_step sim_progₛ) eₛ1 eₛ2 →
      rtc (pure_step sim_progₜ) eₜ1 eₜ2 →
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      intros. rewrite sim_pure_stepsₛ // sim_pure_stepsₜ //.
    Qed.
    Lemma sim_pure_step Χ Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      pure_step sim_progₛ eₛ1 eₛ2 →
      pure_step sim_progₜ eₜ1 eₜ2 →
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      intros. rewrite sim_pure_stepₛ // sim_pure_stepₜ //.
    Qed.
    Lemma sim_pure_head_steps Χ Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      rtc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
      rtc (pure_head_step sim_progₜ) eₜ1 eₜ2 →
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      intros. rewrite sim_pure_head_stepsₛ // sim_pure_head_stepsₜ //.
    Qed.
    Lemma sim_pure_head_step Χ Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      SIM eₛ2 ≳ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      SIM eₛ1 ≳ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      intros. rewrite sim_pure_head_stepₛ // sim_pure_head_stepₜ //.
    Qed.

    Lemma sim_apply_protocol Ψ Χ Φ eₛ eₜ :
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
    Lemma simv_post Χ Φ vₛ vₜ eₛ eₜ :
      eₛ = of_val vₛ →
      eₜ = of_val vₜ →
      Φ vₛ vₜ ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite simv_unseal -sim_post. iSmash.
    Qed.

    Lemma simv_strong_cupd_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ++++∗ Χ2) -∗
      (Φ1 +++∗ Φ2) -∗
      SIM eₛ ≳ eₜ [[ Χ1 ]] {{# Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ2 ]] {{# Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hsim1".
      iApply (sim_strong_cupd_mono with "HΧ [HΦ] Hsim1"). clear eₛ eₜ. iIntros "%eₛ %eₜ".
      iApply (sim_post_vals_cupd_mono with "HΦ").
    Qed.
    Lemma simv_strong_bupd_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ====∗ Χ2) -∗
      (Φ1 ===∗ Φ2) -∗
      SIM eₛ ≳ eₜ [[ Χ1 ]] {{# Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ2 ]] {{# Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hsim1".
      iApply (simv_strong_cupd_mono with "[] [HΦ] Hsim1"); first iModIntro; iSmash.
    Qed.
    Lemma simv_strong_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ---∗ Χ2) -∗
      (Φ1 --∗ Φ2) -∗
      SIM eₛ ≳ eₜ [[ Χ1 ]] {{# Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ2 ]] {{# Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hsim1".
      iApply (simv_strong_bupd_mono with "[] [HΦ] Hsim1"); first iModIntro; iSmash.
    Qed.

    Lemma simv_cupd_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 +++∗ Φ2) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      rewrite -sim_cupd_mono. setoid_rewrite <- sim_post_vals_cupd_mono. iSmash.
    Qed.
    Lemma simv_bupd_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 ===∗ Φ2) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      rewrite -sim_bupd_mono. setoid_rewrite <- sim_post_vals_bupd_mono. iSmash.
    Qed.
    Lemma simv_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 --∗ Φ2) ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ1 }} -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      rewrite -sim_mono. setoid_rewrite <- sim_post_vals_mono. iSmash.
    Qed.
    Lemma simv_mono' Χ Φ1 Φ2 eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ1 }} ⊢
      (Φ1 --∗ Φ2) -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      rewrite simv_mono. iSmash.
    Qed.

    Lemma simv_cupd Χ Φ eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, |++> Φ eₛ eₜ }} ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      apply bi.wand_entails. rewrite -simv_cupd_mono. iSmash.
    Qed.
    Lemma simv_bupd Χ Φ eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, |==> Φ eₛ eₜ }} ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      apply bi.wand_entails. rewrite -simv_bupd_mono. iSmash.
    Qed.

    Lemma simv_frame_l Χ R Φ eₛ eₜ :
      R ∗ SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }} ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, R ∗ Φ eₛ eₜ }}.
    Proof.
      rewrite simv_mono'. iSmash.
    Qed.
    Lemma simv_frame_r Χ R Φ eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }} ∗ R ⊢
      SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, Φ eₛ eₜ ∗ R }}.
    Proof.
      rewrite simv_mono'. iSmash.
    Qed.

    Lemma simv_bind Χ Φ Kₛ eₛ Kₜ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# λ vₛ vₜ,
        SIM Kₛ @@ of_val vₛ ≳ Kₜ @@ of_val vₜ [[ Χ ]] {{# Φ }}
      }} ⊢
      SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal -sim_bind sim_mono'. iSmash.
    Qed.
    Lemma simv_bindₛ Χ Φ K eₛ eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# λ vₛ vₜ,
        SIM K @@ of_val vₛ ≳ of_val vₜ [[ Χ ]] {{# Φ }}
      }} ⊢
      SIM K @@ eₛ ≳ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal -sim_bindₛ sim_mono'. iSmash.
    Qed.
    Lemma simv_bindₜ Χ Φ eₛ K eₜ :
      SIM eₛ ≳ eₜ [[ Χ ]] {{# λ vₛ vₜ,
        SIM of_val vₛ ≳ K @@ of_val vₜ [[ Χ ]] {{# Φ }}
      }} ⊢
      SIM eₛ ≳ K @@ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !simv_unseal -sim_bindₜ sim_mono'. iSmash.
    Qed.
  End simv.

  Lemma sim_close Χ Φ eₛ eₜ :
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
    iApply cupd_sim. rewrite sim_fixpoint.
    iApply (sim_inner_mono with "[] [] (Hsim HΨ)"); first solve_proper; iModIntro; iSmash.
  Qed.
  Lemma sim_close_steps Χ Φ eₛ eₜ :
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
  Lemma sim_close_step Χ Φ eₛ eₜ :
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
    iApply sim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iApply sim_inner_step. iIntros "%σₛ %σₜ".
    iApply ("H" with "HΧ").
  Qed.
  Lemma sim_close_head_step Χ Φ eₛ eₜ :
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
    iApply sim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iApply sim_inner_head_step. iIntros "%σₛ %σₜ".
    iApply ("H" with "HΧ").
  Qed.
  Lemma sim_close_pure_steps Χ Φ eₛ eₜ :
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
    iApply sim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepsₛ & %Hstepsₜ) & Hsim)".
    iApply sim_inner_pure_steps; done.
  Qed.
  Lemma sim_close_pure_step Χ Φ eₛ eₜ :
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
    iApply sim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepₛ & %Hstepₜ) & Hsim)".
    iApply sim_inner_pure_step; done.
  Qed.
  Lemma sim_close_pure_head_steps Χ Φ eₛ eₜ :
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
    iApply sim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepsₛ & %Hstepsₜ) & Hsim)".
    iApply sim_inner_pure_head_steps; done.
  Qed.
  Lemma sim_close_pure_head_step Χ Φ eₛ eₜ :
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
    iApply sim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepₛ & %Hstepₜ) & Hsim)".
    iApply sim_inner_pure_head_step; done.
  Qed.
End sim_state.
