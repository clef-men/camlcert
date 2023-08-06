From iris.bi Require Import
  fixpoint.

From simuliris Require Import
  prelude.
From simuliris.base_logic Require Import
  lib.cupd.proofmode.
From simuliris.program_logic Require Export
  (* FIXME: remove this dependency *)
  sim.rules
  bisim.definition.
From simuliris.program_logic Require Import
  bisim.notations.

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

Section sim_state.
  Context `{sim_programs : !SimPrograms Λₛ Λₜ}.
  Context `{!BiBUpd PROP, !BiAffine PROP}.
  Context `{sim_state : !SimState PROP Λₛ Λₜ}.

  Notation sim_protocol := (sim_protocol PROP Λₛ Λₜ).
  Notation sim_protocol_O := (sim_protocol_O PROP Λₛ Λₜ).
  Implicit Types Χ : sim_protocol.
  Implicit Types N M I : sim_protocol_O.

  Section bisim_body.
    #[global] Instance bisim_body_ne Χ n :
      Proper (
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) (bisim_body Χ).
    Proof.
      intros N1 N2 HN M1 M2 HM Φ1 Φ2 HΦ eₛ1 eₛ2 ->%leibniz_equiv eₜ1 eₜ2 ->%leibniz_equiv.
      solve_proper_core ltac:(fun _ => f_equiv || apply HΧ || apply HN || apply HM || apply HΦ).
    Qed.
    #[global] Instance bisim_body_proper Χ :
      Proper (
        ((≡) ==> (≡)) ==>
        ((≡) ==> (≡)) ==>
        (≡) ==>
        (≡) ==>
        (≡) ==>
        (≡)
      ) (bisim_body Χ).
    Proof.
      intros N1 N2 HN M1 M2 HM Φ1 Φ2 HΦ eₛ1 eₛ2 ->%leibniz_equiv eₜ1 eₜ2 ->%leibniz_equiv.
      rewrite /bisim_body. repeat (f_equiv || apply HΧ || apply HN || apply HM || apply HΦ).
    Qed.

    Lemma bisim_body_strongly_stuck Χ N M Φ eₛ eₜ :
      strongly_stuck sim_progₛ eₛ →
      strongly_stuck sim_progₜ eₜ →
      ⊢ bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "%Hstrongly_stuckₛ %Hstrong_stuckₜ %σₛ %σₜ Hsi !>".
      iLeft. iFrame. auto using strongly_stuck_stuck.
    Qed.
    Lemma bisim_body_strongly_head_stuck Χ N M Φ eₛ eₜ :
      strongly_head_stuck sim_progₛ eₛ →
      strongly_head_stuck sim_progₜ eₜ →
      ⊢ bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      intros.
      apply bisim_body_strongly_stuck; apply strongly_head_stuck_strongly_stuck; done.
    Qed.

    Lemma bisim_body_post Χ N M Φ eₛ eₜ :
      Φ eₛ eₜ ⊢
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iSmash.
    Qed.

    Lemma cupd_bisim_body Χ N M Φ eₛ eₜ :
      (|++> bisim_body Χ N M Φ eₛ eₜ) ⊢
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "Hbisim %σₛ %σₜ Hsi".
      rewrite sim_cupd_eq. iMod ("Hbisim" with "Hsi") as "(Hsi & Hbisim)".
      iApply ("Hbisim" with "Hsi").
    Qed.
    Lemma bupd_bisim_body Χ N M Φ eₛ eₜ :
      (|==> bisim_body Χ N M Φ eₛ eₜ) ⊢
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "Hbisim".
      iApply cupd_bisim_body.
      iMod "Hbisim" as "$". iSmash.
    Qed.

    Lemma bisim_body_monotone R Χ1 Χ2 N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
      (Χ1 ++++∗ Χ2) -∗
      (R Φ1 Φ2 -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      (R Φ1 Φ2 -∗ M1 Φ1 +++∗ M2 Φ2) -∗
      (R Φ1 Φ2 -∗ Φ1 +++∗ Φ2) -∗
      R Φ1 Φ2 -∗
      bisim_body Χ1 N1 M1 Φ1 eₛ eₜ -∗
      bisim_body Χ2 N2 M2 Φ2 eₛ eₜ.
    Proof.
      setoid_rewrite sim_cupd_eq.
      iIntros "HΧ HN HM HΦ HR Hbisim %σₛ %σₜ Hsi".
      iMod ("Hbisim" with "Hsi") as "[Hbisim | [Hbisim | [Hbisim | [Hbisim | Hbisim]]]]".
      - iDestruct "Hbisim" as "(Hsi & [(%Hstuckₛ & %Hstuckₜ) | HΦ1])"; iLeft.
        + iSmash.
        + iMod ("HΦ" with "HR HΦ1 Hsi") as "(Hsi & HΦ2)". iSmash.
      - iDestruct "Hbisim" as "(%Hreducibleₛ & Hbisim)".
        iRight. iLeft. iSplitR; first iSmash. iIntros "!> %eₛ' %σₛ' %Hstepₛ".
        iDestruct ("Hbisim" with "[//]") as "> (Hsi & HM1)".
        iApply ("HM" with "HR HM1 Hsi").
      - iDestruct "Hbisim" as "(%Hreducibleₜ & Hbisim)".
        do 2 iRight. iLeft. iSplitR; first iSmash. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
        iDestruct ("Hbisim" with "[//]") as "> (Hsi & HM1)".
        iApply ("HM" with "HR HM1 Hsi").
      - iDestruct "Hbisim" as "((%Hreducibleₛ & %Hreducibleₜ) & Hbisim)".
        do 3 iRight. iLeft. iSplitR; first iSmash. iIntros "!> %eₛ' %σₛ' %eₜ' %σₜ' (%Hstepₛ & %Hstepₜ)".
        iMod ("Hbisim" with "[//]") as "(Hsi & HN1)".
        iApply ("HN" with "HR HN1 Hsi").
      - iDestruct "Hbisim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & HΧ1 & Hsi & HM1)".
        iMod ("HΧ" with "HΧ1 Hsi") as "(Hsi & HΧ2)".
        do 4 iRight. iExists Kₛ, eₛ', Kₜ, eₜ', Ψ. iFrame. iSplitR; first iSmash. iIntros "!> %eₛ %eₜ HΨ".
        iMod ("HM1" with "HΨ") as "HM1".
        iApply ("HM" with "HR HM1").
    Qed.

    Lemma bisim_body_cupd_mono Χ1 Χ2 N1 N2 M1 M2 Φ eₛ eₜ :
      (Χ1 ++++∗ Χ2) -∗
      (N1 ++++∗ N2) -∗
      (M1 ++++∗ M2) -∗
      bisim_body Χ1 N1 M1 Φ eₛ eₜ -∗
      bisim_body Χ2 N2 M2 Φ eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM".
      iApply (bisim_body_monotone (λ _ _, True)%I with "HΧ [HN] [HM] [] [//]"); iSmash.
    Qed.
    Lemma bisim_body_bupd_mono Χ1 Χ2 N1 N2 M1 M2 Φ eₛ eₜ :
      (Χ1 ====∗ Χ2) -∗
      (N1 ====∗ N2) -∗
      (M1 ====∗ M2) -∗
      bisim_body Χ1 N1 M1 Φ eₛ eₜ -∗
      bisim_body Χ2 N2 M2 Φ eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM".
      iApply (bisim_body_cupd_mono with "[HΧ] [HN] [HM]"); iSmash.
    Qed.
    Lemma bisim_body_mono Χ1 Χ2 N1 N2 M1 M2 Φ eₛ eₜ :
      (Χ1 ---∗ Χ2) -∗
      (N1 ---∗ N2) -∗
      (M1 ---∗ M2) -∗
      bisim_body Χ1 N1 M1 Φ eₛ eₜ -∗
      bisim_body Χ2 N2 M2 Φ eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM".
      iApply (bisim_body_bupd_mono with "[HΧ] [HN] [HM]"); iSmash.
    Qed.

    Lemma bisim_body_strong_cupd_mono Χ1 Χ2 N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
      (Χ1 ++++∗ Χ2) -∗
      ((Φ1 +++∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      ((Φ1 +++∗ Φ2) -∗ M1 Φ1 +++∗ M2 Φ2) -∗
      (Φ1 +++∗ Φ2) -∗
      bisim_body Χ1 N1 M1 Φ1 eₛ eₜ -∗
      bisim_body Χ2 N2 M2 Φ2 eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM HΦ".
      iApply (bisim_body_monotone (λ Φ1 Φ2, Φ1 +++∗ Φ2)%I with "HΧ [HN] [HM] [] HΦ"); iSmash+.
    Qed.
    Lemma bisim_body_strong_bupd_mono Χ1 Χ2 N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
      (Χ1 ====∗ Χ2) -∗
      ((Φ1 ===∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      ((Φ1 ===∗ Φ2) -∗ M1 Φ1 +++∗ M2 Φ2) -∗
      (Φ1 ===∗ Φ2) -∗
      bisim_body Χ1 N1 M1 Φ1 eₛ eₜ -∗
      bisim_body Χ2 N2 M2 Φ2 eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM HΦ".
      iApply (bisim_body_monotone (λ Φ1 Φ2, Φ1 ===∗ Φ2)%I with "[HΧ] [HN] [HM] [] HΦ"); iSmash+.
    Qed.
    Lemma bisim_body_strong_mono Χ1 Χ2 N1 N2 M1 M2 Φ1 Φ2 eₛ eₜ :
      (Χ1 ---∗ Χ2) -∗
      ((Φ1 --∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      ((Φ1 --∗ Φ2) -∗ M1 Φ1 +++∗ M2 Φ2) -∗
      (Φ1 --∗ Φ2) -∗
      bisim_body Χ1 N1 M1 Φ1 eₛ eₜ -∗
      bisim_body Χ2 N2 M2 Φ2 eₛ eₜ.
    Proof.
      iIntros "HΧ HN HM HΦ".
      iApply (bisim_body_monotone (λ Φ1 Φ2, Φ1 --∗ Φ2)%I with "[HΧ] [HN] [HM] [] HΦ"); iSmash+.
    Qed.

    Lemma bisim_body_cupd Χ N M Φ eₛ eₜ :
      (N (λ eₛ eₜ, |++> Φ eₛ eₜ) +++∗ N Φ) -∗
      (M (λ eₛ eₜ, |++> Φ eₛ eₜ) +++∗ M Φ) -∗
      bisim_body Χ N M (λ eₛ eₜ, |++> Φ eₛ eₜ) eₛ eₜ -∗
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HN HM".
      iApply (bisim_body_strong_cupd_mono with "[] [HN] [HM]"); iSmash.
    Qed.
    Lemma bisim_body_bupd Χ N M Φ eₛ eₜ :
      (N (λ eₛ eₜ, |==> Φ eₛ eₜ) +++∗ N Φ) -∗
      (M (λ eₛ eₜ, |==> Φ eₛ eₜ) +++∗ M Φ) -∗
      bisim_body Χ N M (λ eₛ eₜ, |==> Φ eₛ eₜ) eₛ eₜ -∗
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HN HM".
      iApply (bisim_body_strong_bupd_mono with "[] [HN] [HM]"); iSmash.
    Qed.

    Lemma bisim_body_frame_l Χ N M R Φ eₛ eₜ :
      ( ∀ eₛ eₜ,
        R ∗ N Φ eₛ eₜ ++∗
        N (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ
      ) -∗
      ( ∀ eₛ eₜ,
        R ∗ M Φ eₛ eₜ ++∗
        M (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ
      ) -∗
      R ∗ bisim_body Χ N M Φ eₛ eₜ -∗
      bisim_body Χ N M (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ.
    Proof.
      iIntros "HN HM (HR & Hbisim)".
      iApply (bisim_body_monotone (λ _ _, R) with "[] [HN] [HM] [] HR Hbisim"); iSmash.
    Qed.
    Lemma bisim_body_frame_r Χ N M R Φ eₛ eₜ :
      ( ∀ eₛ eₜ,
        N Φ eₛ eₜ ∗ R ++∗
        N (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ
      ) -∗
      ( ∀ eₛ eₜ,
        M Φ eₛ eₜ ∗ R ++∗
        M (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ
      ) -∗
      bisim_body Χ N M Φ eₛ eₜ ∗ R -∗
      bisim_body Χ N M (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ.
    Proof.
      iIntros "HN HM (Hbisim & HR)".
      iApply (bisim_body_monotone (λ _ _, R) with "[] [HN] [HM] [] HR Hbisim"); iSmash.
    Qed.

    (* TODO: bisim_body_bind *)
    (* TODO: bisim_body_bindₛ *)
    (* TODO: bisim_body_bindₜ *)

    (* TODO: bisim_body_bind_inv *)
    (* TODO: bisim_body_bind_invₛ *)
    (* TODO: bisim_body_bind_invₜ *)

    (* TODO: bisim_body_decompose *)

    Lemma bisim_body_stepₛ Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₛ eₛ σₛ⌝ ∗
            ∀ eₛ' σₛ',
            ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ==∗
              sim_state_interp σₛ' σₜ ∗
              M Φ eₛ' eₜ
      ) ⊢
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iSmash.
    Qed.
    Lemma bisim_body_head_stepₛ Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₛ eₛ σₛ⌝ ∗
            ∀ eₛ' σₛ',
            ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ==∗
              sim_state_interp σₛ' σₜ ∗
              M Φ eₛ' eₜ
      ) ⊢
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HM".
      iApply bisim_body_stepₛ. iIntros "%σₛ %σₜ Hsi".
      iMod ("HM" with "Hsi") as "(%Hreducibleₛ & HM)".
      iSplitR; first auto using head_reducible_reducible. iIntros "!> %eₛ' %σₛ' %Hstepₛ".
      apply head_reducible_prim_step in Hstepₛ; last done.
      iSmash.
    Qed.
    Lemma bisim_body_pure_stepₛ Χ N M Φ eₛ1 eₛ2 eₜ :
      pure_step sim_progₛ eₛ1 eₛ2 →
      M Φ eₛ2 eₜ ⊢
      bisim_body Χ N M Φ eₛ1 eₜ.
    Proof.
      iIntros "%Hstepₛ HM".
      iApply bisim_body_stepₛ. iIntros "%σₛ %σₜ Hsi !>".
      iSplit; eauto using pure_step_safe. iIntros "%eₛ' %σₛ' %Hstepₛ' !>".
      eapply pure_step_det in Hstepₛ; last done. destruct Hstepₛ as (-> & ->).
      iSmash.
    Qed.
    Lemma bisim_body_pure_head_stepₛ Χ N M Φ eₛ1 eₛ2 eₜ :
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      M Φ eₛ2 eₜ ⊢
      bisim_body Χ N M Φ eₛ1 eₜ.
    Proof.
      intros Hstepₛ.
      iApply bisim_body_pure_stepₛ.
      eauto using pure_head_step_pure_step.
    Qed.

    Lemma bisim_body_stepₜ Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              M Φ eₛ eₜ'
      ) ⊢
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iSmash.
    Qed.
    Lemma bisim_body_head_stepₜ Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              M Φ eₛ eₜ'
      ) ⊢
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HM".
      iApply bisim_body_stepₜ. iIntros "%σₛ %σₜ Hsi".
      iMod ("HM" with "Hsi") as "(%Hreducibleₜ & HM)".
      iSplitR; first auto using head_reducible_reducible. iIntros "!> %eₜ' %σₜ' %Hstepₜ".
      apply head_reducible_prim_step in Hstepₜ; last done.
      iSmash.
    Qed.
    Lemma bisim_body_pure_stepₜ Χ N M Φ eₛ eₜ1 eₜ2 :
      pure_step sim_progₜ eₜ1 eₜ2 →
      M Φ eₛ eₜ2 ⊢
      bisim_body Χ N M Φ eₛ eₜ1.
    Proof.
      iIntros "%Hstepₜ HM".
      iApply bisim_body_stepₜ. iIntros "%σₛ %σₜ Hsi !>".
      iSplit; eauto using pure_step_safe. iIntros "%eₜ' %σₜ' %Hstepₜ' !>".
      eapply pure_step_det in Hstepₜ; last done. destruct Hstepₜ as (-> & ->).
      iSmash.
    Qed.
    Lemma bisim_body_pure_head_stepₜ Χ N M Φ eₛ eₜ1 eₜ2 :
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      M Φ eₛ eₜ2 ⊢
      bisim_body Χ N M Φ eₛ eₜ1.
    Proof.
      intros Hstepₜ.
      iApply bisim_body_pure_stepₜ.
      eauto using pure_head_step_pure_step.
    Qed.

    Lemma bisim_body_step Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₛ eₛ σₛ ∧ reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₛ' σₛ' eₜ' σₜ',
            ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ' ∧ prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ' σₜ' ∗
              N Φ eₛ' eₜ'
      ) ⊢
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iSmash.
    Qed.
    Lemma bisim_body_head_step Χ N M Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₛ eₛ σₛ ∧ head_reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₛ' σₛ' eₜ' σₜ',
            ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ' ∧ head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ' σₜ' ∗
              N Φ eₛ' eₜ'
      ) ⊢
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros "HN".
      iApply bisim_body_step. iIntros "%σₛ %σₜ Hsi".
      iMod ("HN" with "Hsi") as "((%Hreducibleₛ & %Hreducibleₜ) & HN)".
      iSplitR; first auto using head_reducible_reducible. iIntros "!> %eₛ' %σₛ' %eₜ' %σₜ' (%Hstepₛ & %Hstepₜ)".
      apply head_reducible_prim_step in Hstepₛ; last done.
      apply head_reducible_prim_step in Hstepₜ; last done.
      iSmash.
    Qed.
    Lemma bisim_body_pure_step Χ N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      pure_step sim_progₛ eₛ1 eₛ2 →
      pure_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      bisim_body Χ N M Φ eₛ1 eₜ1.
    Proof.
      iIntros "%Hstepₛ %Hstepₜ HN".
      iApply bisim_body_step. iIntros "%σₛ %σₜ Hsi !>".
      iSplit; first eauto using pure_step_safe. iIntros "%_eₛ2 %_σₛ2 %_eₜ2 %_σₜ (%_Hstepₜ & %_Hstepₛ) !>".
      eapply pure_step_det in _Hstepₛ as (-> & ->); last done.
      eapply pure_step_det in _Hstepₜ as (-> & ->); last done.
      iSmash.
    Qed.
    Lemma bisim_body_pure_head_step Χ N M Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      bisim_body Χ N M Φ eₛ1 eₜ1.
    Proof.
      iIntros "%Hstepₛ %Hstepₜ HN".
      iApply (bisim_body_pure_step with "HN");
        eauto using (tc_congruence id), pure_head_step_pure_step.
    Qed.

    Lemma bisim_body_apply_protocol Ψ Kₛ eₛ' Kₜ eₜ' Χ N M Φ eₛ eₜ :
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
      bisim_body Χ N M Φ eₛ eₜ.
    Proof.
      iIntros (-> ->) "H %σₛ %σₜ Hsi".
      do 4 iRight. iExists Kₛ, eₛ', Kₜ, eₜ', Ψ. iSplitR; first iSmash.
      iApply ("H" with "Hsi").
    Qed.
  End bisim_body.

  Section bisim_inner.
    #[local] Instance bisim_body'_ne Χ n :
      Proper (
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) (definition.bisim_body' Χ).
    Proof.
      intros N1 N2 HN M1 M2 HM ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
      simpl in HΦ, Heₛ, Heₜ. subst.
      apply bisim_body_ne; done || solve_proper.
    Qed.
    #[local] Instance bisim_body'_proper Χ :
      Proper (
        ((≡) ==> (≡)) ==>
        ((≡) ==> (≡)) ==>
        (≡) ==>
        (≡)
      ) (definition.bisim_body' Χ).
    Proof.
      intros N1 N2 HN M1 M2 HM ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
      simpl in HΦ, Heₛ, Heₜ. subst.
      apply bisim_body_proper; done || solve_proper.
    Qed.

    #[local] Instance bisim_body'_mono_pred Χ N :
      NonExpansive N →
      BiMonoPred (definition.bisim_body' Χ N).
    Proof.
      intros HN. split; last solve_proper.
      iIntros "%M1 %M2 %HM1 %HM2 #HM" (((Φ & eₛ) & eₜ)) "Hbisim /=".
      iApply (bisim_body_mono with "[] [] [] Hbisim"); iSmash.
    Qed.

    #[global] Instance bisim_inner_ne Χ n :
      Proper (
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) (bisim_inner Χ).
    Proof.
      rewrite definition.bisim_inner_unseal /definition.bisim_inner_def /curry3.
      solve_proper.
    Qed.
    #[global] Instance bisim_inner_proper Χ :
      Proper (
        ((≡) ==> (≡)) ==>
        (≡) ==>
        (≡) ==>
        (≡) ==>
        (≡)
      ) (bisim_inner Χ).
    Proof.
      rewrite definition.bisim_inner_unseal /definition.bisim_inner_def /curry3.
      solve_proper.
    Qed.

    Lemma bisim_inner_fixpoint Χ N Φ eₛ eₜ :
      NonExpansive N →
      bisim_inner Χ N Φ eₛ eₜ ⊣⊢
      bisim_body Χ N (bisim_inner Χ N) Φ eₛ eₜ.
    Proof.
      rewrite definition.bisim_inner_unseal.
      intros. setoid_rewrite least_fixpoint_unfold; [done | apply _].
    Qed.
    Lemma bisim_inner_unfold Χ N Φ eₛ eₜ :
      NonExpansive N →
      bisim_inner Χ N Φ eₛ eₜ ⊢
      bisim_body Χ N (bisim_inner Χ N) Φ eₛ eₜ.
    Proof.
      intros. rewrite bisim_inner_fixpoint //.
    Qed.
    Lemma bisim_inner_fold Χ N Φ eₛ eₜ :
      NonExpansive N →
      bisim_body Χ N (bisim_inner Χ N) Φ eₛ eₜ ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros. rewrite bisim_inner_fixpoint //.
    Qed.

    Lemma bisim_inner_strong_ind I Χ N Φ eₛ eₜ :
      NonExpansive N →
      NonExpansive I →
      □ (bisim_body Χ N (λ Φ eₛ eₜ, I Φ eₛ eₜ ∧ bisim_inner Χ N Φ eₛ eₜ) ---∗ I) ⊢
      bisim_inner Χ N Φ eₛ eₜ -∗
      I Φ eₛ eₜ.
    Proof.
      rewrite definition.bisim_inner_unseal.
      iIntros "%HN %HI #Hind Hbisim".
      replace (I Φ eₛ eₜ) with ((uncurry3 I) (Φ, eₛ, eₜ)); last done.
      iApply (least_fixpoint_ind with "[] Hbisim"). clear Φ eₛ eₜ. iIntros "!>" (((Φ & eₛ) & eₜ)) "Hbisim /=".
      iApply ("Hind" with "Hbisim").
    Qed.
    Lemma bisim_inner_ind I Χ N Φ eₛ eₜ :
      NonExpansive N →
      NonExpansive I →
      □ (bisim_body Χ N I ---∗ I) ⊢
      bisim_inner Χ N Φ eₛ eₜ -∗
      I Φ eₛ eₜ.
    Proof.
      iIntros "%HN %HI #Hind".
      iApply bisim_inner_strong_ind. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ Hbisim".
      iApply "Hind".
      iApply (bisim_body_mono with "[] [] [] Hbisim"); [iSmash.. |]. clear Φ eₛ eₜ. iIntros "%Φ %eₛ %eₜ (HI & _) //".
    Qed.

    Lemma bisim_inner_strongly_stuck Χ N Φ eₛ eₜ :
      NonExpansive N →
      strongly_stuck sim_progₛ eₛ →
      strongly_stuck sim_progₜ eₜ →
      ⊢ bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite bisim_inner_fixpoint. apply bisim_body_strongly_stuck.
    Qed.
    Lemma bisim_inner_strongly_head_stuck Χ N Φ eₛ eₜ :
      NonExpansive N →
      strongly_head_stuck sim_progₛ eₛ →
      strongly_head_stuck sim_progₜ eₜ →
      ⊢ bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite bisim_inner_fixpoint. apply bisim_body_strongly_head_stuck.
    Qed.

    Lemma bisim_inner_post Χ N Φ eₛ eₜ :
      NonExpansive N →
      Φ eₛ eₜ ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite bisim_inner_fixpoint //. apply bisim_body_post.
    Qed.

    Lemma cupd_bisim_inner Χ N Φ eₛ eₜ :
      NonExpansive N →
      (|++> bisim_inner Χ N Φ eₛ eₜ) ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite bisim_inner_fixpoint. apply cupd_bisim_body.
    Qed.
    Lemma bupd_bisim_inner Χ N Φ eₛ eₜ :
      NonExpansive N →
      (|==> bisim_inner Χ N Φ eₛ eₜ) ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN. rewrite bisim_inner_fixpoint. apply bupd_bisim_body.
    Qed.

    Lemma bisim_inner_monotone R Χ1 Χ2 N1 N2 Φ1 Φ2 eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      NonExpansive2 R →
      □ (Χ1 ++++∗ Χ2) -∗
      □ (R Φ1 Φ2 -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      □ (R Φ1 Φ2 -∗ Φ1 +++∗ Φ2) -∗
      R Φ1 Φ2 -∗
      bisim_inner Χ1 N1 Φ1 eₛ eₜ -∗
      bisim_inner Χ2 N2 Φ2 eₛ eₜ.
    Proof.
      intros HN1 HN2 HR.
      set I := λ Φ1 eₛ eₜ, (
        □ (Χ1 ++++∗ Χ2) -∗
        □ (R Φ1 Φ2 -∗ N1 Φ1 +++∗ N2 Φ2) -∗
        □ (R Φ1 Φ2 -∗ Φ1 +++∗ Φ2) -∗
        R Φ1 Φ2 -∗
        bisim_inner Χ2 N2 Φ2 eₛ eₜ
      )%I.
      cut (bisim_inner Χ1 N1 Φ1 eₛ eₜ -∗ I Φ1 eₛ eₜ).
      { iIntros "%HI #HΧ #HN #HΦ HR Hbisim".
        iApply (HI with "Hbisim HΧ HN HΦ HR").
      }
      iApply (bisim_inner_ind with "[]"); first solve_proper. clear Φ1 eₛ eₜ. iIntros "!> %Φ1 %eₛ %eₜ Hbisim #HΧ #HN #HΦ HR".
      iApply bisim_inner_fixpoint.
      iApply (bisim_body_monotone with "HΧ HN [] HΦ HR Hbisim"). clear eₛ eₜ. iIntros "HR %eₛ %eₜ HI".
      iApply ("HI" with "HΧ HN HΦ HR").
    Qed.

    Lemma bisim_inner_cupd_mono Χ1 Χ2 N1 N2 Φ eₛ eₜ :
      NonExpansive N2 →
      □ (Χ1 ++++∗ Χ2) -∗
      □ (N1 ++++∗ N2) -∗
      bisim_inner Χ1 N1 Φ eₛ eₜ -∗
      bisim_inner Χ2 N2 Φ eₛ eₜ.
    Proof.
      rewrite !definition.bisim_inner_unseal.
      iIntros "%HN2 #HΧ #HN Hbisim". rewrite /bisim_inner /curry3.
      iApply (least_fixpoint_iter with "[] Hbisim"). clear Φ eₛ eₜ. iIntros "!>" (((Φ & eₛ) & eₜ)) "Hbisim".
      rewrite least_fixpoint_unfold /definition.bisim_body' {1 3}/uncurry3.
      iApply (bisim_body_cupd_mono with "[] [] [] Hbisim"); [iSmash.. |]. iStep. auto.
    Qed.
    Lemma bisim_inner_bupd_mono Χ1 Χ2 N1 N2 Φ eₛ eₜ :
      NonExpansive N2 →
      □ (Χ1 ====∗ Χ2) -∗
      □ (N1 ====∗ N2) -∗
      bisim_inner Χ1 N1 Φ eₛ eₜ -∗
      bisim_inner Χ2 N2 Φ eₛ eₜ.
    Proof.
      iIntros "%HN2 #HΧ #HN".
      iApply bisim_inner_cupd_mono; iModIntro; iSmash.
    Qed.
    Lemma bisim_inner_mono Χ1 Χ2 N1 N2 Φ eₛ eₜ :
      NonExpansive N2 →
      □ (Χ1 ---∗ Χ2) -∗
      □ (N1 ---∗ N2) -∗
      bisim_inner Χ1 N1 Φ eₛ eₜ -∗
      bisim_inner Χ2 N2 Φ eₛ eₜ.
    Proof.
      iIntros "%HN2 #HΧ #HN".
      iApply bisim_inner_bupd_mono; iModIntro; iSmash.
    Qed.

    Lemma bisim_inner_strong_cupd_mono Χ1 Χ2 N1 N2 Φ1 Φ2 eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      □ (Χ1 ++++∗ Χ2) -∗
      □ ((Φ1 +++∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      (Φ1 +++∗ Φ2) -∗
      bisim_inner Χ1 N1 Φ1 eₛ eₜ -∗
      bisim_inner Χ2 N2 Φ2 eₛ eₜ.
    Proof.
      iIntros "%HN1 %HN2 #HΧ #HN HΦ".
      iApply (bisim_inner_monotone (λ Φ1 Φ2, Φ1 +++∗ Φ2)%I with "HΧ HN [] HΦ"); first solve_proper. iModIntro. iSmash.
    Qed.
    Lemma bisim_inner_strong_bupd_mono Χ1 Χ2 N1 N2 Φ1 Φ2 eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      □ (Χ1 ====∗ Χ2) -∗
      □ ((Φ1 ===∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      (Φ1 ===∗ Φ2) -∗
      bisim_inner Χ1 N1 Φ1 eₛ eₜ -∗
      bisim_inner Χ2 N2 Φ2 eₛ eₜ.
    Proof.
      iIntros "%HN1 %HN2 #HΧ #HN HΦ".
      iApply (bisim_inner_monotone (λ Φ1 Φ2, Φ1 ===∗ Φ2)%I with "[HΧ] HN [] HΦ"); first solve_proper; iModIntro; iSmash.
    Qed.
    Lemma bisim_inner_strong_mono Χ1 Χ2 N1 N2 Φ1 Φ2 eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      □ (Χ1 ---∗ Χ2) -∗
      □ ((Φ1 --∗ Φ2) -∗ N1 Φ1 +++∗ N2 Φ2) -∗
      (Φ1 --∗ Φ2) -∗
      bisim_inner Χ1 N1 Φ1 eₛ eₜ -∗
      bisim_inner Χ2 N2 Φ2 eₛ eₜ.
    Proof.
      iIntros "%HN1 %HN2 #HΧ #HN HΦ".
      iApply (bisim_inner_monotone (λ Φ1 Φ2, Φ1 --∗ Φ2)%I with "[HΧ] HN [] HΦ"); first solve_proper; iModIntro; iSmash.
    Qed.

    Lemma bisim_inner_cupd Χ N Φ eₛ eₜ :
      NonExpansive N →
      □ (N (λ eₛ eₜ, |++> Φ eₛ eₜ) +++∗ N Φ) ⊢
      bisim_inner Χ N (λ eₛ eₜ, |++> Φ eₛ eₜ) eₛ eₜ -∗
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      iIntros "%HN #HN".
      iApply (bisim_inner_strong_cupd_mono with "[HN]"); try iModIntro; iSmash.
    Qed.
    Lemma bisim_inner_bupd Χ N Φ eₛ eₜ :
      NonExpansive N →
      □ (N (λ eₛ eₜ, |==> Φ eₛ eₜ) +++∗ N Φ) ⊢
      bisim_inner Χ N (λ eₛ eₜ, |==> Φ eₛ eₜ) eₛ eₜ -∗
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      iIntros "%HN #HN".
      iApply (bisim_inner_strong_bupd_mono with "[HN]"); try iModIntro; iSmash.
    Qed.

    Lemma bisim_inner_frame_l Χ N R Φ eₛ eₜ :
      NonExpansive N →
      □ (
        ∀ eₛ eₜ,
        R ∗ N Φ eₛ eₜ ++∗
        N (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ
      ) -∗
      R ∗ bisim_inner Χ N Φ eₛ eₜ -∗
      bisim_inner Χ N (λ eₛ eₜ, R ∗ Φ eₛ eₜ) eₛ eₜ.
    Proof.
      iIntros "%HN #HN (HR & Hbisim)".
      iApply (bisim_inner_monotone (λ _ _, R) with "[] [HN] [] HR Hbisim"); first (by solve_proper_prepare); iModIntro; iSmash.
    Qed.
    Lemma bisim_inner_frame_r Χ N R Φ eₛ eₜ :
      NonExpansive N →
      □ (
        ∀ eₛ eₜ,
        N Φ eₛ eₜ ∗ R ++∗
        N (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ
      ) -∗
      bisim_inner Χ N Φ eₛ eₜ ∗ R -∗
      bisim_inner Χ N (λ eₛ eₜ, Φ eₛ eₜ ∗ R) eₛ eₜ.
    Proof.
      iIntros "%HN #HN (Hbisim & HR)".
      iApply (bisim_inner_monotone (λ _ _, R) with "[] [HN] [] HR Hbisim"); first (by solve_proper_prepare); iModIntro; iSmash.
    Qed.

    Lemma bisim_inner_bind' Χ N1 N2 Φ1 Φ2 Kₛ eₛ Kₜ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      bisim_inner Χ N1 Φ1 eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 Φ1 eₛ' eₜ' -∗
        N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
      ) -∗
      ( ∀ eₛ' eₜ',
        Φ1 eₛ' eₜ' -∗
        bisim_inner Χ N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
      ) -∗
      bisim_inner Χ N2 Φ2 (Kₛ @@ eₛ) (Kₜ @@ eₜ).
    Proof.
      intros HN1 HN2.
      set I : sim_protocol_O := λ Φ1 eₛ eₜ, (
        ( ∀ eₛ' eₜ',
          N1 Φ1 eₛ' eₜ' -∗
          N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
        ) -∗
        ( ∀ eₛ' eₜ',
          Φ1 eₛ' eₜ' -∗
          bisim_inner Χ N2 Φ2 (Kₛ @@ eₛ') (Kₜ @@ eₜ')
        ) -∗
        bisim_inner Χ N2 Φ2 (Kₛ @@ eₛ) (Kₜ @@ eₜ)
      )%I.
      assert (NonExpansive I) as HI.
      { solve_proper_prepare. solve_proper_core ltac:(fun _ => apply HN1 || f_equiv). }
      iApply (bisim_inner_ind I with "[]"). clear Φ1 eₛ eₜ. iIntros "!> %Φ1 %eₛ %eₜ Hbisim1 HN Hbisim2".
      rewrite bisim_inner_fixpoint. iIntros "%σₛ %σₜ Hsi".
      iMod ("Hbisim1" with "Hsi") as "[Hbisim1 | [Hbisim1 | [Hbisim1 | [Hbisim1 | Hbisim1]]]]".
      - iDestruct "Hbisim1" as "(Hsi & [(%Hstuckₛ & %Hstuckₜ) | HΦ1])".
        + iLeft. iFrame. iLeft.
          iPureIntro. split; (apply language_ctx_stuck; [apply _ | done]).
        + iRevert (σₛ σₜ) "Hsi". iApply bisim_inner_fixpoint. iApply ("Hbisim2" with "HΦ1").
      - iDestruct "Hbisim1" as "(%Hreducibleₛ & Hbisim1)".
        iRight. iLeft. iSplitR.
        { iPureIntro. apply reducible_fill_reducible. done. }
        iIntros "!> %eₛ'' %σₛ' %Hstepₛ".
        apply reducible_fill_prim_step in Hstepₛ as (eₛ' & -> & Hstepₛ); last done.
        iMod ("Hbisim1" with "[//]") as "($ & HI)".
        iApply ("HI" with "HN Hbisim2").
      - iDestruct "Hbisim1" as "(%Hreducibleₜ & Hbisim1)".
        do 2 iRight. iLeft. iSplitR.
        { iPureIntro. apply reducible_fill_reducible. done. }
        iIntros "!> %eₜ'' %σₜ' %Hstepₜ".
        apply reducible_fill_prim_step in Hstepₜ as (eₜ' & -> & Hstepₜ); last done.
        iMod ("Hbisim1" with "[//]") as "($ & HI)".
        iApply ("HI" with "HN Hbisim2").
      - iDestruct "Hbisim1" as "((%Hreducibleₛ & %Hreducibleₜ) & Hbisim1)".
        do 3 iRight. iLeft. iSplitR.
        { iPureIntro. split; apply reducible_fill_reducible; done. }
        iIntros "!> %eₛ'' %σₛ' %eₜ'' %σₜ' (%Hstepₛ & %Hstepₜ)".
        apply reducible_fill_prim_step in Hstepₛ as (eₛ' & -> & Hstepₛ); last done.
        apply reducible_fill_prim_step in Hstepₜ as (eₜ' & -> & Hstepₜ); last done.
        iSmash.
      - iDestruct "Hbisim1" as "(%Kₛ' & %eₛ' & %Kₜ' & %eₜ' & %Ψ & (-> & ->) & HΧ & Hsi & HN1)".
        do 4 iRight. iExists (Kₛ ⋅ Kₛ'), eₛ', (Kₜ ⋅ Kₜ'), eₜ', Ψ. iFrame. iSplitR; first rewrite !fill_op //. iIntros "!> %eₛ'' %eₜ'' HΨ".
        rewrite -!fill_op. iApply ("HN1" with "HΨ HN Hbisim2").
    Qed.
    Lemma bisim_inner_bind Χ N1 N2 Φ Kₛ eₛ Kₜ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      bisim_inner Χ N1 (λ eₛ' eₜ', bisim_inner Χ N2 Φ (Kₛ @@ eₛ') (Kₜ @@ eₜ')) eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 (λ eₛ' eₜ', bisim_inner Χ N2 Φ (Kₛ @@ eₛ') (Kₜ @@ eₜ')) eₛ' eₜ' -∗
        N2 Φ (Kₛ @@ eₛ') (Kₜ @@ eₜ')
      ) -∗
      bisim_inner Χ N2 Φ (Kₛ @@ eₛ) (Kₜ @@ eₜ).
    Proof.
      iIntros "%HN1 %HN2 Hbisim HN".
      iApply (bisim_inner_bind' with "Hbisim HN"). iSmash.
    Qed.
    Lemma bisim_inner_bindₛ' Χ N1 N2 Φ1 Φ2 K eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      bisim_inner Χ N1 Φ1 eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 Φ1 eₛ' eₜ' -∗
        N2 Φ2 (K @@ eₛ') eₜ'
      ) -∗
      ( ∀ eₛ' eₜ',
        Φ1 eₛ' eₜ' -∗
        bisim_inner Χ N2 Φ2 (K @@ eₛ') eₜ'
      ) -∗
      bisim_inner Χ N2 Φ2 (K @@ eₛ) eₜ.
    Proof.
      iIntros "%HN1 %HN2 Hbisim1 HN Hbisim2".
      iEval (rewrite -(fill_empty eₜ)).
      iApply (bisim_inner_bind' with "Hbisim1 [HN] [Hbisim2]"); iIntros "%eₛ' %eₜ'";
        rewrite fill_empty; iSmash.
    Qed.
    Lemma bisim_inner_bindₛ Χ N1 N2 Φ K eₛ eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      bisim_inner Χ N1 (λ eₛ' eₜ', bisim_inner Χ N2 Φ (K @@ eₛ') eₜ') eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 (λ eₛ' eₜ', bisim_inner Χ N2 Φ (K @@ eₛ') eₜ') eₛ' eₜ' -∗
        N2 Φ (K @@ eₛ') eₜ'
      ) -∗
      bisim_inner Χ N2 Φ (K @@ eₛ) eₜ.
    Proof.
      iIntros "%HN1 %HN2 Hbisim HN".
      iApply (bisim_inner_bindₛ' with "Hbisim HN"). iSmash.
    Qed.
    Lemma bisim_inner_bindₜ' Χ N1 N2 eₛ K eₜ Φ1 Φ2 :
      NonExpansive N1 →
      NonExpansive N2 →
      bisim_inner Χ N1 Φ1 eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 Φ1 eₛ' eₜ' -∗
        N2 Φ2 eₛ' (K @@ eₜ')
      ) -∗
      ( ∀ eₛ' eₜ',
        Φ1 eₛ' eₜ' -∗
        bisim_inner Χ N2 Φ2 eₛ' (K @@ eₜ')
      ) -∗
      bisim_inner Χ N2 Φ2 eₛ (K @@ eₜ).
    Proof.
      iIntros "%HN1 %HN2 Hbisim1 HN Hbisim2".
      iEval (rewrite -(fill_empty eₛ)).
      iApply (bisim_inner_bind' with "Hbisim1 [HN] [Hbisim2]"); iIntros "%eₛ' %eₜ'";
        rewrite fill_empty; iSmash.
    Qed.
    Lemma bisim_inner_bindₜ Χ N1 N2 Φ eₛ K eₜ :
      NonExpansive N1 →
      NonExpansive N2 →
      bisim_inner Χ N1 (λ eₛ' eₜ', bisim_inner Χ N2 Φ eₛ' (K @@ eₜ')) eₛ eₜ -∗
      ( ∀ eₛ' eₜ',
        N1 (λ eₛ' eₜ', bisim_inner Χ N2 Φ eₛ' (K @@ eₜ')) eₛ' eₜ' -∗
        N2 Φ eₛ' (K @@ eₜ')
      ) -∗
      bisim_inner Χ N2 Φ eₛ (K @@ eₜ).
    Proof.
      iIntros "%HN1 %HN2 Hbisim HN".
      iApply (bisim_inner_bindₜ' with "Hbisim HN"). iSmash.
    Qed.

    (* TODO: bisim_inner_bind_inv *)
    (* TODO: bisim_inner_bind_invₛ *)
    (* TODO: bisim_inner_bind_invₜ *)

    (* TODO: bisim_inner_decompose *)

    Lemma bisim_inner_stepₛ Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₛ eₛ σₛ⌝ ∗
            ∀ eₛ' σₛ',
            ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ==∗
              sim_state_interp σₛ' σₜ ∗
              bisim_inner Χ N Φ eₛ' eₜ
      ) ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite bisim_inner_fixpoint. apply bisim_body_stepₛ.
    Qed.
    Lemma bisim_inner_head_stepₛ Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₛ eₛ σₛ⌝ ∗
            ∀ eₛ' σₛ',
            ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ==∗
              sim_state_interp σₛ' σₜ ∗
              bisim_inner Χ N Φ eₛ' eₜ
      ) ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite bisim_inner_fixpoint. apply bisim_body_head_stepₛ.
    Qed.
    Lemma bisim_inner_pure_stepₛ Χ N Φ eₛ1 eₛ2 eₜ :
      NonExpansive N →
      pure_step sim_progₛ eₛ1 eₛ2 →
      bisim_inner Χ N Φ eₛ2 eₜ ⊢
      bisim_inner Χ N Φ eₛ1 eₜ.
    Proof.
      intros HN.
      setoid_rewrite bisim_inner_fixpoint at 2; [apply bisim_body_pure_stepₛ | done].
    Qed.
    Lemma bisim_inner_pure_stepsₛ Χ N Φ eₛ1 eₛ2 eₜ :
      NonExpansive N →
      rtc (pure_step sim_progₛ) eₛ1 eₛ2 →
      bisim_inner Χ N Φ eₛ2 eₜ ⊢
      bisim_inner Χ N Φ eₛ1 eₜ.
    Proof.
      intros HN.
      induction 1 as [| eₛ eₛ' eₛ'' Hstepₛ Hstepsₛ IH]; first done.
      rewrite IH. apply bisim_inner_pure_stepₛ; done.
    Qed.
    Lemma bisim_inner_pure_head_stepₛ Χ N Φ eₛ1 eₛ2 eₜ :
      NonExpansive N →
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      bisim_inner Χ N Φ eₛ2 eₜ ⊢
      bisim_inner Χ N Φ eₛ1 eₜ.
    Proof.
      intros HN.
      setoid_rewrite bisim_inner_fixpoint at 2; [apply bisim_body_pure_head_stepₛ | done].
    Qed.
    Lemma bisim_inner_pure_head_stepsₛ Χ N Φ eₛ1 eₛ2 eₜ :
      NonExpansive N →
      rtc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
      bisim_inner Χ N Φ eₛ2 eₜ ⊢
      bisim_inner Χ N Φ eₛ1 eₜ.
    Proof.
      intros HN.
      induction 1 as [| eₛ eₛ' eₛ'' Hstepₛ Hstepsₛ IH]; first done.
      rewrite IH. apply bisim_inner_pure_head_stepₛ; done.
    Qed.

    Lemma bisim_inner_stepₜ Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              bisim_inner Χ N Φ eₛ eₜ'
      ) ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite bisim_inner_fixpoint. apply bisim_body_stepₜ.
    Qed.
    Lemma bisim_inner_head_stepₜ Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              bisim_inner Χ N Φ eₛ eₜ'
      ) ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite bisim_inner_fixpoint. apply bisim_body_head_stepₜ.
    Qed.
    Lemma bisim_inner_pure_stepₜ Χ N Φ eₛ eₜ1 eₜ2 :
      NonExpansive N →
      pure_step sim_progₜ eₜ1 eₜ2 →
      bisim_inner Χ N Φ eₛ eₜ2 ⊢
      bisim_inner Χ N Φ eₛ eₜ1.
    Proof.
      intros HN.
      setoid_rewrite bisim_inner_fixpoint at 2; [apply bisim_body_pure_stepₜ | done].
    Qed.
    Lemma bisim_inner_pure_stepsₜ Χ N Φ eₛ eₜ1 eₜ2 :
      NonExpansive N →
      rtc (pure_step sim_progₜ) eₜ1 eₜ2 →
      bisim_inner Χ N Φ eₛ eₜ2 ⊢
      bisim_inner Χ N Φ eₛ eₜ1.
    Proof.
      intros HN.
      induction 1 as [| eₜ eₜ' eₜ'' Hstepₜ Hstepsₜ IH]; first done.
      rewrite IH. apply bisim_inner_pure_stepₜ; done.
    Qed.
    Lemma bisim_inner_pure_head_stepₜ Χ N Φ eₛ eₜ1 eₜ2 :
      NonExpansive N →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      bisim_inner Χ N Φ eₛ eₜ2 ⊢
      bisim_inner Χ N Φ eₛ eₜ1.
    Proof.
      intros HN.
      setoid_rewrite bisim_inner_fixpoint at 2; [apply bisim_body_pure_head_stepₜ | done].
    Qed.
    Lemma bisim_inner_pure_head_stepsₜ Χ N Φ eₛ eₜ1 eₜ2 :
      NonExpansive N →
      rtc (pure_head_step sim_progₜ) eₜ1 eₜ2 →
      bisim_inner Χ N Φ eₛ eₜ2 ⊢
      bisim_inner Χ N Φ eₛ eₜ1.
    Proof.
      intros HN.
      induction 1 as [| eₜ eₜ' eₜ'' Hstepₜ Hstepsₜ IH]; first done.
      rewrite IH. apply bisim_inner_pure_head_stepₜ; done.
    Qed.

    Lemma bisim_inner_step Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₛ eₛ σₛ ∧ reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₛ' σₛ' eₜ' σₜ',
            ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ' ∧ prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ' σₜ' ∗
              N Φ eₛ' eₜ'
      ) ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite bisim_inner_fixpoint. apply bisim_body_step.
    Qed.
    Lemma bisim_inner_head_step Χ N Φ eₛ eₜ :
      NonExpansive N →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₛ eₛ σₛ ∧ head_reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₛ' σₛ' eₜ' σₜ',
            ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ' ∧ head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ' σₜ' ∗
              N Φ eₛ' eₜ'
      ) ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite bisim_inner_fixpoint. apply bisim_body_head_step.
    Qed.
    Lemma bisim_inner_pure_step Χ N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      NonExpansive N →
      pure_step sim_progₛ eₛ1 eₛ2 →
      pure_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      bisim_inner Χ N Φ eₛ1 eₜ1.
    Proof.
      intros HN.
      rewrite bisim_inner_fixpoint. apply bisim_body_pure_step.
    Qed.
    Lemma bisim_inner_pure_head_step Χ N Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      NonExpansive N →
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      N Φ eₛ2 eₜ2 ⊢
      bisim_inner Χ N Φ eₛ1 eₜ1.
    Proof.
      intros HN.
      rewrite bisim_inner_fixpoint. apply bisim_body_pure_head_step.
    Qed.

    Lemma bisim_inner_apply_protocol Ψ Kₛ eₛ' Kₜ eₜ' Χ N Φ eₛ eₜ :
      NonExpansive N →
      eₛ = Kₛ @@ eₛ' →
      eₜ = Kₜ @@ eₜ' →
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          Χ Ψ eₛ' eₜ' ∗
          sim_state_interp σₛ σₜ ∗
            ∀ eₛ eₜ,
            Ψ eₛ eₜ ++∗
            bisim_inner Χ N Φ (Kₛ @@ eₛ) (Kₜ @@ eₜ)

      ) ⊢
      bisim_inner Χ N Φ eₛ eₜ.
    Proof.
      intros HN.
      rewrite bisim_inner_fixpoint. apply bisim_body_apply_protocol.
    Qed.
  End bisim_inner.

  Section bisim.
    #[local] Instance bisim_inner'_ne Χ n :
      Proper (
        ((≡{n}≡) ==> (≡{n}≡)) ==>
        (≡{n}≡) ==>
        (≡{n}≡)
      ) (definition.bisim_inner' Χ).
    Proof.
      intros N1 N2 HN ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
      simpl in HΦ, Heₛ, Heₜ. subst.
      apply bisim_inner_ne; done || solve_proper.
    Qed.
    #[local] Instance bisim_inner'_proper Χ :
      Proper (
        ((≡) ==> (≡)) ==>
        (≡) ==>
        (≡)
      ) (definition.bisim_inner' Χ).
    Proof.
      intros N1 N2 HN ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
      simpl in HΦ, Heₛ, Heₜ. subst.
      apply bisim_inner_proper; done || solve_proper.
    Qed.
    #[local] Instance bisim_inner'_mono_pred Χ :
      BiMonoPred (definition.bisim_inner' Χ).
    Proof.
      split.
      - iIntros "%N1 %N2 %HN1 %HN2 #HN" (((Φ & eₛ) & eₜ)) "Hbisim".
        iApply (bisim_inner_mono with "[] [] Hbisim"); first solve_proper; iModIntro; iSmash.
      - intros N HN n ((Φ1 & eₛ1) & eₜ1) ((Φ2 & eₛ2) & eₜ2) ((HΦ & Heₛ%leibniz_equiv) & Heₜ%leibniz_equiv).
        rewrite /definition.bisim_inner' /=.
        apply bisim_inner_ne; solve_proper.
    Qed.

    #[global] Instance bisim_ne Χ n :
      Proper ((≡{n}≡) ==> (=) ==> (=) ==> (≡{n}≡)) (bisim Χ).
    Proof.
      rewrite definition.bisim_unseal.
      solve_proper.
    Qed.
    #[global] Instance bisim_proper Χ :
      Proper ((≡) ==> (=) ==> (=) ==> (≡)) (bisim Χ).
    Proof.
      rewrite definition.bisim_unseal.
      solve_proper.
    Qed.

    Lemma bisim_fixpoint Χ Φ eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} ⊣⊢
      bisim_inner Χ (bisim Χ) Φ eₛ eₜ.
    Proof.
      rewrite definition.bisim_unseal.
      setoid_rewrite greatest_fixpoint_unfold; [done | apply _].
    Qed.
    Lemma bisim_unfold Χ Φ eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} ⊢
      bisim_inner Χ (bisim Χ) Φ eₛ eₜ.
    Proof.
      rewrite bisim_fixpoint //.
    Qed.
    Lemma bisim_fold Χ Φ eₛ eₜ :
      bisim_inner Χ (bisim Χ) Φ eₛ eₜ ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite bisim_fixpoint //.
    Qed.

    Lemma bisim_eq Χ Φ eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} ⊣⊢
      bisim_body Χ (bisim Χ) (bisim Χ) Φ eₛ eₜ.
    Proof.
      rewrite bisim_fixpoint.
      setoid_rewrite bisim_inner_fixpoint; last solve_proper.
      rewrite /bisim_body. setoid_rewrite <- bisim_fixpoint. done.
    Qed.

    Lemma bisim_strong_coind Χ I Φ eₛ eₜ :
      NonExpansive I →
      □ (I ---∗ bisim_inner Χ (λ Φ eₛ eₜ, I Φ eₛ eₜ ∨ BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }})) ⊢
      I Φ eₛ eₜ -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite definition.bisim_unseal.
      iIntros "%HI #Hind HI".
      replace (I Φ eₛ eₜ) with ((uncurry3 I) (Φ, eₛ, eₜ)); last done.
      iApply (greatest_fixpoint_coind with "[] HI"). clear Φ eₛ eₜ. iIntros "!>" (((Φ & eₛ) & eₜ)) "HI /=".
      iSmash.
    Qed.
    Lemma bisim_coind Χ I Φ eₛ eₜ :
      NonExpansive I →
      □ (I ---∗ bisim_inner Χ I) ⊢
      I Φ eₛ eₜ -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iIntros "%HI #Hind".
      iApply bisim_strong_coind. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ HI".
      iApply (bisim_inner_mono with "[] [] (Hind HI)"); first solve_proper; iModIntro; iSmash.
    Qed.

    Lemma bisim_strongly_stuck Χ Φ eₛ eₜ :
      strongly_stuck sim_progₛ eₛ →
      strongly_stuck sim_progₜ eₜ →
      ⊢ BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite bisim_fixpoint. apply bisim_inner_strongly_stuck. solve_proper.
    Qed.
    Lemma bisim_strongly_head_stuck Χ Φ eₛ eₜ :
      strongly_head_stuck sim_progₛ eₛ →
      strongly_head_stuck sim_progₜ eₜ →
      ⊢ BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite bisim_fixpoint. apply bisim_inner_strongly_head_stuck. solve_proper.
    Qed.

    Lemma bisim_post Χ Φ eₛ eₜ :
      Φ eₛ eₜ ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite bisim_fixpoint. apply bisim_inner_post. solve_proper.
    Qed.

    Lemma cupd_bisim Χ Φ eₛ eₜ :
      (|++> BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite bisim_fixpoint. apply cupd_bisim_inner. solve_proper.
    Qed.
    Lemma bupd_bisim Χ Φ eₛ eₜ :
      (|==> BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite bisim_fixpoint. apply bupd_bisim_inner. solve_proper.
    Qed.

    Lemma bisim_strong_cupd_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ++++∗ Χ2) -∗
      (Φ1 +++∗ Φ2) -∗
      BISIM eₛ ≃ eₜ [[ Χ1 ]] {{ Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ2 ]] {{ Φ2 }}.
    Proof.
      set I : sim_protocol_O := λ Φ2 eₛ eₜ, (
        ∃ Φ1,
        □ (Χ1 ++++∗ Χ2) ∗
        (Φ1 +++∗ Φ2) ∗
        BISIM eₛ ≃ eₜ [[ Χ1 ]] {{ Φ1 }}
      )%I.
      assert (NonExpansive I) by solve_proper.
      cut (I Φ2 eₛ eₜ -∗ BISIM eₛ ≃ eₜ [[ Χ2 ]] {{ Φ2 }}).
      { iIntros "%HI #HΧ HΦ Hbisim1".
        iApply HI. iExists Φ1. iFrame "#∗".
      }
      iApply (bisim_coind with "[]"). clear Φ1 Φ2 eₛ eₜ. iIntros "!> %Φ2 %eₛ %eₜ (%Φ1 & #HΧ & HΦ & Hbisim1)".
      rewrite bisim_fixpoint.
      iApply (bisim_inner_strong_cupd_mono with "HΧ [] HΦ Hbisim1"); first solve_proper. clear eₛ eₜ. iIntros "!> HΦ %eₛ %eₜ Hbisim1".
      iExists Φ1. iFrame "#∗". iSmash.
    Qed.
    Lemma bisim_strong_bupd_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ====∗ Χ2) -∗
      (Φ1 ===∗ Φ2) -∗
      BISIM eₛ ≃ eₜ [[ Χ1 ]] {{ Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ2 ]] {{ Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hbisim1".
      iApply (bisim_strong_cupd_mono with "[] [HΦ] Hbisim1"); first iModIntro; iSmash.
    Qed.
    Lemma bisim_strong_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ---∗ Χ2) -∗
      (Φ1 --∗ Φ2) -∗
      BISIM eₛ ≃ eₜ [[ Χ1 ]] {{ Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ2 ]] {{ Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hbisim1".
      iApply (bisim_strong_bupd_mono with "[] [HΦ] Hbisim1"); first iModIntro; iSmash.
    Qed.

    Lemma bisim_cupd_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 +++∗ Φ2) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      iIntros "HΦ Hbisim1".
      iApply (bisim_strong_cupd_mono with "[] HΦ Hbisim1"). iModIntro. iSmash.
    Qed.
    Lemma bisim_bupd_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 ===∗ Φ2) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      rewrite -bisim_cupd_mono. iSmash.
    Qed.
    Lemma bisim_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 --∗ Φ2) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      rewrite -bisim_bupd_mono. iSmash.
    Qed.
    Lemma bisim_mono' Χ Φ1 Φ2 eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ1 }} ⊢
      (Φ1 --∗ Φ2) -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      rewrite bisim_mono. iSmash.
    Qed.

    Lemma bisim_cupd Χ Φ eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }} ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iApply (bisim_cupd_mono with "[]"). iSmash.
    Qed.
    Lemma bisim_bupd Χ Φ eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }} ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      iApply (bisim_bupd_mono with "[]"). iSmash.
    Qed.

    Lemma bisim_frame_l Χ R Φ eₛ eₜ :
      R ∗ BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ eₜ, R ∗ Φ eₛ eₜ }}.
    Proof.
      iIntros "(HR & Hbisim)".
      iApply (bisim_mono with "[HR] Hbisim"). iSmash.
    Qed.
    Lemma bisim_frame_r Χ R Φ eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} ∗ R ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ eₜ, Φ eₛ eₜ ∗ R }}.
    Proof.
      iIntros "(Hbisim & HR)".
      iApply (bisim_mono with "[HR] Hbisim"). iSmash.
    Qed.

    Lemma bisim_bind Χ Φ Kₛ eₛ Kₜ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        BISIM Kₛ @@ eₛ' ≃ Kₜ @@ eₜ' [[ Χ ]] {{ Φ }}
      }} ⊢
      BISIM Kₛ @@ eₛ ≃ Kₜ @@ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      set I : sim_protocol_O := λ Φ eₛ'' eₜ'', (
        ∃ Kₛ eₛ Kₜ eₜ,
        ⌜eₛ'' = Kₛ @@ eₛ ∧ eₜ'' = Kₜ @@ eₜ⌝ ∗
        BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          BISIM Kₛ @@ eₛ' ≃ Kₜ @@ eₜ' [[ Χ ]] {{ Φ }}
        }}
      )%I.
      assert (NonExpansive I) as HI by solve_proper+.
      enough (∀ eₛ eₜ, I Φ eₛ eₜ -∗ BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}) as H.
      { iIntros "Hbisim". iApply H. iSmash. }
      clear eₛ eₜ. iIntros "%eₛ %eₜ".
      iApply (bisim_coind with "[]"). clear Φ Kₛ eₛ Kₜ eₜ. iIntros "!> %Φ %eₛ'' %eₜ'' (%Kₛ & %eₛ & %Kₜ & %eₜ & (-> & ->) & Hbisim)".
      rewrite bisim_fixpoint. iApply (bisim_inner_bind' with "Hbisim"); first solve_proper.
      - iSmash.
      - iIntros "%eₛ' %eₜ' Hbisim".
        rewrite bisim_fixpoint. iApply (bisim_inner_mono with "[] [] Hbisim"); first auto. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ Hbisim".
        iExists ∅, eₛ, ∅, eₜ. iSplit; first rewrite !fill_empty //.
        iApply bisim_post. rewrite !fill_empty //.
    Qed.
    Lemma bisim_bind' Χ Φ1 Φ2 Kₛ eₛ Kₜ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ1 }} -∗
      ( ∀ eₛ' eₜ',
        Φ1 eₛ' eₜ' -∗
        BISIM Kₛ @@ eₛ' ≃ Kₜ @@ eₜ' [[ Χ ]] {{ Φ2 }}
      ) -∗
      BISIM Kₛ @@ eₛ ≃ Kₜ @@ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      iIntros "Hbisim HΦ1".
      iApply bisim_bind. iApply (bisim_mono with "HΦ1 Hbisim").
    Qed.
    Lemma bisim_bindₛ Χ Φ K eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        BISIM K @@ eₛ' ≃ eₜ' [[ Χ ]] {{ Φ }}
      }} ⊢
      BISIM K @@ eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite -{2}(fill_empty eₜ) -(bisim_bind ∅).
      iApply (bisim_mono with "[]").
      setoid_rewrite fill_empty. iSmash.
    Qed.
    Lemma bisim_bindₜ Χ Φ eₛ K eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        BISIM eₛ' ≃ K @@ eₜ' [[ Χ ]] {{ Φ }}
      }} ⊢
      BISIM eₛ ≃ K @@ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite -{2}(fill_empty eₛ) -(bisim_bind ∅).
      iApply (bisim_mono with "[]").
      setoid_rewrite fill_empty. iSmash.
    Qed.

    Lemma bisim_bind_inv Χ Φ Kₛ eₛ Kₜ eₜ :
      BISIM Kₛ @@ eₛ ≃ Kₜ @@ eₜ [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        BISIM Kₛ @@ eₛ' ≃ Kₜ @@ eₜ' [[ Χ ]] {{ Φ }}
      }}.
    Proof.
      iIntros "Hbisim". iApply bisim_post. iSmash.
    Qed.
    Lemma bisim_bind_invₛ Χ Φ K eₛ eₜ :
      BISIM K @@ eₛ ≃ eₜ [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        BISIM K @@ eₛ' ≃ eₜ' [[ Χ ]] {{ Φ }}
      }}.
    Proof.
      iIntros "Hbisim". iApply bisim_post. iSmash.
    Qed.
    Lemma bisim_bind_invₜ Χ Φ eₛ K eₜ :
      BISIM eₛ ≃ K @@ eₜ [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
        BISIM eₛ' ≃ K @@ eₜ' [[ Χ ]] {{ Φ }}
      }}.
    Proof.
      iIntros "Hbisim". iApply bisim_post. iSmash.
    Qed.

    Lemma bisim_decompose Χ Φ1 Φ2 eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ1 }} -∗
      ( ∀ eₛ' eₜ',
        Φ1 eₛ' eₜ' -∗
        BISIM eₛ' ≃ eₜ' [[ Χ ]] {{ Φ2 }}
      ) -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ2 }}.
    Proof.
      iIntros "Hbisim1 Hbisim2".
      iEval (rewrite -(fill_empty eₛ) -(fill_empty eₜ)). iApply bisim_bind.
      iApply (bisim_mono' with "Hbisim1 [Hbisim2]").
      setoid_rewrite fill_empty. iSmash.
    Qed.

    Lemma bisim_stepₛ Χ Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₛ eₛ σₛ⌝ ∗
            ∀ eₛ' σₛ',
            ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ==∗
              sim_state_interp σₛ' σₜ ∗
              BISIM eₛ' ≃ eₜ [[ Χ ]] {{ Φ }}
      ) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      setoid_rewrite bisim_fixpoint. apply bisim_inner_stepₛ. solve_proper.
    Qed.
    Lemma bisim_head_stepₛ Χ Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₛ eₛ σₛ⌝ ∗
            ∀ eₛ' σₛ',
            ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ'⌝ ==∗
              sim_state_interp σₛ' σₜ ∗
              BISIM eₛ' ≃ eₜ [[ Χ ]] {{ Φ }}
      ) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      setoid_rewrite bisim_fixpoint. apply bisim_inner_head_stepₛ. solve_proper.
    Qed.
    Lemma bisim_pure_stepsₛ Χ Φ eₛ1 eₛ2 eₜ :
      rtc (pure_step sim_progₛ) eₛ1 eₛ2 →
      BISIM eₛ2 ≃ eₜ [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ1 ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !bisim_fixpoint. apply bisim_inner_pure_stepsₛ. solve_proper.
    Qed.
    Lemma bisim_pure_stepₛ Χ Φ eₛ1 eₛ2 eₜ :
      pure_step sim_progₛ eₛ1 eₛ2 →
      BISIM eₛ2 ≃ eₜ [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ1 ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !bisim_fixpoint. apply bisim_inner_pure_stepₛ. solve_proper.
    Qed.
    Lemma bisim_pure_head_stepsₛ Χ Φ eₛ1 eₛ2 eₜ :
      rtc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
      BISIM eₛ2 ≃ eₜ [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ1 ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !bisim_fixpoint. apply bisim_inner_pure_head_stepsₛ. solve_proper.
    Qed.
    Lemma bisim_pure_head_stepₛ Χ Φ eₛ1 eₛ2 eₜ :
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      BISIM eₛ2 ≃ eₜ [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ1 ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !bisim_fixpoint. apply bisim_inner_pure_head_stepₛ. solve_proper.
    Qed.

    Lemma bisim_stepₜ Χ Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              BISIM eₛ ≃ eₜ' [[ Χ ]] {{ Φ }}
      ) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      setoid_rewrite bisim_fixpoint. apply bisim_inner_stepₜ. solve_proper.
    Qed.
    Lemma bisim_head_stepₜ Χ Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₜ' σₜ',
            ⌜head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ σₜ' ∗
              BISIM eₛ ≃ eₜ' [[ Χ ]] {{ Φ }}
      ) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      setoid_rewrite bisim_fixpoint. apply bisim_inner_head_stepₜ. solve_proper.
    Qed.
    Lemma bisim_pure_stepsₜ Χ Φ eₛ eₜ1 eₜ2 :
      rtc (pure_step sim_progₜ) eₜ1 eₜ2 →
      BISIM eₛ ≃ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ ≃ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !bisim_fixpoint. apply bisim_inner_pure_stepsₜ. solve_proper.
    Qed.
    Lemma bisim_pure_stepₜ Χ Φ eₛ eₜ1 eₜ2 :
      pure_step sim_progₜ eₜ1 eₜ2 →
      BISIM eₛ ≃ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ ≃ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !bisim_fixpoint. apply bisim_inner_pure_stepₜ. solve_proper.
    Qed.
    Lemma bisim_pure_head_stepsₜ Χ Φ eₛ eₜ1 eₜ2 :
      rtc (pure_head_step sim_progₜ) eₜ1 eₜ2 →
      BISIM eₛ ≃ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ ≃ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !bisim_fixpoint. apply bisim_inner_pure_head_stepsₜ. solve_proper.
    Qed.
    Lemma bisim_pure_head_stepₜ Χ Φ eₛ eₜ1 eₜ2 :
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      BISIM eₛ ≃ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ ≃ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite !bisim_fixpoint. apply bisim_inner_pure_head_stepₜ. solve_proper.
    Qed.

    Lemma bisim_step Χ Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜reducible sim_progₛ eₛ σₛ ∧ reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₛ' σₛ' eₜ' σₜ',
            ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ' ∧ prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ' σₜ' ∗
              BISIM eₛ' ≃ eₜ' [[ Χ ]] {{ Φ }}
      ) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite bisim_fixpoint. apply bisim_inner_step. solve_proper.
    Qed.
    Lemma bisim_head_step Χ Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          ⌜head_reducible sim_progₛ eₛ σₛ ∧ head_reducible sim_progₜ eₜ σₜ⌝ ∗
            ∀ eₛ' σₛ' eₜ' σₜ',
            ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ' ∧ head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
              sim_state_interp σₛ' σₜ' ∗
              BISIM eₛ' ≃ eₜ' [[ Χ ]] {{ Φ }}
      ) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite bisim_fixpoint. apply bisim_inner_head_step. solve_proper.
    Qed.
    Lemma bisim_pure_steps Χ Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      rtc (pure_step sim_progₛ) eₛ1 eₛ2 →
      rtc (pure_step sim_progₜ) eₜ1 eₜ2 →
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      intros. rewrite bisim_pure_stepsₛ // bisim_pure_stepsₜ //.
    Qed.
    Lemma bisim_pure_step Χ Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      pure_step sim_progₛ eₛ1 eₛ2 →
      pure_step sim_progₜ eₜ1 eₜ2 →
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      intros. rewrite bisim_pure_stepₛ // bisim_pure_stepₜ //.
    Qed.
    Lemma bisim_pure_head_steps Χ Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      rtc (pure_head_step sim_progₛ) eₛ1 eₛ2 →
      rtc (pure_head_step sim_progₜ) eₜ1 eₜ2 →
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      intros. rewrite bisim_pure_head_stepsₛ // bisim_pure_head_stepsₜ //.
    Qed.
    Lemma bisim_pure_head_step Χ Φ eₛ1 eₛ2 eₜ1 eₜ2 :
      pure_head_step sim_progₛ eₛ1 eₛ2 →
      pure_head_step sim_progₜ eₜ1 eₜ2 →
      BISIM eₛ2 ≃ eₜ2 [[ Χ ]] {{ Φ }} ⊢
      BISIM eₛ1 ≃ eₜ1 [[ Χ ]] {{ Φ }}.
    Proof.
      intros. rewrite bisim_pure_head_stepₛ // bisim_pure_head_stepₜ //.
    Qed.

    Lemma bisim_apply_protocol Ψ Χ Φ eₛ eₜ :
      ( ∀ σₛ σₜ,
        sim_state_interp σₛ σₜ ==∗
          Χ Ψ eₛ eₜ ∗
          sim_state_interp σₛ σₜ ∗
            ∀ eₛ eₜ,
            Ψ eₛ eₜ -∗
            BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}
      ) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}.
    Proof.
      rewrite bisim_fixpoint. iIntros "Hbisim".
      iApply (bisim_inner_apply_protocol Ψ ∅ _ ∅); [solve_proper | rewrite fill_empty //.. |]. iIntros "%σₛ %σₜ Hsi".
      iMod ("Hbisim" with "Hsi") as "($ & $ & Hbisim)". iIntros "!> %eₛ' %eₜ' HΨ !>".
      rewrite !fill_empty -bisim_fixpoint. iSmash.
    Qed.
  End bisim.

  Section bisimv.
    Lemma bisimv_post Χ Φ vₛ vₜ eₛ eₜ :
      eₛ = of_val vₛ →
      eₜ = of_val vₜ →
      Φ vₛ vₜ ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite bisimv_unseal -bisim_post. iSmash.
    Qed.

    Lemma bisimv_strong_cupd_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ++++∗ Χ2) -∗
      (Φ1 +++∗ Φ2) -∗
      BISIM eₛ ≃ eₜ [[ Χ1 ]] {{# Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ2 ]] {{# Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hbisim1".
      iApply (bisim_strong_cupd_mono with "HΧ [HΦ] Hbisim1"). clear eₛ eₜ. iIntros "%eₛ %eₜ".
      iApply (sim_post_vals_cupd_mono with "HΦ").
    Qed.
    Lemma bisimv_strong_bupd_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ====∗ Χ2) -∗
      (Φ1 ===∗ Φ2) -∗
      BISIM eₛ ≃ eₜ [[ Χ1 ]] {{# Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ2 ]] {{# Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hbisim1".
      iApply (bisimv_strong_cupd_mono with "[] [HΦ] Hbisim1"); first iModIntro; iSmash.
    Qed.
    Lemma bisimv_strong_mono Χ1 Χ2 Φ1 Φ2 eₛ eₜ :
      □ (Χ1 ---∗ Χ2) -∗
      (Φ1 --∗ Φ2) -∗
      BISIM eₛ ≃ eₜ [[ Χ1 ]] {{# Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ2 ]] {{# Φ2 }}.
    Proof.
      iIntros "#HΧ HΦ Hbisim1".
      iApply (bisimv_strong_bupd_mono with "[] [HΦ] Hbisim1"); first iModIntro; iSmash.
    Qed.

    Lemma bisimv_cupd_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 +++∗ Φ2) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      rewrite -bisim_cupd_mono. setoid_rewrite <- sim_post_vals_cupd_mono. iSmash.
    Qed.
    Lemma bisimv_bupd_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 ===∗ Φ2) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      rewrite -bisim_bupd_mono. setoid_rewrite <- sim_post_vals_bupd_mono. iSmash.
    Qed.
    Lemma bisimv_mono Χ Φ1 Φ2 eₛ eₜ :
      (Φ1 --∗ Φ2) ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ1 }} -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      rewrite -bisim_mono. setoid_rewrite <- sim_post_vals_mono. iSmash.
    Qed.
    Lemma bisimv_mono' Χ Φ1 Φ2 eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ1 }} ⊢
      (Φ1 --∗ Φ2) -∗
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ2 }}.
    Proof.
      rewrite bisimv_mono. iSmash.
    Qed.

    Lemma bisimv_cupd Χ Φ eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ eₛ eₜ, |++> Φ eₛ eₜ }} ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      apply bi.wand_entails. rewrite -bisimv_cupd_mono. iSmash.
    Qed.
    Lemma bisimv_bupd Χ Φ eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ eₛ eₜ, |==> Φ eₛ eₜ }} ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      apply bi.wand_entails. rewrite -bisimv_bupd_mono. iSmash.
    Qed.

    Lemma bisimv_frame_l Χ R Φ eₛ eₜ :
      R ∗ BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ }} ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ eₛ eₜ, R ∗ Φ eₛ eₜ }}.
    Proof.
      rewrite bisimv_mono'. iSmash.
    Qed.
    Lemma bisimv_frame_r Χ R Φ eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ }} ∗ R ⊢
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ eₛ eₜ, Φ eₛ eₜ ∗ R }}.
    Proof.
      rewrite bisimv_mono'. iSmash.
    Qed.

    Lemma bisimv_bind Χ Φ Kₛ eₛ Kₜ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ vₛ vₜ,
        BISIM Kₛ @@ of_val vₛ ≃ Kₜ @@ of_val vₜ [[ Χ ]] {{# Φ }}
      }} ⊢
      BISIM Kₛ @@ eₛ ≃ Kₜ @@ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal -bisim_bind bisim_mono'. iSmash.
    Qed.
    Lemma bisimv_bindₛ Χ Φ K eₛ eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ vₛ vₜ,
        BISIM K @@ of_val vₛ ≃ of_val vₜ [[ Χ ]] {{# Φ }}
      }} ⊢
      BISIM K @@ eₛ ≃ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal -bisim_bindₛ bisim_mono'. iSmash.
    Qed.
    Lemma bisimv_bindₜ Χ Φ eₛ K eₜ :
      BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ vₛ vₜ,
        BISIM of_val vₛ ≃ K @@ of_val vₜ [[ Χ ]] {{# Φ }}
      }} ⊢
      BISIM eₛ ≃ K @@ eₜ [[ Χ ]] {{# Φ }}.
    Proof.
      rewrite !bisimv_unseal -bisim_bindₜ bisim_mono'. iSmash.
    Qed.
  End bisimv.

  Lemma bisim_close Χ Φ eₛ eₜ :
    □ (
      ∀ Ψ eₛ eₜ,
      Χ Ψ eₛ eₜ -∗
      bisim_inner ⊥ (λ _, bisim Χ Ψ) (λ _ _, False) eₛ eₜ
    ) ⊢
    BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} -∗
    BISIM eₛ ≃ eₜ {{ Φ }}.
  Proof.
    iIntros "#H".
    iApply (bisim_coind with "[]"); first solve_proper. clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ".
    rewrite bisim_fixpoint. iApply (bisim_inner_ind with "[]"); first solve_proper.
    { solve_proper_prepare. apply bisim_inner_ne; done || solve_proper. }
    clear Φ eₛ eₜ. iIntros "!> %Φ %eₛ %eₜ Hbisim".
    setoid_rewrite bisim_inner_fixpoint at 2; last solve_proper.
    iIntros "%σₛ %σₜ Hsi".
    iMod ("Hbisim" with "Hsi") as "[Hbisim | [Hbisim | [Hbisim | [Hbisim | Hbisim]]]]"; try iSmash.
    iDestruct "Hbisim" as "(%Kₛ & %eₛ' & %Kₜ & %eₜ' & %Ψ & (-> & ->) & HΧ & Hsi & Hbisim)".
    iDestruct ("H" with "HΧ") as "HΨ". iClear "H".
    iRevert (σₛ σₜ) "Hsi". setoid_rewrite <- bisim_inner_fixpoint; last solve_proper.
    iApply (bisim_inner_bind' with "HΨ [Hbisim]"); [solve_proper | iIntros "%eₛ %eₜ HΨ" | iIntros "%eₛ %eₜ []"].
    iApply (bisim_bind' with "HΨ"). clear eₛ eₜ. iIntros "%eₛ %eₜ HΨ".
    iApply cupd_bisim. rewrite bisim_fixpoint.
    iApply (bisim_inner_mono with "[] [] (Hbisim HΨ)"); first solve_proper; iModIntro; iSmash.
  Qed.
  Lemma bisim_close_step Χ Φ eₛ eₜ :
    □ (
      ∀ Ψ eₛ σₛ eₜ σₜ,
      Χ Ψ eₛ eₜ -∗
      sim_state_interp σₛ σₜ ==∗
        ⌜reducible sim_progₛ eₛ σₛ ∧ reducible sim_progₜ eₜ σₜ⌝ ∗
          ∀ eₛ' σₛ' eₜ' σₜ',
          ⌜prim_step sim_progₛ eₛ σₛ eₛ' σₛ' ∧ prim_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
            sim_state_interp σₛ' σₜ' ∗
            BISIM eₛ' ≃ eₜ' [[ Χ ]] {{ Ψ }}
    ) ⊢
    BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} -∗
    BISIM eₛ ≃ eₜ {{ Φ }}.
  Proof.
    iIntros "#H".
    iApply bisim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iApply bisim_inner_step. iIntros "%σₛ %σₜ".
    iApply ("H" with "HΧ").
  Qed.
  Lemma bisim_close_head_step Χ Φ eₛ eₜ :
    □ (
      ∀ Ψ eₛ σₛ eₜ σₜ,
      Χ Ψ eₛ eₜ -∗
      sim_state_interp σₛ σₜ ==∗
        ⌜head_reducible sim_progₛ eₛ σₛ ∧ head_reducible sim_progₜ eₜ σₜ⌝ ∗
          ∀ eₛ' σₛ' eₜ' σₜ',
          ⌜head_step sim_progₛ eₛ σₛ eₛ' σₛ' ∧ head_step sim_progₜ eₜ σₜ eₜ' σₜ'⌝ ==∗
            sim_state_interp σₛ' σₜ' ∗
            BISIM eₛ' ≃ eₜ' [[ Χ ]] {{ Ψ }}
    ) ⊢
    BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} -∗
    BISIM eₛ ≃ eₜ {{ Φ }}.
  Proof.
    iIntros "#H".
    iApply bisim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iApply bisim_inner_head_step. iIntros "%σₛ %σₜ".
    iApply ("H" with "HΧ").
  Qed.
  Lemma bisim_close_pure_step Χ Φ eₛ eₜ :
    □ (
      ∀ Ψ eₛ eₜ,
      Χ Ψ eₛ eₜ -∗
        ∃ eₛ' eₜ',
        ⌜pure_step sim_progₛ eₛ eₛ' ∧ pure_step sim_progₜ eₜ eₜ'⌝ ∗
        BISIM eₛ' ≃ eₜ' [[ Χ ]] {{ Ψ }}
    ) ⊢
    BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} -∗
    BISIM eₛ ≃ eₜ {{ Φ }}.
  Proof.
    iIntros "#H".
    iApply bisim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepₛ & %Hstepₜ) & Hbisim)".
    iApply bisim_inner_pure_step; done.
  Qed.
  Lemma bisim_close_pure_head_step Χ Φ eₛ eₜ :
    □ (
      ∀ Ψ eₛ eₜ,
      Χ Ψ eₛ eₜ -∗
        ∃ eₛ' eₜ',
        ⌜pure_head_step sim_progₛ eₛ eₛ' ∧ pure_head_step sim_progₜ eₜ eₜ'⌝ ∗
        BISIM eₛ' ≃ eₜ' [[ Χ ]] {{ Ψ }}
    ) ⊢
    BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }} -∗
    BISIM eₛ ≃ eₜ {{ Φ }}.
  Proof.
    iIntros "#H".
    iApply bisim_close. clear eₛ eₜ. iIntros "!> %Ψ %eₛ %eₜ HΧ".
    iDestruct ("H" with "HΧ") as "(%eₛ' & %eₜ' & (%Hstepₛ & %Hstepₜ) & Hbisim)".
    iApply bisim_inner_pure_head_step; done.
  Qed.
End sim_state.
