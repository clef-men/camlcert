From Paco Require Import
  paco.

From iris.bi Require Import
  fixpoint.
From iris.base_logic Require Import
  bi.

From simuliris Require Import
  prelude.
From simuliris.iris Require Import
  proofmode.
From simuliris.iris.base_logic Require Import
  satisfiable.
From simuliris.iris.program_logic Require Import
  language.

Section bi.
  Context `{!BiBUpd PROP} `{!BiAffine PROP}.
  Context {Λ : language}.
  Context (prog : program Λ).
  Implicit Types N I : expr_O Λ -d> state_O Λ -d> PROP.

  Definition idiverges_body N : expr_O Λ -d> state_O Λ -d> PROP := (
    λ e σ,
      |==> ∃ e' σ', ⌜prim_step prog e σ e' σ'⌝ ∗ N e' σ'
  )%I.

  #[local] Definition idiverges_body' (N : prodO (expr_O Λ) (state_O Λ) -d> PROP) : prodO (expr_O Λ) (state_O Λ) → PROP :=
    uncurry $ idiverges_body $ curry N.
  #[local] Definition idiverges_def : expr_O Λ -d> state_O Λ -d> PROP :=
    curry $ bi_greatest_fixpoint idiverges_body'.
  #[local] Definition idiverges_aux :
    seal (@idiverges_def). Proof. by eexists. Qed.
  Definition idiverges :=
    idiverges_aux.(unseal).
  #[local] Definition idiverges_unseal : @idiverges = @idiverges_def :=
    idiverges_aux.(seal_eq).

  Section idiverges_body.
    #[global] Instance idiverges_body_ne n :
      Proper ((≡{n}≡) ==> (=) ==> (=) ==> (≡{n}≡)) idiverges_body.
    Proof.
      solve_proper.
    Qed.
    #[global] Instance idiverges_body_proper :
      Proper ((≡) ==> (=) ==> (=) ==> (≡)) idiverges_body.
    Proof.
      solve_proper.
    Qed.

    Lemma bupd_idiverges_body N e σ :
      (|==> idiverges_body N e σ) -∗
      idiverges_body N e σ.
    Proof.
      iIntros ">$".
    Qed.

    Lemma idiverges_body_mono N1 N2 e σ :
      (∀ e' σ', N1 e' σ' -∗ N2 e' σ') -∗
      idiverges_body N1 e σ -∗
      idiverges_body N2 e σ.
    Proof.
      iIntros "HN >(%e' & %σ' & %Hstep & HN1)". iSmash.
    Qed.
  End idiverges_body.

  Section idiverges.
    #[local] Instance idiverges_body'_ne n :
      Proper ((≡{n}≡) ==> (=) ==> (≡{n}≡)) idiverges_body'.
    Proof.
      intros N1 N2 HN (e1, σ1) (e2, σ2) <-.
      rewrite /idiverges_body' /=. f_equiv. intros e σ. apply HN.
    Qed.
    #[local] Instance idiverges_body'_proper :
      Proper ((≡) ==> (=) ==> (≡)) idiverges_body'.
    Proof.
      intros N1 N2 HN (e1, σ1) (e2, σ2) <-.
      rewrite /idiverges_body' /=. f_equiv. intros e σ. apply HN.
    Qed.
    #[local] Instance idiverges_body'_mono_pred :
      BiMonoPred idiverges_body'.
    Proof.
      split; last solve_proper.
      iIntros "%N1 %N2 %HN1 %HN2 #HN" ((e, σ)) "/=".
      iApply idiverges_body_mono. iIntros "%e' %σ' HN1".
      iApply ("HN" with "HN1").
    Qed.

    Lemma idiverges_fixpoint e σ :
      idiverges e σ ⊣⊢
      idiverges_body idiverges e σ.
    Proof.
      rewrite idiverges_unseal.
      setoid_rewrite greatest_fixpoint_unfold; [done | apply _].
    Qed.
    Lemma idiverges_unfold e σ :
      idiverges e σ -∗
      idiverges_body idiverges e σ.
    Proof.
      rewrite idiverges_fixpoint. auto.
    Qed.
    Lemma idiverges_fold e σ :
      idiverges_body idiverges e σ -∗
      idiverges e σ.
    Proof.
      rewrite idiverges_fixpoint. auto.
    Qed.

    Lemma idiverges_strong_coind I e σ :
      □ (
        ∀ e σ,
        I e σ ==∗
          ∃ e' σ',
          ⌜tc (step prog) (e, σ) (e', σ')⌝ ∗
          (I e' σ' ∨ idiverges e σ)
      ) -∗
      I e σ -∗
      idiverges e σ.
    Proof.
      assert (BiMonoPred (λ (N : _ → _) x, uncurry I x ∨ idiverges_body' N x)%I) as Hmono.
      { clear dependent e σ. split.
        - iIntros "%N1 %N2 %HN1 %HN2 #HN" ((e, σ)) "[HI | HN1]"; first iSmash.
          iRight. iApply (idiverges_body_mono with "[] HN1"). iSmash.
        - intros N HN n (e1, σ1) (e2, σ2) (He%leibniz_equiv & Hσ%leibniz_equiv).
          solve_proper.
      }
      rewrite idiverges_unseal.
      iIntros "#Hind HI".
      replace (I e σ) with ((uncurry I) (e, σ)); last done.
      iApply (greatest_fixpoint_paco with "[] HI"). clear e σ. iIntros "!>" ((e, σ)) "HI /=".
      iMod ("Hind" with "HI") as "(%e'' & %σ'' & %Hsteps & [HI | Hidiv])"; iClear "Hind"; last first.
      { rewrite -idiverges_unseal idiverges_fixpoint.
        iApply (idiverges_body_mono with "[] Hidiv"). iIntros "%e' %σ' Hidiv".
        rewrite idiverges_unseal /idiverges_def /curry /Datatypes.curry /=.
        iApply (greatest_fixpoint_strong_mono with "[] Hidiv"). clear dependent e σ. iIntros "!> %N" ((e, σ)) "Hidiv". auto.
      }
      iModIntro.
      match goal with |- _ _ ?P =>
        enough (I e'' σ'' -∗ P) as H; first iApply (H with "HI")
      end.
      remember (e, σ) as cfg. remember (e'', σ'') as cfg''.
      revert dependent σ. revert dependent e.
      induction Hsteps as [? ? Hstep | ? (e', σ') ? Hstep Hsteps IH]; iIntros (e σ ->) "HI"; simplify.
      - iExists e'', σ''. iSplit; first auto using step_prim_step.
        setoid_rewrite greatest_fixpoint_unfold; auto.
      - iExists e', σ'. iSplit; first auto using step_prim_step.
        setoid_rewrite greatest_fixpoint_unfold; last done.
        iRight. iApply (IH with "HI"); iSmash+.
    Qed.
    Lemma idiverges_coind I e σ :
      □ (
        ∀ e σ,
        I e σ ==∗
          ∃ e' σ',
          ⌜tc (step prog) (e, σ) (e', σ')⌝ ∗
          I e' σ'
      ) -∗
      I e σ -∗
      idiverges e σ.
    Proof.
      iIntros "#Hind HI".
      iApply (idiverges_strong_coind with "[] HI"). clear e σ. iIntros "!> %e %σ HI".
      iMod ("Hind" with "HI") as "(%e' & %σ' & %Hsteps & HI)". iSmash.
    Qed.

    Lemma bupd_idiverges e σ :
      (|==> idiverges e σ) -∗
      idiverges e σ.
    Proof.
      rewrite idiverges_fixpoint. apply bupd_idiverges_body.
    Qed.
  End idiverges.
End bi.

Lemma idiverges_adequacy M Λ (prog : program Λ) e σ :
  (⊢@{uPredI M} idiverges prog e σ) →
  diverges prog e σ.
Proof.
  intros Hidiv%isat_intro.
  revert dependent σ. revert dependent e. pcofix CIH. intros e σ.
  rewrite idiverges_fixpoint.
  intros (e' & (σ' & (Hstep%satisfiable_elim & Hisat)%satisfiable_sep)%satisfiable_exists)%satisfiable_bupd%satisfiable_exists.
  pfold. econstructor; first done. right. apply CIH. done.
Qed.
