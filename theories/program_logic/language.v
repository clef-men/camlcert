From stdpp Require Import
  gmap.

From Paco Require Import
  paco.

From iris.algebra Require Export
  ofe.

From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.

Section LanguageMixin.
  Context {expr val program state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (prim_step : program → expr → state → expr → state → Prop).

  Record LanguageMixin := {
    language_mixin_to_of_val e v :
      e = of_val v →
      to_val e = Some v ;
    language_mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    language_mixin_prim_step_not_val prog e1 σ1 e2 σ2 :
      prim_step prog e1 σ1 e2 σ2 →
      to_val e1 = None ;
  }.
End LanguageMixin.
#[global] Arguments Build_LanguageMixin {_ _ _ _ _ _ _} _ _ _ : assert.

Structure language := {
  expr : Type ;
  val : Type ;
  program : Type ;
  state : Type ;
  of_val : val → expr ;
  to_val : expr → option val ;
  prim_step : program → expr → state → expr → state → Prop ;
  language_mixin : LanguageMixin of_val to_val prim_step ;
}.
#[global] Arguments Build_language {_ _ _ _ _ _ _} _ : assert.
#[global] Arguments of_val {_} _ : assert.
#[global] Arguments to_val {_} _ : assert.
#[global] Arguments prim_step {_} _ _ _ _ _ : assert.

Definition config Λ : Type := expr Λ * state Λ.

Canonical state_O Λ := leibnizO (state Λ).
Canonical val_O Λ := leibnizO (val Λ).
Canonical expr_O Λ := leibnizO (expr Λ).

Class LanguageCtx {Λ} (K : expr Λ → expr Λ) := {
  language_ctx_not_val e :
    to_val e = None →
    to_val (K e) = None ;
  language_ctx_prim_step prog e1 σ1 e2 σ2 :
    prim_step prog e1 σ1 e2 σ2 →
    prim_step prog (K e1) σ1 (K e2) σ2 ;
  language_ctx_prim_step_inv prog e1' σ1 e2 σ2 :
    to_val e1' = None →
    prim_step prog (K e1') σ1 e2 σ2 →
    ∃ e2', e2 = K e2' ∧ prim_step prog e1' σ1 e2' σ2 ;
}.

#[global] Instance language_ctx_id Λ :
  LanguageCtx (@id (expr Λ)).
Proof.
  split; naive_solver.
Qed.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types prog : program Λ.
  Implicit Types σ : state Λ.
  Implicit Types cfg : config Λ.

  Inductive step prog cfg1 cfg2 : Prop :=
    | prim_step_step e1 σ1 e2 σ2 :
        prim_step prog e1 σ1 e2 σ2 →
        cfg1 = (e1, σ1) →
        cfg2 = (e2, σ2) →
        step prog cfg1 cfg2.

  Definition reducible prog e σ :=
    ∃ e' σ', prim_step prog e σ e' σ'.
  Definition strongly_reducible prog e :=
    ∀ σ, reducible prog e σ.
  Definition irreducible prog e σ :=
    ∀ e' σ', ¬ prim_step prog e σ e' σ'.
  Definition strongly_irreducible prog e :=
    ∀ σ, irreducible prog e σ.
  Definition stuck prog e σ :=
    irreducible prog e σ ∧ to_val e = None.
  Definition strongly_stuck prog e :=
    strongly_irreducible prog e ∧ to_val e = None.

  Definition converges prog e σ e' σ' :=
    rtc (step prog) (e, σ) (e', σ') ∧ irreducible prog e' σ'.

  CoInductive diverges_body prog (diverges : expr Λ → state Λ → Prop) : expr Λ → state Λ → Prop :=
    | diverges_step e σ e' σ' :
        prim_step prog e σ e' σ' →
        diverges e' σ' →
        diverges_body prog diverges e σ.
  Definition diverges prog :=
    paco2 (diverges_body prog) bot2.
  Lemma diverges_body_mono prog :
    monotone2 (diverges_body prog).
  Proof.
    intros e σ R1 R2 [] HR. econstructor; first done. apply HR. done.
  Qed.
  Hint Resolve diverges_body_mono : paco.

  Record pure_step prog e1 e2 := {
    pure_step_safe σ1 :
      reducible prog e1 σ1 ;
    pure_step_det σ1 e2' σ2 :
      prim_step prog e1 σ1 e2' σ2 →
      σ2 = σ1 ∧ e2' = e2 ;
  }.

  Class IsStronglyStuck prog e :=
    is_strongly_stuck : strongly_stuck prog e.
  Class PureExec prog (ϕ : Prop) n e1 e2 :=
    pure_exec : ϕ → nsteps (pure_step prog) n e1 e2.

  Lemma to_of_val e v :
    e = of_val v →
    to_val e = Some v.
  Proof.
    apply language_mixin.
  Qed.
  Lemma of_to_val e v :
    to_val e = Some v →
    of_val v = e.
  Proof.
    apply language_mixin.
  Qed.
  Lemma prim_step_not_val prog e1 σ1 e2 σ2 :
    prim_step prog e1 σ1 e2 σ2 →
    to_val e1 = None.
  Proof.
    apply language_mixin.
  Qed.

  Lemma step_prim_step prog e1 σ1 e2 σ2 :
    step prog (e1, σ1) (e2, σ2) →
    prim_step prog e1 σ1 e2 σ2.
  Proof.
    intros []. simplify. eauto.
  Qed.
  Lemma irreducible_not_reducible prog e σ :
    irreducible prog e σ ↔
    ¬ reducible prog e σ.
  Proof.
    rewrite /reducible /irreducible. naive_solver.
  Qed.
  Lemma reducible_not_val prog e σ :
    reducible prog e σ →
    to_val e = None.
  Proof.
    intros (? & ? & ?); eauto using prim_step_not_val.
  Qed.
  Lemma val_irreducible prog e v σ :
    e = of_val v →
    irreducible prog e σ.
  Proof.
    intros ?%to_of_val ? ? ?%prim_step_not_val. naive_solver.
  Qed.
  Lemma stuck_irreducible prog e σ :
    stuck prog e σ →
    irreducible prog e σ.
  Proof.
    rewrite /stuck. naive_solver.
  Qed.
  Lemma stuck_not_val prog e σ :
    stuck prog e σ →
    to_val e = None.
  Proof.
    rewrite /stuck. naive_solver.
  Qed.

  Lemma diverges_reducible prog e σ :
    diverges prog e σ →
    reducible prog e σ.
  Proof.
    intros Hdiv. punfold Hdiv.
    destruct Hdiv. esplit. eauto.
  Qed.
  Lemma diverges_not_stuck prog e σ :
    diverges prog e σ →
    ¬ stuck prog e σ.
  Proof.
    by intros ?%diverges_reducible ?%stuck_irreducible%irreducible_not_reducible.
  Qed.
  Lemma diverges_not_val prog e σ v :
    diverges prog e σ →
    e ≠ of_val v.
  Proof.
    intros Hdiv ?%to_of_val. punfold Hdiv.
    destruct Hdiv as [? ? ? ? ?%prim_step_not_val]. naive_solver.
  Qed.

  Lemma strongly_stuck_stuck prog e σ :
    strongly_stuck prog e →
    stuck prog e σ.
  Proof.
    intros []. split; done.
  Qed.

  Lemma pure_step_prim_step prog e1 e2 σ :
    pure_step prog e1 e2 →
    prim_step prog e1 σ e2 σ.
  Proof.
    intros [(? & ? & Hstep) Hdet].
    specialize (Hdet _ _ _ Hstep). simplify. eauto.
  Qed.

  Lemma pure_steps_pure_exec prog n e1 e2 :
    nsteps (pure_step prog) n e1 e2 →
    PureExec prog True n e1 e2.
  Proof.
    intros ? ?. done.
  Qed.
  Lemma pure_step_pure_exec prog e1 e2 :
    pure_step prog e1 e2 →
    PureExec prog True 1 e1 e2.
  Proof.
    intros. eapply pure_steps_pure_exec, nsteps_once. done.
  Qed.

  Lemma rtc_step_val prog v cfg1 cfg2 :
    rtc (step prog) cfg1 cfg2 →
    cfg1.1 = of_val v →
    cfg1 = cfg2.
  Proof.
    intros [| [] ? ? [? ? ? ? ?%prim_step_not_val ? ?]] ?%to_of_val;
      simplify; naive_solver.
  Qed.
  Lemma rtc_step_stuck prog cfg1 cfg2 :
    rtc (step prog) cfg1 cfg2 →
    stuck prog cfg1.1 cfg1.2 →
    cfg1 = cfg2.
  Proof.
    intros [| [] ? ? []] Hstuck; simplify; first done.
    eapply stuck_irreducible in Hstuck. rewrite /irreducible in Hstuck.
    naive_solver.
  Qed.

  Section language_ctx.
    Context (K : expr Λ → expr Λ) `{!LanguageCtx K}.

    Lemma language_ctx_step prog e1 σ1 e2 σ2 :
      step prog (e1, σ1) (e2, σ2) →
      step prog (K e1, σ1) (K e2, σ2).
    Proof.
      intros []. simplify.
      esplit; auto. eauto using language_ctx_prim_step.
    Qed.
    Lemma language_ctx_reducible prog e σ :
      reducible prog e σ →
      reducible prog (K e) σ.
    Proof.
      rewrite /reducible. naive_solver eauto using language_ctx_prim_step.
    Qed.
    Lemma language_ctx_tc_step prog e1 σ1 e2 σ2 :
      tc (step prog) (e1, σ1) (e2, σ2) →
      tc (step prog) (K e1, σ1) (K e2, σ2).
    Proof.
      set K_cfg : config Λ → config Λ := λ '(e, σ), (K e, σ).
      change (K ?e, ?σ) with (K_cfg (e, σ)). apply tc_congruence.
      intros [] []. apply language_ctx_step.
    Qed.
    Lemma language_ctx_rtc_step prog e1 σ1 e2 σ2 :
      rtc (step prog) (e1, σ1) (e2, σ2) →
      rtc (step prog) (K e1, σ1) (K e2, σ2).
    Proof.
      intros []%rtc_tc; simplify; eauto using rtc_refl, tc_rtc, language_ctx_tc_step.
    Qed.

    Lemma language_ctx_reducible_inv prog e σ :
      to_val e = None →
      reducible prog (K e) σ →
      reducible prog e σ.
    Proof.
      intros ? (? & ? & (? & -> & ?)%language_ctx_prim_step_inv); last done.
      rewrite /reducible. eauto.
    Qed.
    Lemma language_ctx_irreducible prog e σ :
      to_val e = None →
      irreducible prog e σ →
      irreducible prog (K e) σ.
    Proof.
      rewrite !irreducible_not_reducible. eauto using language_ctx_reducible_inv.
    Qed.
    Lemma language_ctx_strongly_irreducible prog e :
      to_val e = None →
      strongly_irreducible prog e →
      strongly_irreducible prog (K e).
    Proof.
      intros Hnot_val Hstrongly_irreducible σ. apply language_ctx_irreducible; done.
    Qed.
    Lemma language_ctx_stuck prog e σ :
      stuck prog e σ →
      stuck prog (K e) σ.
    Proof.
      rewrite /stuck. intros [].
      split; eauto using language_ctx_not_val, language_ctx_irreducible.
    Qed.
    Lemma language_ctx_strongly_stuck prog e :
      strongly_stuck prog e →
      strongly_stuck prog (K e).
    Proof.
      intros (Hirreducible & Hnot_val). split.
      - apply language_ctx_strongly_irreducible; done.
      - apply language_ctx_not_val. done.
    Qed.

    Lemma language_ctx_pure_step prog e1 e2 :
      pure_step prog e1 e2 →
      pure_step prog (K e1) (K e2).
    Proof.
      intros []. split.
      - eauto using language_ctx_reducible.
      - intros * Hstep. eapply language_ctx_prim_step_inv in Hstep; first naive_solver.
        unshelve eauto using reducible_not_val; eauto.
    Qed.
    Lemma language_ctx_pure_exec prog ϕ n e1 e2 :
      PureExec prog ϕ n e1 e2 →
      PureExec prog ϕ n (K e1) (K e2).
    Proof.
      intros ? ?. eapply nsteps_congruence; eauto using language_ctx_pure_step.
    Qed.
  End language_ctx.
End language.

#[global] Hint Resolve diverges_body_mono : paco.
