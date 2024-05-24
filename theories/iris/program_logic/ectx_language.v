From iris.algebra Require Export
  cmra.

From camlcert Require Import
  prelude.
From camlcert.common Require Export
  typeclasses.
From camlcert.iris.program_logic Require Export
  language.

Section EctxLanguageMixin.
  Context {expr val program state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (head_step : program → expr → state → expr → state → Prop).
  Context ectx `{!Empty ectx} `{!Op ectx} `{!Fill ectx expr}.

  Record EctxLanguageMixin := {
    ectx_language_mixin_to_of_val e v :
      e = of_val v →
      to_val e = Some v ;
    ectx_language_mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    ectx_language_mixin_head_step_not_val prog e1 σ1 e2 σ2 :
      head_step prog e1 σ1 e2 σ2 →
      to_val e1 = None ;

    ectx_language_mixin_fill_empty e :
      ∅ @@ e = e ;
    ectx_language_mixin_fill_op K1 K2 e :
      K1 @@ K2 @@ e = (K1 ⋅ K2) @@ e ;
    ectx_language_mixin_fill_inj K :
      Inj (=) (=) (K @@.) ;
    ectx_language_mixin_fill_not_val K e :
      to_val e = None →
      to_val (K @@ e) = None ;

    ectx_language_mixin_fill_redex prog K K_redex e1 e1_redex σ1 e2 σ2 :
      K @@ e1 = K_redex @@ e1_redex →
      to_val e1 = None →
      head_step prog e1_redex σ1 e2 σ2 →
      ∃ K', K_redex = K ⋅ K' ;
    ectx_language_mixin_fill_head_step_val prog K e1 σ1 e2 σ2 :
      head_step prog (K @@ e1) σ1 e2 σ2 →
      is_Some (to_val e1) ∨ K = ∅ ;
  }.
End EctxLanguageMixin.
#[global] Arguments Build_EctxLanguageMixin {_ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _ _ : assert.

Structure ectx_language := {
  expr : Type ;
  val : Type ;
  program : Type ;
  state : Type ;
  of_val : val → expr ;
  to_val : expr → option val ;
  head_step : program → expr → state → expr → state → Prop ;

  ectx : Type ;
  ectx_language_empty : Empty ectx ;
  ectx_language_op : Op ectx ;
  ectx_language_fill : Fill ectx expr ;

  ectx_language_mixin : EctxLanguageMixin of_val to_val head_step ectx ;
}.
#[global] Arguments Build_ectx_language {_ _ _ _ _ _ _ _ _ _ _} _ : assert.
#[global] Arguments of_val {_}.
#[global] Arguments to_val {_}.
#[global] Arguments head_step {_}.
#[global] Hint Extern 0 (Empty _) => refine (ectx_language_empty _); shelve
: typeclass_instances.
#[global] Hint Extern 0 (Op _) => refine (ectx_language_op _); shelve
: typeclass_instances.
#[global] Hint Extern 0 (Fill _ _) => refine (ectx_language_fill _); shelve
: typeclass_instances.

Section ectx_language.
  Context {Λ : ectx_language}.

  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types K : ectx Λ.

  Inductive prim_step prog e1 σ1 e2 σ2 : Prop :=
    | fill_head_step_prim_step K e1' e2' :
        e1 = K @@ e1' →
        e2 = K @@ e2' →
        head_step prog e1' σ1 e2' σ2 →
        prim_step prog e1 σ1 e2 σ2.

  Definition sub_redexes_are_values e :=
    ∀ K e',
    e = K @@ e' →
    to_val e' = None →
    K = ∅.

  Definition head_reducible prog e σ :=
    ∃ e' σ', head_step prog e σ e' σ'.
  Definition strongly_head_reducible prog e :=
    ∀ σ, head_reducible prog e σ.
  Definition head_irreducible prog e σ :=
    ∀ e' σ', ¬ head_step prog e σ e' σ'.
  Definition strongly_head_irreducible prog e :=
    ∀ σ, head_irreducible prog e σ.
  Definition head_stuck prog e σ :=
    to_val e = None ∧ head_irreducible prog e σ.
  Definition strongly_head_stuck prog e :=
    strongly_head_irreducible prog e ∧ to_val e = None ∧ sub_redexes_are_values e.

  Record pure_head_step prog e1 e2 := {
    pure_head_step_safe σ1 :
      head_reducible prog e1 σ1 ;
    pure_head_step_det σ1 e2' σ2 :
      head_step prog e1 σ1 e2' σ2 →
      σ2 = σ1 ∧ e2' = e2 ;
  }.

  Class IsStronglyHeadStuck prog (ϕ : Prop) e :=
    is_strongly_head_stuck : ϕ → strongly_head_stuck prog e.
  Class PureHeadExec prog n (ϕ : Prop) e1 e2 :=
    pure_head_exec_pure_head_steps : ϕ → nsteps (pure_head_step prog) n e1 e2.

  Lemma head_step_not_val prog e1 σ1 e2 σ2 :
    head_step prog e1 σ1 e2 σ2 →
    to_val e1 = None.
  Proof.
    apply ectx_language_mixin.
  Qed.
  Lemma fill_empty e :
    ∅ @@ e = e.
  Proof.
    apply ectx_language_mixin.
  Qed.
  Lemma fill_op K1 K2 e :
    K1 @@ K2 @@ e = (K1 ⋅ K2) @@ e.
  Proof.
    apply ectx_language_mixin.
  Qed.
  #[global] Instance fill_inj K :
    Inj (=) (=) (K @@.).
  Proof.
    apply ectx_language_mixin.
  Qed.
  Lemma fill_not_val K e :
    to_val e = None →
    to_val (K @@ e) = None.
  Proof.
    apply ectx_language_mixin.
  Qed.
  Lemma fill_redex prog K K_redex e1 e1_redex σ1 e2 σ2 :
    K @@ e1 = K_redex @@ e1_redex →
    to_val e1 = None →
    head_step prog e1_redex σ1 e2 σ2 →
    ∃ K', K_redex = K ⋅ K'.
  Proof.
    apply ectx_language_mixin.
  Qed.
  Lemma fill_head_step_val prog K e σ1 e2 σ2 :
    head_step prog (K @@ e) σ1 e2 σ2 →
    is_Some (to_val e) ∨ K = ∅.
  Proof.
    apply ectx_language_mixin.
  Qed.

  Lemma language_of_ectx_language_mixin :
    LanguageMixin (@of_val Λ) to_val prim_step.
  Proof.
    split.
    - apply ectx_language_mixin.
    - apply ectx_language_mixin.
    - intros * [? ? ? -> -> ?%head_step_not_val]. apply fill_not_val. done.
  Qed.
  Canonical language_of_ectx_language' :=
    Build_language language_of_ectx_language_mixin.

  Lemma head_step_prim_step prog e1 σ1 e2 σ2 :
    head_step prog e1 σ1 e2 σ2 →
    prim_step prog e1 σ1 e2 σ2.
  Proof.
    econstructor; eauto using fill_empty.
  Qed.
  Lemma prim_step_fill_prim_step prog K e1 σ1 e2 σ2 :
    prim_step prog e1 σ1 e2 σ2 →
    prim_step prog (K @@ e1) σ1 (K @@ e2) σ2.
  Proof.
    intros []. simplify.
    eauto using fill_head_step_prim_step, fill_op.
  Qed.

  Lemma fill_val K e :
    is_Some (to_val (K @@ e)) →
    is_Some (to_val e).
  Proof.
    rewrite -!not_eq_None_Some. eauto using fill_not_val.
  Qed.
  Lemma fill_prim_step_inv prog K e1' σ1 e2 σ2 :
    to_val e1' = None →
    prim_step prog (K @@ e1') σ1 e2 σ2 →
    ∃ e2', e2 = K @@ e2' ∧ prim_step prog e1' σ1 e2' σ2.
  Proof.
    intros ? [K_redex e1_redex e2_redex Heq -> Hstep].
    edestruct fill_redex as [K' ?]; eauto; simplify.
    rewrite -fill_op in Heq; apply (inj (_ @@.)) in Heq.
    eexists. rewrite -fill_op. eauto using prim_step.
  Qed.

  Lemma reducible_fill_reducible prog K e σ :
    reducible prog e σ →
    reducible prog (K @@ e) σ.
  Proof.
    intros (? & ? & ?). do 2 eexists. eapply prim_step_fill_prim_step. eauto.
  Qed.
  Lemma reducible_fill_prim_step prog K e1 σ1 e2 σ2 :
    reducible prog e1 σ1 →
    prim_step prog (K @@ e1) σ1 e2 σ2 →
    ∃ e2', e2 = K @@ e2' ∧ prim_step prog e1 σ1 e2' σ2.
  Proof.
    intros Hreducible.
    eapply fill_prim_step_inv, reducible_not_val. done.
  Qed.

  Lemma head_irreducible_not_head_reducible prog e σ :
    head_irreducible prog e σ ↔
    ¬ head_reducible prog e σ.
  Proof.
    rewrite /head_reducible /head_irreducible. naive_solver.
  Qed.
  Lemma head_reducible_fill_reducible prog K e σ :
    head_reducible prog e σ →
    reducible prog (K @@ e) σ.
  Proof.
    intros (? & ? & ?). do 2 eexists. eapply fill_head_step_prim_step; eauto.
  Qed.
  Lemma head_reducible_reducible prog e σ :
    head_reducible prog e σ →
    reducible prog e σ.
  Proof.
    rewrite -{2}(fill_empty e). eauto using head_reducible_fill_reducible.
  Qed.
  Lemma reducible_head_reducible prog e σ :
    reducible prog e σ →
    sub_redexes_are_values e →
    head_reducible prog e σ.
  Proof.
    intros (? & ? & []) ?. simplify.
    assert (K = ∅) as -> by eauto using head_step_not_val.
    rewrite fill_empty /head_reducible; eauto.
  Qed.
  Lemma head_irreducible_irreducible prog e σ :
    head_irreducible prog e σ →
    sub_redexes_are_values e →
    irreducible prog e σ.
  Proof.
    rewrite irreducible_not_reducible head_irreducible_not_head_reducible.
    eauto using reducible_head_reducible.
  Qed.
  Lemma head_reducible_fill_prim_step prog K e1 σ1 e2 σ2 :
    head_reducible prog e1 σ1 →
    prim_step prog (K @@ e1) σ1 e2 σ2 →
    ∃ e2', e2 = K @@ e2' ∧ head_step prog e1 σ1 e2' σ2.
  Proof.
    intros (? & ? & Hstep) [K' e1' e2' Heq -> Hstep'].
    edestruct fill_redex as [K'' ?]; eauto using head_step_not_val.
    simplify. rewrite -fill_op in Heq. simplify.
    exists (K'' @@ e2'). rewrite fill_op; split; first done.
    apply fill_head_step_val in Hstep as [[v ?] | ?].
    { apply head_step_not_val in Hstep'. simplify. }
    simplify. by rewrite !fill_empty.
  Qed.
  Lemma head_reducible_prim_step prog e1 σ1 e2 σ2 :
    head_reducible prog e1 σ1 →
    prim_step prog e1 σ1 e2 σ2 →
    head_step prog e1 σ1 e2 σ2.
  Proof.
    intros.
    edestruct (head_reducible_fill_prim_step prog ∅) as (? & ? & ?); rewrite ?fill_empty //.
    simplify. rewrite fill_empty //.
  Qed.

  Lemma strongly_head_reducible_strongly_reducible prog e :
    strongly_head_reducible prog e →
    strongly_reducible prog e.
  Proof.
    intros ? ?. eauto using head_reducible_reducible.
  Qed.
  Lemma strongly_head_irreducible_strongly_irreducible prog e :
    strongly_head_irreducible prog e →
    sub_redexes_are_values e →
    strongly_irreducible prog e.
  Proof.
    intros ** ?. eauto using head_irreducible_irreducible.
  Qed.
  Lemma strongly_head_stuck_strongly_stuck prog e :
    strongly_head_stuck prog e →
    strongly_stuck prog e.
  Proof.
    intros (? & ? & ?). esplit; last done.
    eauto using strongly_head_irreducible_strongly_irreducible.
  Qed.
  #[global] Instance is_strongly_head_stuck_is_strongly_stuck prog ϕ e :
    IsStronglyHeadStuck prog ϕ e →
    IsStronglyStuck prog ϕ e.
  Proof.
    intros Hstrongly_head_stuck Hϕ.
    apply strongly_head_stuck_strongly_stuck, is_strongly_head_stuck. done.
  Qed.

  #[global] Instance fill_language_ctx K :
    LanguageCtx (K @@.).
  Proof.
    split; simpl.
    - apply ectx_language_mixin.
    - eauto using prim_step_fill_prim_step.
    - eauto using fill_prim_step_inv.
  Qed.

  Lemma pure_head_step_fill_pure_step prog K e1 e2 :
    pure_head_step prog e1 e2 →
    pure_step prog (K @@ e1) (K @@ e2).
  Proof.
    intros []. split.
    - eauto using head_reducible_fill_reducible.
    - intros * ?%head_reducible_fill_prim_step; naive_solver.
  Qed.
  Lemma pure_head_step_pure_step prog e1 e2 :
    pure_head_step prog e1 e2 →
    pure_step prog e1 e2.
  Proof.
    intros. rewrite -(fill_empty e1) -(fill_empty e2).
    eauto using pure_head_step_fill_pure_step.
  Qed.

  Lemma pure_head_steps_pure_head_exec prog n e1 e2 :
    nsteps (pure_head_step prog) n e1 e2 →
    PureHeadExec prog n True e1 e2.
  Proof.
    intros ? ?. done.
  Qed.
  Lemma pure_head_step_pure_head_exec prog e1 e2 :
    pure_head_step prog e1 e2 →
    PureHeadExec prog 1 True e1 e2.
  Proof.
    intros. eapply pure_head_steps_pure_head_exec, nsteps_once. done.
  Qed.
  Lemma pure_head_exec_pure_head_step prog ϕ e1 e2 :
    PureHeadExec prog 1 ϕ e1 e2 →
    ϕ →
    pure_head_step prog e1 e2.
  Proof.
    intros. apply nsteps_once_inv, pure_head_exec_pure_head_steps. done.
  Qed.
  Lemma pure_exec_fill_pure_exec prog K n ϕ e1 e2 :
    PureExec prog n ϕ e1 e2 →
    PureExec prog n ϕ (K @@ e1) (K @@ e2).
  Proof.
    apply language_ctx_pure_exec, _.
  Qed.
  Lemma pure_head_exec_fill_pure_exec prog K n ϕ e1 e2 :
    PureHeadExec prog n ϕ e1 e2 →
    PureExec prog n ϕ (K @@ e1) (K @@ e2).
  Proof.
    intros ? ?.
    eapply nsteps_congruence;
    eauto using pure_head_exec_pure_head_steps, pure_head_step_fill_pure_step.
  Qed.
  #[global] Instance pure_head_exec_pure_exec prog n ϕ e1 e2 :
    PureHeadExec prog n ϕ e1 e2 →
    PureExec prog n ϕ e1 e2.
  Proof.
    intros. rewrite -(fill_empty e1) -(fill_empty e2).
    eauto using pure_head_exec_fill_pure_exec.
  Qed.
End ectx_language.

#[global] Arguments language_of_ectx_language' : clear implicits.
Coercion language_of_ectx_language' : ectx_language >-> language.

Definition language_of_ectx_language '(Build_ectx_language mixin) : language :=
  Eval compute in Build_ectx_language mixin.
#[global] Arguments language_of_ectx_language : simpl never.
