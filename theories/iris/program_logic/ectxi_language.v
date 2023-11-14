From simuliris Require Import
  prelude.
From simuliris.iris.program_logic Require Export
  ectx_language.

Section EctxiLanguageMixin.
  Context {expr val program state : Type}.
  Context (of_val : val → expr).
  Context (to_val : expr → option val).
  Context (head_step : program → expr → state → expr → state → Prop).
  Context (ectxi : Type) `{!Fill ectxi expr}.

  Record EctxiLanguageMixin := {
    ectxi_language_mixin_to_of_val e v :
      e = of_val v →
      to_val e = Some v ;
    ectxi_language_mixin_of_to_val e v :
      to_val e = Some v →
      of_val v = e ;
    ectxi_language_mixin_head_step_not_val prog e1 σ1 e2 σ2 :
      head_step prog e1 σ1 e2 σ2 →
      to_val e1 = None ;

    ectxi_language_mixin_fill_item_inj k :
      Inj (=) (=) (k @@.) ;
    ectxi_language_mixin_fill_item_not_val k e :
      to_val e = None →
      to_val (k @@ e) = None ;

    ectxi_language_mixin_fill_item_no_val_inj k1 e1 k2 e2 :
      to_val e1 = None →
      to_val e2 = None →
      k1 @@ e1 = k2 @@ e2 →
      k1 = k2 ;
    ectxi_language_mixin_fill_item_head_step_val prog k e1 σ1 e2 σ2 :
      head_step prog (k @@ e1) σ1 e2 σ2 →
      is_Some (to_val e1) ;
  }.
End EctxiLanguageMixin.
#[global] Arguments Build_EctxiLanguageMixin {_ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ : assert.

Structure ectxi_language := {
  expr : Type ;
  val : Type ;
  program : Type ;
  state : Type ;
  of_val : val → expr ;
  to_val : expr → option val ;
  head_step : program → expr → state → expr → state → Prop ;

  ectxi : Type ;
  ectxi_language_fill_item : Fill ectxi expr ;

  ectxi_language_mixin : EctxiLanguageMixin of_val to_val head_step ectxi ;
}.
#[global] Arguments Build_ectxi_language {_ _ _ _ _ _ _ _ _} _ : assert.
#[global] Arguments of_val {_}.
#[global] Arguments to_val {_}.
#[global] Arguments head_step {_}.
#[global] Hint Extern 0 (Fill _ _) => refine (ectxi_language_fill_item _); shelve
: typeclass_instances.

Section ectxi_language.
  Context {Λ : ectxi_language}.

  Notation ectx :=
    (list (ectxi Λ)).

  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.
  Implicit Types σ : state Λ.
  Implicit Types k : ectxi Λ.
  Implicit Types K : ectx.

  #[global] Instance fill_item_inj k :
    Inj (=) (=) (k @@.).
  Proof.
    apply ectxi_language_mixin.
  Qed.
  Lemma fill_item_not_val k e :
    to_val e = None →
    to_val (k @@ e) = None.
  Proof.
    apply ectxi_language_mixin.
  Qed.
  Lemma fill_item_no_val_inj k1 k2 e1 e2 :
    to_val e1 = None →
    to_val e2 = None →
    k1 @@ e1 = k2 @@ e2 →
    k1 = k2.
  Proof.
    apply ectxi_language_mixin.
  Qed.
  Lemma fill_item_head_step_val prog k e σ1 e2 σ2 :
    head_step prog (k @@ e) σ1 e2 σ2 →
    is_Some (to_val e).
  Proof.
    apply ectxi_language_mixin.
  Qed.

  Lemma fill_item_val k e :
    is_Some (to_val (k @@ e)) →
    is_Some (to_val e).
  Proof.
    rewrite -!not_eq_None_Some. eauto using fill_item_not_val.
  Qed.

  #[local] Instance ectxi_language_empty : Empty ectx :=
    [].
  #[local] Instance ectxi_language_op : Op ectx :=
    flip (++).
  #[local] Instance ectxi_language_fill : Fill ectx (expr Λ) :=
    Build_Fill $ fold_left (flip (@@)).

  Lemma ectx_language_of_ectxi_language_mixin :
    EctxLanguageMixin of_val to_val head_step ectx.
  Proof.
    Arguments fill {_ _ _} _ _ / : assert.
    assert (fill_op : ∀ K1 K2 e,
      (K1 ⋅ K2) @@ e = K1 @@ K2 @@ e
    ). {
      simpl. eauto using fold_left_app.
    }
    assert (fill_not_val : ∀ K e,
      to_val e = None →
      to_val (K @@ e) = None
    ). {
      induction K; naive_solver eauto using fill_item_not_val.
    }
    assert (fill_head_step_val : ∀ prog K e1 σ1 e2 σ2,
      head_step prog (K @@ e1) σ1 e2 σ2 →
      is_Some (to_val e1) ∨ K = ∅
    ). {
      induction K as [| k K]; intros * Hstep; first auto.
      left. edestruct (IHK (k @@ e1)); first done.
      + eapply fill_item_val. done.
      + simplify. eapply fill_item_head_step_val. done.
    }
    split; try done || apply ectxi_language_mixin.
    - induction K as [| k K]; intros ?**; first done.
      apply (inj (k @@.)); auto using fill_item_inj.
    - intros * Heq ? Hstep. revert K_redex Heq.
      induction K as [| k K] using rev_ind; intros K_redex Heq.
      + naive_solver eauto using app_nil_r.
      + destruct K_redex as [| k_redex K_redex _] using rev_ind; intros.
        * cbn in Heq. simplify. eapply fill_head_step_val in Hstep as [].
          -- exfalso. eapply eq_None_not_Some; done.
          -- exists ∅. done.
        * rewrite !fill_op in Heq.
          assert (k = k_redex) as ->.
          { apply fill_item_no_val_inj in Heq; eauto.
            apply fill_not_val. eapply ectxi_language_mixin. done.
          }
          simplify. destruct IHK with (K_redex := K_redex) as [K' ->]; first done.
          exists K'. setoid_rewrite app_assoc. done.
  Qed.
  Canonical ectx_language_of_ectxi_language' :=
    Build_ectx_language ectx_language_of_ectxi_language_mixin.
  Canonical language_of_ectxi_language' :=
    language_of_ectx_language ectx_language_of_ectxi_language'.
End ectxi_language.

#[global] Arguments ectx_language_of_ectxi_language' : clear implicits.
Coercion ectx_language_of_ectxi_language' : ectxi_language >-> ectx_language.

#[global] Arguments language_of_ectxi_language' : clear implicits.
Coercion language_of_ectxi_language' : ectxi_language >-> language.

Definition ectx_language_of_ectxi_language '(Build_ectxi_language mixin) : ectx_language :=
  Eval compute -[ectxi_language_empty ectxi_language_op ectxi_language_fill] in
  Build_ectxi_language mixin.
#[global] Arguments ectx_language_of_ectxi_language : simpl never.
