From iris.bi Require Import
  bi.
From iris.base_logic Require Import
  bi.

From simuliris Require Import
  prelude.

Section Satisfiable.
  Context `{!BiBUpd PROP} `{!BiAffine PROP}.
  Implicit Types P Q : PROP.

  Class Satisfiable (sat : PROP → Prop) := {
    satisfiable_mono P Q :
      (P ⊢ Q) →
      sat P → sat Q ;
    satisfiable_elim φ :
      sat (⌜φ⌝)%I →
      φ ;
    satisfiable_bupd P :
      sat (|==> P)%I →
      sat P ;
    satisfiable_exists `(Φ : X → PROP) :
      sat (∃ x, Φ x)%I →
      ∃ x, sat (Φ x) ;
  }.

  Section derived_lemmas.
    Context `{!Satisfiable sat}.
    Arguments sat _%I.

    #[global] Instance satisfiable_entails :
      Proper ((⊢) ==> impl) sat.
    Proof.
      intros P1 P2 HP HP1. eapply satisfiable_mono; done.
    Qed.
    #[global] Instance satisfiable_equiv :
      Proper ((≡) ==> iff) sat.
    Proof.
      intros P1 P2 HP.
      split; intros HP1;
        eauto using satisfiable_mono, bi.equiv_entails_1_1, bi.equiv_entails_1_2.
    Qed.

    Lemma satisfiable_sep P Q :
      sat (P ∗ Q) →
      sat P ∧ sat Q.
    Proof.
      intros Hsat. split; (eapply satisfiable_mono; last done);
        auto using bi.sep_elim_l, bi.sep_elim_r with typeclass_instances.
    Qed.
    Lemma satisfiable_and P Q :
      sat (P ∧ Q) →
      sat P ∧ sat Q.
    Proof.
      intros Hsat. split; (eapply satisfiable_mono; last done);
        auto using bi.and_elim_l, bi.and_elim_r.
    Qed.
    Lemma satisfiable_or P Q :
      sat (P ∨ Q) →
      sat P ∨ sat Q.
    Proof.
      rewrite bi.or_alt. intros [[] Hsat]%satisfiable_exists; auto.
    Qed.
    Lemma satisfiable_forall {X} (Φ : X → PROP) x :
      sat (∀ x, Φ x) →
      sat (Φ x).
    Proof.
      apply satisfiable_mono, bi.forall_elim.
    Qed.
    Lemma satisfiable_pers P :
      sat (<pers> P) →
      sat P.
    Proof.
      apply satisfiable_mono, bi.persistently_elim, _.
    Qed.
    Lemma satisfiable_intuitionistic P :
      sat (□ P) →
      sat P.
    Proof.
      apply satisfiable_mono, bi.intuitionistically_elim.
    Qed.
    Lemma satisfiable_impl P Q :
      (⊢ P) →
      sat (P → Q) →
      sat Q.
    Proof.
      intros HP Hsat. eapply satisfiable_mono; last done.
      setoid_rewrite <- (left_id emp%I bi_and) at 1. rewrite HP. apply bi.impl_elim_r.
    Qed.
    Lemma satisfiable_wand P Q :
      (⊢ P) →
      sat (P -∗ Q) →
      sat Q.
    Proof.
      intros HP Hsat. eapply satisfiable_mono; last done.
      setoid_rewrite <- (left_id emp%I bi_sep) at 1. rewrite HP. apply bi.wand_elim_r.
    Qed.
  End derived_lemmas.
End Satisfiable.

Section isat.
  Context {M : ucmra}.
  Implicit Types P : uPred M.

  Definition isat P :=
    ∃ x, ✓{0} x ∧ uPred_holds P 0 x.

  #[global] Instance isat_satisfiable :
    Satisfiable isat.
  Proof.
    split; unfold isat; try uPred.unseal.
    - intros P Q [H] [x [Hv HP]]; by eauto.
    - intros φ [x [_ Hφ]]. apply Hφ.
    - intros P [x [Hv HP]].
      destruct (HP 0 ε) as [y HP']; [done|by rewrite right_id|].
      revert HP'; rewrite right_id; eauto.
    - intros X Φ [x [Hv [a HΦ]]]; eauto.
  Qed.

  Lemma isat_intro P :
    (⊢ P) →
    isat P.
  Proof.
    intros HP. exists ε. split; first by apply ucmra_unit_validN.
    apply HP; first by apply ucmra_unit_validN.
    uPred.unseal. done.
  Qed.
End isat.
