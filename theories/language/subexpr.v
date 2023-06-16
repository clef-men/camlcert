From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics
  typeclasses
  relation.
From simuliris.language Require Export
  tactics.

Inductive subexprdir : expr → expr → Prop :=
  | subexprdir_let_1 e1 e2 :
      subexprdir e1 (Let e1 e2)
  | subexprdir_let_2 e1 e2 :
      subexprdir e2 (Let e1 e2)
  | subexprdir_call_1 e1 e2 :
      subexprdir e1 (Call e1 e2)
  | subexprdir_call_2 e1 e2 :
      subexprdir e2 (Call e1 e2)
  | subexprdir_unop op e :
      subexprdir e (Unop op e)
  | subexprdir_binop_1 op e1 e2 :
      subexprdir e1 (Binop op e1 e2)
  | subexprdir_binop_2 op e1 e2 :
      subexprdir e2 (Binop op e1 e2)
  | subexprdir_if_0 e0 e1 e2 :
      subexprdir e0 (If e0 e1 e2)
  | subexprdir_if_1 e0 e1 e2 :
      subexprdir e1 (If e0 e1 e2)
  | subexprdir_if_2 e0 e1 e2 :
      subexprdir e2 (If e0 e1 e2)
  | subexprdir_constr_1 constr e1 e2 :
      subexprdir e1 (Constr constr e1 e2)
  | subexprdir_constr_2 constr e1 e2 :
      subexprdir e2 (Constr constr e1 e2)
  | subexprdir_constr_det_1 constr e1 e2 :
      subexprdir e1 (ConstrDet constr e1 e2)
  | subexprdir_constr_det_2 constr e1 e2 :
      subexprdir e2 (ConstrDet constr e1 e2)
  | subexprdir_load_1 e1 e2 :
      subexprdir e1 (Load e1 e2)
  | subexprdir_load_2 e1 e2 :
      subexprdir e2 (Load e1 e2)
  | subexprdir_store_1 e1 e2 e3 :
      subexprdir e1 (Store e1 e2 e3)
  | subexprdir_store_2 e1 e2 e3 :
      subexprdir e2 (Store e1 e2 e3)
  | subexprdir_store_3 e1 e2 e3 :
      subexprdir e3 (Store e1 e2 e3).

Lemma subexprdir_wf :
  wf subexprdir.
Proof.
  intros e. induction e; constructor; intros e' He'; invert He'; done.
Qed.

Definition subexpr :=
  tc subexprdir.
#[global] Instance expr_sqsubset : SqSubset expr :=
  subexpr.

Lemma subexpr_wf :
  wf (⊏).
Proof.
  eauto using tc_wf, subexprdir_wf.
Qed.

Lemma subexprdir_subexpr e1 e2 :
  subexprdir e1 e2 →
  e1 ⊏ e2.
Proof.
  constructor. done.
Qed.

Lemma subexpr_let_1 e e1 e2 :
  e ⊏ e1 →
  e ⊏ (Let e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_let_2 e e1 e2 :
  e ⊏ e2 →
  e ⊏ (Let e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_call_1 e e1 e2 :
  e ⊏ e1 →
  e ⊏ (Call e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_call_2 e e1 e2 :
  e ⊏ e2 →
  e ⊏ (Call e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_unop e op e' :
  e ⊏ e' →
  e ⊏ (Unop op e').
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_binop_1 e op e1 e2 :
  e ⊏ e1 →
  e ⊏ (Binop op e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_binop_2 e op e1 e2 :
  e ⊏ e2 →
  e ⊏ (Binop op e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_if_0 e e0 e1 e2 :
  e ⊏ e0 →
  e ⊏ (If e0 e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_if_1 e e0 e1 e2 :
  e ⊏ e1 →
  e ⊏ (If e0 e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_if_2 e e0 e1 e2 :
  e ⊏ e2 →
  e ⊏ (If e0 e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_constr_1 e constr e1 e2 :
  e ⊏ e1 →
  e ⊏ (Constr constr e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_constr_2 e constr e1 e2 :
  e ⊏ e2 →
  e ⊏ (Constr constr e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_constr_det_1 e constr e1 e2 :
  e ⊏ e1 →
  e ⊏ (ConstrDet constr e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_constr_det_2 e constr e1 e2 :
  e ⊏ e2 →
  e ⊏ (ConstrDet constr e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_load_1 e e1 e2 :
  e ⊏ e1 →
  e ⊏ (Load e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_load_2 e e1 e2 :
  e ⊏ e2 →
  e ⊏ (Load e1 e2).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_store_1 e e1 e2 e3 :
  e ⊏ e1 →
  e ⊏ (Store e1 e2 e3).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_store_2 e e1 e2 e3 :
  e ⊏ e2 →
  e ⊏ (Store e1 e2 e3).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.
Lemma subexpr_store_3 e e1 e2 e3 :
  e ⊏ e3 →
  e ⊏ (Store e1 e2 e3).
Proof.
  intros. eapply tc_r; eauto using subexprdir.
Qed.

#[global] Hint Constructors subexprdir : language.
#[global] Hint Resolve subexprdir_subexpr : language.
#[global] Hint Resolve subexpr_let_1 | 2 : language.
#[global] Hint Resolve subexpr_let_2 | 2 : language.
#[global] Hint Resolve subexpr_call_1 | 2 : language.
#[global] Hint Resolve subexpr_call_2 | 2 : language.
#[global] Hint Resolve subexpr_unop | 2 : language.
#[global] Hint Resolve subexpr_binop_1 | 2 : language.
#[global] Hint Resolve subexpr_binop_2 | 2 : language.
#[global] Hint Resolve subexpr_if_0 | 2 : language.
#[global] Hint Resolve subexpr_if_1 | 2 : language.
#[global] Hint Resolve subexpr_if_2 | 2 : language.
#[global] Hint Resolve subexpr_constr_1 | 2 : language.
#[global] Hint Resolve subexpr_constr_2 | 2 : language.
#[global] Hint Resolve subexpr_constr_det_1 | 2 : language.
#[global] Hint Resolve subexpr_constr_det_2 | 2 : language.
#[global] Hint Resolve subexpr_load_1 | 2 : language.
#[global] Hint Resolve subexpr_load_2 | 2 : language.
#[global] Hint Resolve subexpr_store_1 | 2 : language.
#[global] Hint Resolve subexpr_store_2 | 2 : language.
#[global] Hint Resolve subexpr_store_3 | 2 : language.
