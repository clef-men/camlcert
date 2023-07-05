From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics
  relation.
From simuliris.lambda_lang Require Export
  tactics.

Inductive lambda_subexprdir : lambda_expr → lambda_expr → Prop :=
  | lambda_subexprdir_let_1 e1 e2 :
      lambda_subexprdir e1 (LambdaLet e1 e2)
  | lambda_subexprdir_let_2 e1 e2 :
      lambda_subexprdir e2 (LambdaLet e1 e2)
  | lambda_subexprdir_call_1 e1 e2 :
      lambda_subexprdir e1 (LambdaCall e1 e2)
  | lambda_subexprdir_call_2 e1 e2 :
      lambda_subexprdir e2 (LambdaCall e1 e2)
  | lambda_subexprdir_unop op e :
      lambda_subexprdir e (LambdaUnop op e)
  | lambda_subexprdir_binop_1 op e1 e2 :
      lambda_subexprdir e1 (LambdaBinop op e1 e2)
  | lambda_subexprdir_binop_2 op e1 e2 :
      lambda_subexprdir e2 (LambdaBinop op e1 e2)
  | lambda_subexprdir_if_0 e0 e1 e2 :
      lambda_subexprdir e0 (LambdaIf e0 e1 e2)
  | lambda_subexprdir_if_1 e0 e1 e2 :
      lambda_subexprdir e1 (LambdaIf e0 e1 e2)
  | lambda_subexprdir_if_2 e0 e1 e2 :
      lambda_subexprdir e2 (LambdaIf e0 e1 e2)
  | lambda_subexprdir_constr_1 tag e1 e2 :
      lambda_subexprdir e1 (LambdaConstr tag e1 e2)
  | lambda_subexprdir_constr_2 tag e1 e2 :
      lambda_subexprdir e2 (LambdaConstr tag e1 e2)
  | lambda_subexprdir_constr_det_1 tag e1 e2 :
      lambda_subexprdir e1 (LambdaConstrDet tag e1 e2)
  | lambda_subexprdir_constr_det_2 tag e1 e2 :
      lambda_subexprdir e2 (LambdaConstrDet tag e1 e2)
  | lambda_subexprdir_load_1 e1 e2 :
      lambda_subexprdir e1 (LambdaLoad e1 e2)
  | lambda_subexprdir_load_2 e1 e2 :
      lambda_subexprdir e2 (LambdaLoad e1 e2)
  | lambda_subexprdir_store_1 e1 e2 e3 :
      lambda_subexprdir e1 (LambdaStore e1 e2 e3)
  | lambda_subexprdir_store_2 e1 e2 e3 :
      lambda_subexprdir e2 (LambdaStore e1 e2 e3)
  | lambda_subexprdir_store_3 e1 e2 e3 :
      lambda_subexprdir e3 (LambdaStore e1 e2 e3).

Lemma lambda_subexprdir_wf :
  wf lambda_subexprdir.
Proof.
  intros e. induction e; constructor; intros e' He'; invert He'; done.
Qed.

Definition lambda_subexpr :=
  tc lambda_subexprdir.
#[global] Instance expr_sqsubset : SqSubset lambda_expr :=
  lambda_subexpr.

Lemma lambda_subexpr_wf :
  wf (⊏).
Proof.
  eauto using tc_wf, lambda_subexprdir_wf.
Qed.

Lemma lambda_subexprdir_subexpr e1 e2 :
  lambda_subexprdir e1 e2 →
  e1 ⊏ e2.
Proof.
  constructor. done.
Qed.

Lemma lambda_subexpr_let_1 e e1 e2 :
  e ⊏ e1 →
  e ⊏ (LambdaLet e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_let_2 e e1 e2 :
  e ⊏ e2 →
  e ⊏ (LambdaLet e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_call_1 e e1 e2 :
  e ⊏ e1 →
  e ⊏ (LambdaCall e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_call_2 e e1 e2 :
  e ⊏ e2 →
  e ⊏ (LambdaCall e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_unop e op e' :
  e ⊏ e' →
  e ⊏ (LambdaUnop op e').
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_binop_1 e op e1 e2 :
  e ⊏ e1 →
  e ⊏ (LambdaBinop op e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_binop_2 e op e1 e2 :
  e ⊏ e2 →
  e ⊏ (LambdaBinop op e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_if_0 e e0 e1 e2 :
  e ⊏ e0 →
  e ⊏ (LambdaIf e0 e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_if_1 e e0 e1 e2 :
  e ⊏ e1 →
  e ⊏ (LambdaIf e0 e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_if_2 e e0 e1 e2 :
  e ⊏ e2 →
  e ⊏ (LambdaIf e0 e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_constr_1 e tag e1 e2 :
  e ⊏ e1 →
  e ⊏ (LambdaConstr tag e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_constr_2 e tag e1 e2 :
  e ⊏ e2 →
  e ⊏ (LambdaConstr tag e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_constr_det_1 e tag e1 e2 :
  e ⊏ e1 →
  e ⊏ (LambdaConstrDet tag e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_constr_det_2 e tag e1 e2 :
  e ⊏ e2 →
  e ⊏ (LambdaConstrDet tag e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_load_1 e e1 e2 :
  e ⊏ e1 →
  e ⊏ (LambdaLoad e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_load_2 e e1 e2 :
  e ⊏ e2 →
  e ⊏ (LambdaLoad e1 e2).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_store_1 e e1 e2 e3 :
  e ⊏ e1 →
  e ⊏ (LambdaStore e1 e2 e3).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_store_2 e e1 e2 e3 :
  e ⊏ e2 →
  e ⊏ (LambdaStore e1 e2 e3).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.
Lemma lambda_subexpr_store_3 e e1 e2 e3 :
  e ⊏ e3 →
  e ⊏ (LambdaStore e1 e2 e3).
Proof.
  intros. eapply tc_r; eauto using lambda_subexprdir.
Qed.

#[global] Hint Constructors lambda_subexprdir : lambda_lang.
#[global] Hint Resolve lambda_subexprdir_subexpr : lambda_lang.
#[global] Hint Resolve lambda_subexpr_let_1 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_let_2 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_call_1 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_call_2 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_unop | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_binop_1 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_binop_2 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_if_0 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_if_1 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_if_2 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_constr_1 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_constr_2 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_constr_det_1 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_constr_det_2 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_load_1 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_load_2 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_store_1 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_store_2 | 2 : lambda_lang.
#[global] Hint Resolve lambda_subexpr_store_3 | 2 : lambda_lang.
