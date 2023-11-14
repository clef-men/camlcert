From simuliris Require Import
  prelude.
From simuliris.common Require Import
  relation.
From simuliris.data_lang Require Export
  tactics.

Inductive data_subexprdir : data_expr → data_expr → Prop :=
  | data_subexprdir_let_1 e1 e2 :
      data_subexprdir e1 (DataLet e1 e2)
  | data_subexprdir_let_2 e1 e2 :
      data_subexprdir e2 (DataLet e1 e2)
  | data_subexprdir_call_1 e1 e2 :
      data_subexprdir e1 (DataCall e1 e2)
  | data_subexprdir_call_2 e1 e2 :
      data_subexprdir e2 (DataCall e1 e2)
  | data_subexprdir_unop op e :
      data_subexprdir e (DataUnop op e)
  | data_subexprdir_binop_1 op e1 e2 :
      data_subexprdir e1 (DataBinop op e1 e2)
  | data_subexprdir_binop_2 op e1 e2 :
      data_subexprdir e2 (DataBinop op e1 e2)
  | data_subexprdir_binop_det_1 op e1 e2 :
      data_subexprdir e1 (DataBinopDet op e1 e2)
  | data_subexprdir_binop_det_2 op e1 e2 :
      data_subexprdir e2 (DataBinopDet op e1 e2)
  | data_subexprdir_if_0 e0 e1 e2 :
      data_subexprdir e0 (DataIf e0 e1 e2)
  | data_subexprdir_if_1 e0 e1 e2 :
      data_subexprdir e1 (DataIf e0 e1 e2)
  | data_subexprdir_if_2 e0 e1 e2 :
      data_subexprdir e2 (DataIf e0 e1 e2)
  | data_subexprdir_block_1 tag e1 e2 :
      data_subexprdir e1 (DataBlock tag e1 e2)
  | data_subexprdir_block_2 tag e1 e2 :
      data_subexprdir e2 (DataBlock tag e1 e2)
  | data_subexprdir_block_det_1 tag e1 e2 :
      data_subexprdir e1 (DataBlockDet tag e1 e2)
  | data_subexprdir_block_det_2 tag e1 e2 :
      data_subexprdir e2 (DataBlockDet tag e1 e2)
  | data_subexprdir_load_1 e1 e2 :
      data_subexprdir e1 (DataLoad e1 e2)
  | data_subexprdir_load_2 e1 e2 :
      data_subexprdir e2 (DataLoad e1 e2)
  | data_subexprdir_store_1 e1 e2 e3 :
      data_subexprdir e1 (DataStore e1 e2 e3)
  | data_subexprdir_store_2 e1 e2 e3 :
      data_subexprdir e2 (DataStore e1 e2 e3)
  | data_subexprdir_store_3 e1 e2 e3 :
      data_subexprdir e3 (DataStore e1 e2 e3).

Lemma data_subexprdir_wf :
  wf data_subexprdir.
Proof.
  intros e. induction e; constructor; intros e' He'; invert He'; done.
Qed.

Definition data_subexpr :=
  tc data_subexprdir.
#[global] Instance expr_sqsubset : SqSubset data_expr :=
  data_subexpr.

Lemma data_subexpr_wf :
  wf (⊏).
Proof.
  eauto using tc_wf, data_subexprdir_wf.
Qed.

Lemma data_subexprdir_subexpr e1 e2 :
  data_subexprdir e1 e2 →
  e1 ⊏ e2.
Proof.
  constructor. done.
Qed.

Lemma data_subexpr_let_1 e e1 e2 :
  e ⊏ e1 →
  e ⊏ (DataLet e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_let_2 e e1 e2 :
  e ⊏ e2 →
  e ⊏ (DataLet e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_call_1 e e1 e2 :
  e ⊏ e1 →
  e ⊏ (DataCall e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_call_2 e e1 e2 :
  e ⊏ e2 →
  e ⊏ (DataCall e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_unop e op e' :
  e ⊏ e' →
  e ⊏ (DataUnop op e').
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_binop_1 e op e1 e2 :
  e ⊏ e1 →
  e ⊏ (DataBinop op e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_binop_2 e op e1 e2 :
  e ⊏ e2 →
  e ⊏ (DataBinop op e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_binop_det_1 e op e1 e2 :
  e ⊏ e1 →
  e ⊏ (DataBinopDet op e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_binop_det_2 e op e1 e2 :
  e ⊏ e2 →
  e ⊏ (DataBinopDet op e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_if_0 e e0 e1 e2 :
  e ⊏ e0 →
  e ⊏ (DataIf e0 e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_if_1 e e0 e1 e2 :
  e ⊏ e1 →
  e ⊏ (DataIf e0 e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_if_2 e e0 e1 e2 :
  e ⊏ e2 →
  e ⊏ (DataIf e0 e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_block_1 e tag e1 e2 :
  e ⊏ e1 →
  e ⊏ (DataBlock tag e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_block_2 e tag e1 e2 :
  e ⊏ e2 →
  e ⊏ (DataBlock tag e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_block_det_1 e tag e1 e2 :
  e ⊏ e1 →
  e ⊏ (DataBlockDet tag e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_block_det_2 e tag e1 e2 :
  e ⊏ e2 →
  e ⊏ (DataBlockDet tag e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_load_1 e e1 e2 :
  e ⊏ e1 →
  e ⊏ (DataLoad e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_load_2 e e1 e2 :
  e ⊏ e2 →
  e ⊏ (DataLoad e1 e2).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_store_1 e e1 e2 e3 :
  e ⊏ e1 →
  e ⊏ (DataStore e1 e2 e3).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_store_2 e e1 e2 e3 :
  e ⊏ e2 →
  e ⊏ (DataStore e1 e2 e3).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.
Lemma data_subexpr_store_3 e e1 e2 e3 :
  e ⊏ e3 →
  e ⊏ (DataStore e1 e2 e3).
Proof.
  intros. eapply tc_r; eauto using data_subexprdir.
Qed.

#[global] Hint Constructors data_subexprdir : data_lang.
#[global] Hint Resolve data_subexprdir_subexpr : data_lang.
#[global] Hint Resolve data_subexpr_let_1 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_let_2 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_call_1 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_call_2 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_unop | 2 : data_lang.
#[global] Hint Resolve data_subexpr_binop_1 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_binop_2 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_binop_det_1 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_binop_det_2 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_if_0 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_if_1 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_if_2 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_block_1 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_block_2 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_block_det_1 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_block_det_2 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_load_1 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_load_2 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_store_1 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_store_2 | 2 : data_lang.
#[global] Hint Resolve data_subexpr_store_3 | 2 : data_lang.
