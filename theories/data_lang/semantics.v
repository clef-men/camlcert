From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  syntax.
From camlcert Require Import
  options.

Implicit Types b : bool.
Implicit Types l : loc.
Implicit Types func : data_function.
Implicit Types annot : data_annotation.
Implicit Types tag : data_tag.
Implicit Types idx : data_index.
Implicit Types v w : data_val.
Implicit Types e : data_expr.
Implicit Types prog : data_program.

Definition data_state :=
  gmap loc data_val.
Implicit Types σ : data_state.

#[global] Instance data_state_eq_dec :
  EqDecision data_state.
Proof.
  solve_decision.
Defined.
#[global] Instance data_state_inhabited :
  Inhabited data_state.
Proof.
  apply _.
Qed.

Definition data_unop_eval op v :=
  match op, v with
  | DataNeg, DataBool b =>
      Some (DataBool (negb b))
  | DataUminus, DataInt n =>
      Some (DataInt (- n))
  | _, _ =>
      None
  end.
#[global] Arguments data_unop_eval !_ !_ / : assert.

Definition data_binop_eval_int op n1 n2 :=
  match op with
  | DataPlus =>
      Some (DataInt (n1 + n2))
  | DataMinus =>
      Some (DataInt (n1 - n2))
  | DataMult =>
      Some (DataInt (n1 * n2))
  | DataQuot =>
      Some (DataInt (n1 `quot` n2))
  | DataRem =>
      Some (DataInt (n1 `rem` n2))
  | DataLe =>
      Some (DataBool (bool_decide (n1 ≤ n2)%Z))
  | DataLt =>
      Some (DataBool (bool_decide (n1 < n2)%Z))
  | DataGe =>
      Some (DataBool (bool_decide (n1 >= n2)%Z))
  | DataGt =>
      Some (DataBool (bool_decide (n1 > n2)%Z))
  | _ =>
      None
  end.
#[global] Arguments data_binop_eval_int !_ _ _ / : assert.

Definition data_binop_eval op v1 v2 :=
  match op with
  | DataEq =>
      Some (DataBool (bool_decide (v1 = v2)))
  | DataNe =>
      Some (DataBool (bool_decide (v1 ≠ v2)))
  | _ =>
      match v1, v2 with
      | DataInt n1, DataInt n2 =>
          data_binop_eval_int op n1 n2
      | _, _ =>
          None
      end
  end.
#[global] Arguments data_binop_eval !_ !_ !_ / : assert.

Inductive data_head_step prog : data_expr → data_state → data_expr → data_state → Prop :=
  | data_head_step_let v e e' σ :
      e' = e.[DataVal v/] →
      data_head_step prog
        (DataLet (DataVal v) e)
        σ
        e'
        σ
  | data_head_step_call func def annot v e e' σ :
      prog !! func = Some def →
      e = def.(data_definition_body) →
      e' = e.[DataVal v/] →
      data_head_step prog
        (DataCall (DataVal $ DataFunc func annot) (DataVal v))
        σ
        e'
        σ
  | data_head_step_unop op v v' σ :
      data_unop_eval op v = Some v' →
      data_head_step prog
        (DataUnop op (DataVal v))
        σ
        (DataVal v')
        σ
  | data_head_step_binop_1 op e1 e2 e' σ :
      e' = DataLet e1 $ DataLet e2.[ren (+1)] $ DataBinopDet op (DataVar 1) (DataVar 0) →
      data_head_step prog
        (DataBinop op e1 e2)
        σ
        e'
        σ
  | data_head_step_binop_2 op e1 e2 e' σ :
      e' = DataLet e2 $ DataLet e1.[ren (+1)] $ DataBinopDet op (DataVar 0) (DataVar 1) →
      data_head_step prog
        (DataBinop op e1 e2)
        σ
        e'
        σ
  | data_head_step_binop_det op v1 v2 v' σ :
      data_binop_eval op v1 v2 = Some v' →
      data_head_step prog
        (DataBinopDet op (DataVal v1) (DataVal v2))
        σ
        (DataVal v')
        σ
  | data_head_step_if b e1 e2 σ :
      data_head_step prog
        (DataIf (DataVal $ DataBool b) e1 e2)
        σ
        (if b then e1 else e2)
        σ
  | data_head_step_block_1 tag e1 e2 e' σ :
      e' = DataLet e1 $ DataLet e2.[ren (+1)] $ DataBlockDet tag (DataVar 1) (DataVar 0) →
      data_head_step prog
        (DataBlock tag e1 e2)
        σ
        e'
        σ
  | data_head_step_block_2 tag e1 e2 e' σ :
      e' = DataLet e2 $ DataLet e1.[ren (+1)] $ DataBlockDet tag (DataVar 0) (DataVar 1) →
      data_head_step prog
        (DataBlock tag e1 e2)
        σ
        e'
        σ
  | data_head_step_block_det tag v1 v2 σ l :
      σ !! (l +ₗ 0) = None →
      σ !! (l +ₗ 1) = None →
      σ !! (l +ₗ 2) = None →
      data_head_step prog
        (DataBlockDet tag (DataVal v1) (DataVal v2))
        σ
        (DataVal $ DataLoc l)
        (<[l +ₗ 2 := v2]> (<[l +ₗ 1 := v1]> (<[l +ₗ 0 := DataTag tag]> σ)))
  | data_head_step_load l l' idx v σ :
      σ !! (l +ₗ idx) = Some v →
      data_head_step prog
        (DataLoad (DataVal $ DataLoc l) (DataVal $ DataIndex idx))
        σ
        (DataVal v)
        σ
  | data_head_step_store l idx v w σ :
      σ !! (l +ₗ idx) = Some v →
      data_head_step prog
        (DataStore (DataVal $ DataLoc l) (DataVal $ DataIndex idx) (DataVal w))
        σ
        (DataVal DataUnit)
        (<[l +ₗ idx := w]> σ).

Lemma data_head_step_block_det' prog tag v1 v2 σ σ' :
  let l := loc_fresh (dom σ) in
  σ' = <[l +ₗ 2 := v2]> (<[l +ₗ 1 := v1]> (<[l +ₗ 0 := DataTag tag]> σ)) →
  data_head_step prog
    (DataBlockDet tag (DataVal v1) (DataVal v2))
    σ
    (DataVal $ DataLoc l)
    σ'.
Proof.
  intros l ->.
  apply data_head_step_block_det;
    rewrite -not_elem_of_dom;
    apply loc_fresh_fresh; lia.
Qed.

Lemma data_head_step_not_val prog e1 σ1 e2 σ2 :
  data_head_step prog e1 σ1 e2 σ2 →
  data_to_val e1 = None.
Proof.
  destruct 1; naive_solver.
Qed.

Inductive data_ectxi :=
  | DataEctxiLet e2
  | DataEctxiCall1 e1
  | DataEctxiCall2 v2
  | DataEctxiUnop (op : data_unop)
  | DataEctxiIf e1 e2
  | DataEctxiLoad1 e1
  | DataEctxiLoad2 v2
  | DataEctxiStore1 e1 e2
  | DataEctxiStore2 e1 v3
  | DataEctxiStore3 v2 v3.

Definition data_ectxi_fill k e :=
  match k with
  | DataEctxiLet e2 =>
      DataLet e e2
  | DataEctxiCall1 e1 =>
      DataCall e1 e
  | DataEctxiCall2 v2 =>
      DataCall e (DataVal v2)
  | DataEctxiUnop op =>
      DataUnop op e
  | DataEctxiIf e1 e2 =>
      DataIf e e1 e2
  | DataEctxiLoad1 e1 =>
      DataLoad e1 e
  | DataEctxiLoad2 v2 =>
      DataLoad e (DataVal v2)
  | DataEctxiStore1 e1 e2 =>
      DataStore e1 e2 e
  | DataEctxiStore2 e1 v3 =>
      DataStore e1 e (DataVal v3)
  | DataEctxiStore3 v2 v3 =>
      DataStore e (DataVal v2) (DataVal v3)
  end.
#[global] Arguments data_ectxi_fill !_ _ / : assert.
#[global] Instance data_ectxi_fill_ : Fill data_ectxi data_expr :=
  Build_Fill data_ectxi_fill.

#[global] Instance data_ectxi_fill_inj k :
  Inj (=) (=) (k @@.).
Proof.
  induction k; intros ?*; naive_solver.
Qed.
Lemma data_ectxi_fill_val k e :
  is_Some (data_to_val (k @@ e)) →
  is_Some (data_to_val e).
Proof.
  intros (v & ?). destruct k; done.
Qed.
Lemma data_ectxi_fill_not_val k e :
  data_to_val e = None →
  data_to_val (k @@ e) = None.
Proof.
  destruct k; done.
Qed.
Lemma data_ectxi_fill_no_val_inj k1 e1 k2 e2 :
  data_to_val e1 = None →
  data_to_val e2 = None →
  k1 @@ e1 = k2 @@ e2 →
  k1 = k2.
Proof.
  destruct k1, k2; naive_solver.
Qed.
Lemma data_ectxi_fill_head_step_val prog k e σ1 e2 σ2 :
  data_head_step prog (k @@ e) σ1 e2 σ2 →
  is_Some (data_to_val e).
Proof.
  destruct k; inversion_clear 1; done.
Qed.

Definition data_ectx :=
  list data_ectxi.
