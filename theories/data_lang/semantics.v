From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  syntax.
From simuliris.data_lang Require Import
  notations.

Definition data_state := gmap loc data_val.

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

Implicit Types b : bool.
Implicit Types l : loc.
Implicit Types func : data_function.
Implicit Types annot : data_annotation.
Implicit Types tag : data_tag.
Implicit Types idx : data_index.
Implicit Types v w : data_val.
Implicit Types e : data_expr.
Implicit Types prog : data_program.
Implicit Types σ : data_state.

Definition data_unop_eval op v :=
  match op, v with
  | DataOpNeg, DataBool b =>
      Some (DataBool (negb b))
  | DataOpUminus, DataInt n =>
      Some (DataInt (- n))
  | _, _ =>
      None
  end.
#[global] Arguments data_unop_eval !_ !_ / : assert.

Definition data_binop_eval_int op n1 n2 :=
  match op with
  | DataOpPlus =>
      Some (DataInt (n1 + n2))
  | DataOpMinus =>
      Some (DataInt (n1 - n2))
  | DataOpMult =>
      Some (DataInt (n1 * n2))
  | DataOpQuot =>
      Some (DataInt (n1 `quot` n2))
  | DataOpRem =>
      Some (DataInt (n1 `rem` n2))
  | DataOpLe =>
      Some (DataBool (bool_decide (n1 ≤ n2)%Z))
  | DataOpLt =>
      Some (DataBool (bool_decide (n1 < n2)%Z))
  | DataOpGe =>
      Some (DataBool (bool_decide (n1 >= n2)%Z))
  | DataOpGt =>
      Some (DataBool (bool_decide (n1 > n2)%Z))
  | DataOpEq =>
      Some (DataBool (bool_decide (n1 = n2)%Z))
  | DataOpNe =>
      Some (DataBool (bool_decide (n1 ≠ n2)%Z))
  end.
#[global] Arguments data_binop_eval_int !_ _ _ / : assert.

Definition data_binop_eval_bool op b1 b2 :=
  match op with
  | DataOpEq =>
      Some (DataBool (bool_decide (b1 = b2)))
  | DataOpNe =>
      Some (DataBool (bool_decide (b1 ≠ b2)))
  | _ =>
      None
  end.
#[global] Arguments data_binop_eval_bool !_ _ _ / : assert.

Definition data_binop_eval_function op func1 func2 :=
  match op with
  | DataOpEq =>
      Some (DataBool (bool_decide (func1 = func2)))
  | DataOpNe =>
      Some (DataBool (bool_decide (func1 ≠ func2)))
  | _ =>
      None
  end.
#[global] Arguments data_binop_eval_function !_ _ _ / : assert.

Definition data_binop_eval op v1 v2 :=
  match v1, v2 with
  | DataInt n1, DataInt n2 =>
      data_binop_eval_int op n1 n2
  | DataBool b1, DataBool b2 =>
      data_binop_eval_bool op b1 b2
  | DataFunc func1 _, DataFunc func2 _ =>
      data_binop_eval_function op func1 func2
  | _, _ =>
      None
  end.
#[global] Arguments data_binop_eval !_ !_ !_ / : assert.

Inductive data_head_step prog : data_expr → data_state → data_expr → data_state → Prop :=
  | data_head_step_let v e e' σ :
      e' = e.[#v/] →
      data_head_step prog
        (let: v in e) σ
        e' σ
  | data_head_step_call func annot v e e' σ :
      prog !! func = Some e →
      e' = e.[#v/] →
      data_head_step prog
        ((DataFunc func annot) v) σ
        e' σ
  | data_head_step_unop op v v' σ :
      data_unop_eval op v = Some v' →
      data_head_step prog
        (DataUnop op v) σ
        v' σ
  | data_head_step_binop_1 op e1 e2 e' σ :
      e' = (let: e1 in let: e2.[ren (+1)] in DataBinopDet op $1 $0)%data_expr →
      data_head_step prog
        (DataBinop op e1 e2) σ
        e' σ
  | data_head_step_binop_2 op e1 e2 e' σ :
      e' = (let: e2 in let: e1.[ren (+1)] in DataBinopDet op $0 $1)%data_expr →
      data_head_step prog
        (DataBinop op e1 e2) σ
        e' σ
  | data_head_step_binop_det op v1 v2 v' σ :
      data_binop_eval op v1 v2 = Some v' →
      data_head_step prog
        (DataBinopDet op v1 v2) σ
        v' σ
  | data_head_step_if b e1 e2 σ :
      data_head_step prog
        (if: b then e1 else e2) σ
        (if b then e1 else e2) σ
  | data_head_step_constr_1 tag e1 e2 e' σ :
      e' = (let: e1 in let: e2.[ren (+1)] in &&tag $1 $0)%data_expr →
      data_head_step prog
        (&tag e1 e2) σ
        e' σ
  | data_head_step_constr_2 tag e1 e2 e' σ :
      e' = (let: e2 in let: e1.[ren (+1)] in &&tag $0 $1)%data_expr →
      data_head_step prog
        (&tag e1 e2) σ
        e' σ
  | data_head_step_constr_det tag v1 v2 σ l :
      σ !! (l +ₗ 0) = None →
      σ !! (l +ₗ 1) = None →
      σ !! (l +ₗ 2) = None →
      data_head_step prog
        (&&tag v1 v2) σ
        l (<[l +ₗ 2 := v2]> (<[l +ₗ 1 := v1]> (<[l +ₗ 0 := DataTag tag]> σ)))
  | data_head_step_load l l' idx v σ :
      σ !! (l +ₗ idx) = Some v →
      data_head_step prog
        (![idx] l) σ
        v σ
  | data_head_step_store l idx v w σ :
      σ !! (l +ₗ idx) = Some v →
      data_head_step prog
        (l <-[idx]- w) σ
        #() (<[l +ₗ idx := w]> σ).

Lemma data_head_step_constr_det' prog tag v1 v2 σ σ' :
  let l := loc_fresh (dom σ) in
  σ' = <[l +ₗ 2 := v2]> (<[l +ₗ 1 := v1]> (<[l +ₗ 0 := DataTag tag]> σ)) →
  data_head_step prog
    (&&tag v1 v2) σ
    l σ'.
Proof.
  intros l ->.
  apply data_head_step_constr_det;
    rewrite -not_elem_of_dom;
    apply loc_fresh_fresh; lia.
Qed.
