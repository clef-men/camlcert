From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  syntax.
From simuliris.lambda_lang Require Import
  notations.

Definition lambda_state := gmap loc lambda_val.

#[global] Instance lambda_state_eq_dec :
  EqDecision lambda_state.
Proof.
  solve_decision.
Defined.
#[global] Instance lambda_state_inhabited :
  Inhabited lambda_state.
Proof.
  apply _.
Qed.

Implicit Types b : bool.
Implicit Types l : loc.
Implicit Types func : lambda_function.
Implicit Types tag : lambda_tag.
Implicit Types idx : lambda_index.
Implicit Types v w : lambda_val.
Implicit Types e : lambda_expr.
Implicit Types prog : lambda_program.
Implicit Types σ : lambda_state.

Definition lambda_unop_eval op v :=
  match op, v with
  | LambdaOpNeg, LambdaBool b =>
      Some (LambdaBool (negb b))
  | LambdaOpUminus, LambdaInt n =>
      Some (LambdaInt (- n))
  | _, _ =>
      None
  end.
#[global] Arguments lambda_unop_eval !_ !_ / : assert.

Definition lambda_binop_eval_int op n1 n2 :=
  match op with
  | LambdaOpPlus =>
      Some (LambdaInt (n1 + n2))
  | LambdaOpMinus =>
      Some (LambdaInt (n1 - n2))
  | LambdaOpMult =>
      Some (LambdaInt (n1 * n2))
  | LambdaOpQuot =>
      Some (LambdaInt (n1 `quot` n2))
  | LambdaOpRem =>
      Some (LambdaInt (n1 `rem` n2))
  | LambdaOpLe =>
      Some (LambdaBool (bool_decide (n1 ≤ n2)%Z))
  | LambdaOpLt =>
      Some (LambdaBool (bool_decide (n1 < n2)%Z))
  | LambdaOpEq =>
      Some (LambdaBool (bool_decide (n1 = n2)%Z))
  end.
#[global] Arguments lambda_binop_eval_int !_ _ _ / : assert.

Definition lambda_binop_eval_bool op b1 b2 :=
  match op with
  | LambdaOpEq =>
      Some (LambdaBool (bool_decide (b1 = b2)))
  | _ =>
      None
  end.
#[global] Arguments lambda_binop_eval_bool !_ _ _ / : assert.

Definition lambda_binop_eval_function op func1 func2 :=
  match op with
  | LambdaOpEq =>
      Some (LambdaBool (bool_decide (func1 = func2)))
  | _ =>
      None
  end.
#[global] Arguments lambda_binop_eval_function !_ _ _ / : assert.

Definition lambda_binop_eval op v1 v2 :=
  match v1, v2 with
  | LambdaInt n1, LambdaInt n2 =>
      lambda_binop_eval_int op n1 n2
  | LambdaBool b1, LambdaBool b2 =>
      lambda_binop_eval_bool op b1 b2
  | LambdaFunc func1, LambdaFunc func2 =>
      lambda_binop_eval_function op func1 func2
  | _, _ =>
      None
  end.
#[global] Arguments lambda_binop_eval !_ !_ !_ / : assert.

Inductive lambda_head_step prog : lambda_expr → lambda_state → lambda_expr → lambda_state → Prop :=
  | lambda_head_step_let v e e' σ :
      e' = e.[#v/] →
      lambda_head_step prog
        (let: v in e) σ
        e' σ
  | lambda_head_step_call func v e e' σ :
      prog !! func = Some e →
      e' = e.[#v/] →
      lambda_head_step prog
        (func v) σ
        e' σ
  | lambda_head_step_unop op v v' σ :
      lambda_unop_eval op v = Some v' →
      lambda_head_step prog
        (LambdaUnop op v) σ
        v' σ
  | lambda_head_step_binop_1 op e1 e2 e' σ :
      e' = (let: e1 in let: e2.[ren (+1)] in LambdaBinopDet op $1 $0)%lambda_expr →
      lambda_head_step prog
        (LambdaBinop op e1 e2) σ
        e' σ
  | lambda_head_step_binop_2 op e1 e2 e' σ :
      e' = (let: e2 in let: e1.[ren (+1)] in LambdaBinopDet op $0 $1)%lambda_expr →
      lambda_head_step prog
        (LambdaBinop op e1 e2) σ
        e' σ
  | lambda_head_step_binop_det op v1 v2 v' σ :
      lambda_binop_eval op v1 v2 = Some v' →
      lambda_head_step prog
        (LambdaBinopDet op v1 v2) σ
        v' σ
  | lambda_head_step_if b e1 e2 σ :
      lambda_head_step prog
        (if: b then e1 else e2) σ
        (if b then e1 else e2) σ
  | lambda_head_step_constr_1 tag e1 e2 e' σ :
      e' = (let: e1 in let: e2.[ren (+1)] in &&tag $1 $0)%lambda_expr →
      lambda_head_step prog
        (&tag e1 e2) σ
        e' σ
  | lambda_head_step_constr_2 tag e1 e2 e' σ :
      e' = (let: e2 in let: e1.[ren (+1)] in &&tag $0 $1)%lambda_expr →
      lambda_head_step prog
        (&tag e1 e2) σ
        e' σ
  | lambda_head_step_constr_det tag v1 v2 σ l :
      σ !! (l +ₗ 0) = None →
      σ !! (l +ₗ 1) = None →
      σ !! (l +ₗ 2) = None →
      lambda_head_step prog
        (&&tag v1 v2) σ
        l (<[l +ₗ 2 := v2]> (<[l +ₗ 1 := v1]> (<[l +ₗ 0 := LambdaTag tag]> σ)))
  | lambda_head_step_load l l' idx v σ :
      σ !! (l +ₗ idx) = Some v →
      lambda_head_step prog
        (![idx] l) σ
        v σ
  | lambda_head_step_store l idx v w σ :
      σ !! (l +ₗ idx) = Some v →
      lambda_head_step prog
        (l <-[idx]- w) σ
        #() (<[l +ₗ idx := w]> σ).

Lemma lambda_head_step_constr_det' prog tag v1 v2 σ σ' :
  let l := loc_fresh (dom σ) in
  σ' = <[l +ₗ 2 := v2]> (<[l +ₗ 1 := v1]> (<[l +ₗ 0 := LambdaTag tag]> σ)) →
  lambda_head_step prog
    (&&tag v1 v2) σ
    l σ'.
Proof.
  intros l ->.
  apply lambda_head_step_constr_det;
    rewrite -not_elem_of_dom;
    apply loc_fresh_fresh; lia.
Qed.
