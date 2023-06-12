From simuliris Require Import
  prelude.
From simuliris.language Require Export
  syntax.
From simuliris.language Require Import
  notations.

Definition state := gmap loc val.

#[global] Instance state_eq_dec :
  EqDecision state.
Proof.
  solve_decision.
Defined.
#[global] Instance state_inhabited :
  Inhabited state.
Proof.
  apply _.
Qed.

Implicit Types b : bool.
Implicit Types l : loc.
Implicit Types func : function.
Implicit Types constr : constructor.
Implicit Types v w : val.
Implicit Types e : expr.
Implicit Types prog : program.
Implicit Types σ : state.

Definition unop_eval op v :=
  match op, v with
  | OpNeg, Bool b =>
      Some (Bool (negb b))
  | OpUminus, Int n =>
      Some (Int (- n))
  | _, _ =>
      None
  end.

Definition binop_eval_int op n1 n2 :=
  match op with
  | OpPlus =>
      Some (Int (n1 + n2))
  | OpMinus =>
      Some (Int (n1 - n2))
  | OpMult =>
      Some (Int (n1 * n2))
  | OpQuot =>
      Some (Int (n1 `quot` n2))
  | OpRem =>
      Some (Int (n1 `rem` n2))
  | OpLe =>
      Some (Bool (bool_decide (n1 ≤ n2)%Z))
  | OpLt =>
      Some (Bool (bool_decide (n1 < n2)%Z))
  | OpEq =>
      Some (Bool (bool_decide (n1 = n2)%Z))
  | _ =>
      None
  end.
Definition binop_eval_bool op b1 b2 :=
  match op with
  | OpEq =>
      Some (Bool (bool_decide (b1 = b2)))
  | _ =>
      None
  end.
Definition binop_eval_loc op l1 l2 :=
  match op with
  | OpLe =>
      Some (Bool (bool_decide (l1 ≤ₗ l2)))
  | OpLt =>
      Some (Bool (bool_decide (l1 <ₗ l2)))
  | OpEq =>
      Some (Bool (bool_decide (l1 = l2)))
  | _ =>
      None
  end.
Definition binop_eval_function op func1 func2 :=
  match op with
  | OpEq =>
      Some (Bool (bool_decide (func1 = func2)))
  | _ =>
      None
  end.
Definition binop_eval op v1 v2 :=
  match v1, v2 with
  | Int n1, Int n2 =>
      binop_eval_int op n1 n2
  | Bool b1, Bool b2 =>
      binop_eval_bool op b1 b2
  | Loc l1, Loc l2 =>
      binop_eval_loc op l1 l2
  | Func func1, Func func2 =>
      binop_eval_function op func1 func2
  | Loc l1, Int n2 =>
      match op with
      | OpOffset =>
          Some (Loc (l1 +ₗ n2))
      | _ =>
          None
      end
  | _, _ =>
      None
  end.

Inductive head_step prog : expr → state → expr → state → Prop :=
  | head_step_let v e e' σ :
      e' = e.[#v/] →
      head_step prog
        (let: v in e) σ
        e' σ
  | head_step_call func v e e' σ :
      prog !! func = Some e →
      e' = e.[#v/] →
      head_step prog
        (func v) σ
        e' σ
  | head_step_unop op v v' σ :
      unop_eval op v = Some v' →
      head_step prog
        (Unop op v) σ
        v' σ
  | head_step_binop op v1 v2 v' σ :
      binop_eval op v1 v2 = Some v' →
      head_step prog
        (Binop op v1 v2) σ
        v' σ
  | head_step_if b e1 e2 σ :
      head_step prog
        (if: b then e1 else e2) σ
        (if b then e1 else e2) σ
  | head_step_constr_1 constr e1 e2 e' σ :
      e' = (let: e1 in let: e2.[ren (+1)] in &&constr $1 $0)%E →
      head_step prog
        (&constr e1 e2) σ
        e' σ
  | head_step_constr_2 constr e1 e2 e' σ :
      e' = (let: e2 in let: e1.[ren (+1)] in &&constr $0 $1)%E →
      head_step prog
        (&constr e1 e2) σ
        e' σ
  | head_step_constr_det constr v1 v2 σ l :
      σ !! l = None →
      σ !! (l +ₗ 1) = None →
      σ !! (l +ₗ 2) = None →
      head_step prog
        (&&constr v1 v2) σ
        l (<[l +ₗ 2 := v2]> (<[l +ₗ 1 := v1]> (<[l := Int (Z.of_nat constr)]> σ)))
  | head_step_load l v σ :
      σ !! l = Some v →
      head_step prog
        (! l) σ
        v σ
  | head_step_store l v w σ :
      σ !! l = Some v →
      head_step prog
        (l <- w) σ
        #() (<[l := w]> σ).

Lemma head_step_constr_det' prog constr v1 v2 σ σ' :
  let l := loc_fresh (dom σ) in
  σ' = <[l +ₗ 2 := v2]> (<[l +ₗ 1 := v1]> (<[l := Int (Z.of_nat constr)]> σ)) →
  head_step prog
    (&&constr v1 v2) σ
    l σ'.
Proof.
  intros l ->. apply head_step_constr_det;
    rewrite -not_elem_of_dom; first rewrite -(loc_add_0 l);
    apply loc_fresh_fresh; lia.
Qed.
