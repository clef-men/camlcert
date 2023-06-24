From stdpp Require Export
  binders.

From simuliris Require Import
  prelude.
From simuliris.tmc_lang Require Export
  syntax.

Notation name := string
( only parsing
).

Inductive human_val :=
  | HumanUnit
  | HumanIndex (idx : index)
  | HumanInt (n : Z)
  | HumanBool (b : bool)
  | HumanFunc (func : function).

#[global] Instance human_val_inhabited : Inhabited human_val :=
  populate HumanUnit.
#[global] Instance human_val_eq_dec : EqDecision human_val :=
  ltac:(solve_decision).
#[global] Instance human_val_countable :
  Countable human_val.
Proof.
  pose encode v :=
    match v with
    | HumanUnit =>
        inl ()
    | HumanIndex idx =>
        inr $ inl idx
    | HumanInt n =>
        inr $ inr $ inl n
    | HumanBool b =>
        inr $ inr $ inr $ inl b
    | HumanFunc func =>
        inr $ inr $ inr $ inr func
    end.
  pose decode v :=
    match v with
    | inl () =>
        HumanUnit
    | inr (inl idx) =>
        HumanIndex idx
    | inr (inr (inl n)) =>
        HumanInt n
    | inr (inr (inr (inl b))) =>
        HumanBool b
    | inr (inr (inr (inr func))) =>
        HumanFunc func
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive human_expr :=
  | HumanVal (v : human_val)
  | HumanVar (x : name)
  | HumanLet (x : binder) (e1 e2 : human_expr)
  | HumanCall (e1 e2 : human_expr)
  | HumanUnop (op : unop) (e : human_expr)
  | HumanBinop (op : binop) (e1 e2 : human_expr)
  | HumanIf (e0 e1 e2 : human_expr)
  | HumanConstr (constr : constructor) (e1 e2 : human_expr)
  | HumanLoad (e1 e2 : human_expr)
  | HumanStore (e1 e2 e3 : human_expr).

#[global] Instance human_expr_inhabited : Inhabited human_expr :=
  populate (HumanVal inhabitant).
#[global] Instance human_expr_eq_dec : EqDecision human_expr :=
  ltac:(solve_decision).
#[global] Instance human_expr_countable :
  Countable human_expr.
Proof.
  pose fix encode e :=
    match e with
    | HumanVal v =>
        GenLeaf (inl v)
    | HumanVar x =>
        GenLeaf (inr $ inl $ BNamed x)
    | HumanLet x e1 e2 =>
        GenNode 0 [GenLeaf (inr $ inl x); encode e1; encode e2]
    | HumanCall e1 e2 =>
        GenNode 1 [encode e1; encode e2]
    | HumanUnop op e =>
        GenNode 2 [GenLeaf (inr $ inr $ inl op); encode e]
    | HumanBinop op e1 e2 =>
        GenNode 3 [GenLeaf (inr $ inr $ inr $ inl op); encode e1; encode e2]
    | HumanIf e0 e1 e2 =>
        GenNode 4 [encode e0; encode e1; encode e2]
    | HumanConstr constr e1 e2 =>
        GenNode 5 [GenLeaf (inr $ inr $ inr $ inr constr); encode e1; encode e2]
    | HumanLoad e1 e2 =>
        GenNode 6 [encode e1; encode e2]
    | HumanStore e1 e2 e3 =>
        GenNode 7 [encode e1; encode e2; encode e3]
    end.
  pose fix decode e :=
    match e with
    | GenLeaf (inl v) =>
        HumanVal v
    | GenLeaf (inr (inl (BNamed x))) =>
        HumanVar x
    | GenNode 0 [GenLeaf (inr (inl x)); e1; e2] =>
        HumanLet x (decode e1) (decode e2)
    | GenNode 1 [e1; e2] =>
        HumanCall (decode e1) (decode e2)
    | GenNode 2 [GenLeaf (inr (inr (inl op))); e] =>
        HumanUnop op (decode e)
    | GenNode 3 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] =>
        HumanBinop op (decode e1) (decode e2)
    | GenNode 4 [e0; e1; e2] =>
        HumanIf (decode e0) (decode e1) (decode e2)
    | GenNode 5 [GenLeaf (inr (inr (inr (inr constr)))); e1; e2] =>
        HumanConstr constr (decode e1) (decode e2)
    | GenNode 6 [e1; e2] =>
        HumanLoad (decode e1) (decode e2)
    | GenNode 7 [e1; e2; e3] =>
        HumanStore (decode e1) (decode e2) (decode e3)
    | _ =>
        @inhabitant _ human_expr_inhabited
    end.
  apply (inj_countable' encode decode). intros e. induction e; simpl; congruence.
Qed.

Definition human_program := gmap function (binder * human_expr).
