From stdpp Require Export
  binders.

From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  syntax.

Notation lambda_human_name := string (only parsing).

Inductive lambda_human_val :=
  | LambdaHumanUnit
  | LambdaHumanIndex (idx : lambda_index)
  | LambdaHumanInt (n : Z)
  | LambdaHumanBool (b : bool)
  | LambdaHumanFunc (func : lambda_function).

#[global] Instance lambda_human_val_inhabited : Inhabited lambda_human_val :=
  populate LambdaHumanUnit.
#[global] Instance lambda_human_val_eq_dec : EqDecision lambda_human_val :=
  ltac:(solve_decision).
#[global] Instance lambda_human_val_countable :
  Countable lambda_human_val.
Proof.
  pose encode v :=
    match v with
    | LambdaHumanUnit =>
        inl ()
    | LambdaHumanIndex idx =>
        inr $ inl idx
    | LambdaHumanInt n =>
        inr $ inr $ inl n
    | LambdaHumanBool b =>
        inr $ inr $ inr $ inl b
    | LambdaHumanFunc func =>
        inr $ inr $ inr $ inr func
    end.
  pose decode v :=
    match v with
    | inl () =>
        LambdaHumanUnit
    | inr (inl idx) =>
        LambdaHumanIndex idx
    | inr (inr (inl n)) =>
        LambdaHumanInt n
    | inr (inr (inr (inl b))) =>
        LambdaHumanBool b
    | inr (inr (inr (inr func))) =>
        LambdaHumanFunc func
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive lambda_human_expr :=
  | LambdaHumanVal (v : lambda_human_val)
  | LambdaHumanVar (x : lambda_human_name)
  | LambdaHumanLet (x : binder) (e1 e2 : lambda_human_expr)
  | LambdaHumanCall (e1 e2 : lambda_human_expr)
  | LambdaHumanUnop (op : lambda_unop) (e : lambda_human_expr)
  | LambdaHumanBinop (op : lambda_binop) (e1 e2 : lambda_human_expr)
  | LambdaHumanIf (e0 e1 e2 : lambda_human_expr)
  | LambdaHumanConstr (constr : lambda_constructor) (e1 e2 : lambda_human_expr)
  | LambdaHumanLoad (e1 e2 : lambda_human_expr)
  | LambdaHumanStore (e1 e2 e3 : lambda_human_expr).

#[global] Instance lambda_human_expr_inhabited : Inhabited lambda_human_expr :=
  populate (LambdaHumanVal inhabitant).
#[global] Instance lambda_human_expr_eq_dec : EqDecision lambda_human_expr :=
  ltac:(solve_decision).
#[global] Instance lambda_human_expr_countable :
  Countable lambda_human_expr.
Proof.
  pose fix encode e :=
    match e with
    | LambdaHumanVal v =>
        GenLeaf (inl v)
    | LambdaHumanVar x =>
        GenLeaf (inr $ inl $ BNamed x)
    | LambdaHumanLet x e1 e2 =>
        GenNode 0 [GenLeaf (inr $ inl x); encode e1; encode e2]
    | LambdaHumanCall e1 e2 =>
        GenNode 1 [encode e1; encode e2]
    | LambdaHumanUnop op e =>
        GenNode 2 [GenLeaf (inr $ inr $ inl op); encode e]
    | LambdaHumanBinop op e1 e2 =>
        GenNode 3 [GenLeaf (inr $ inr $ inr $ inl op); encode e1; encode e2]
    | LambdaHumanIf e0 e1 e2 =>
        GenNode 4 [encode e0; encode e1; encode e2]
    | LambdaHumanConstr constr e1 e2 =>
        GenNode 5 [GenLeaf (inr $ inr $ inr $ inr constr); encode e1; encode e2]
    | LambdaHumanLoad e1 e2 =>
        GenNode 6 [encode e1; encode e2]
    | LambdaHumanStore e1 e2 e3 =>
        GenNode 7 [encode e1; encode e2; encode e3]
    end.
  pose fix decode e :=
    match e with
    | GenLeaf (inl v) =>
        LambdaHumanVal v
    | GenLeaf (inr (inl (BNamed x))) =>
        LambdaHumanVar x
    | GenNode 0 [GenLeaf (inr (inl x)); e1; e2] =>
        LambdaHumanLet x (decode e1) (decode e2)
    | GenNode 1 [e1; e2] =>
        LambdaHumanCall (decode e1) (decode e2)
    | GenNode 2 [GenLeaf (inr (inr (inl op))); e] =>
        LambdaHumanUnop op (decode e)
    | GenNode 3 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] =>
        LambdaHumanBinop op (decode e1) (decode e2)
    | GenNode 4 [e0; e1; e2] =>
        LambdaHumanIf (decode e0) (decode e1) (decode e2)
    | GenNode 5 [GenLeaf (inr (inr (inr (inr constr)))); e1; e2] =>
        LambdaHumanConstr constr (decode e1) (decode e2)
    | GenNode 6 [e1; e2] =>
        LambdaHumanLoad (decode e1) (decode e2)
    | GenNode 7 [e1; e2; e3] =>
        LambdaHumanStore (decode e1) (decode e2) (decode e3)
    | _ =>
        @inhabitant _ lambda_human_expr_inhabited
    end.
  apply (inj_countable' encode decode). intros e. induction e; simpl; congruence.
Qed.

Definition lambda_human_program :=
  gmap lambda_function (binder * lambda_human_expr).
