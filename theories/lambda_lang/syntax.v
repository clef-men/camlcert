From stdpp Require Export
  strings
  gmap.
From stdpp Require Import
  countable.

From simuliris Require Import
  prelude.
From simuliris.common Require Export
  autosubst
  three
  loc
  typeclasses.

Notation lambda_index := three (only parsing).

Definition lambda_tag := nat.

Notation lambda_function := string (only parsing).

Inductive lambda_val :=
  | LambdaUnit
  | LambdaIndex (idx : lambda_index)
  | LambdaTag (tag : lambda_tag)
  | LambdaInt (n : Z)
  | LambdaBool (b : bool)
  | LambdaLoc (l : loc)
  | LambdaFunc (func : lambda_function).

#[global] Instance lambda_val_inhabited : Inhabited lambda_val :=
  populate LambdaUnit.
#[global] Instance lambda_val_eq_dec : EqDecision lambda_val :=
  ltac:(solve_decision).
#[global] Instance lambda_val_countable :
  Countable lambda_val.
Proof.
  pose encode v :=
    match v with
    | LambdaUnit =>
        inl ()
    | LambdaIndex idx =>
        inr $ inl idx
    | LambdaTag tag =>
        inr $ inr $ inl tag
    | LambdaInt n =>
        inr $ inr $ inr $ inl n
    | LambdaBool b =>
        inr $ inr $ inr $ inr $ inl b
    | LambdaLoc l =>
        inr $ inr $ inr $ inr $ inr $ inl l
    | LambdaFunc func =>
        inr $ inr $ inr $ inr $ inr $ inr func
    end.
  pose decode v :=
    match v with
    | inl () =>
        LambdaUnit
    | inr (inl idx) =>
        LambdaIndex idx
    | inr (inr (inl tag)) =>
        LambdaTag tag
    | inr (inr (inr (inl n))) =>
        LambdaInt n
    | inr (inr (inr (inr (inl b)))) =>
        LambdaBool b
    | inr (inr (inr (inr (inr (inl l))))) =>
        LambdaLoc l
    | inr (inr (inr (inr (inr (inr func))))) =>
        LambdaFunc func
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

#[global] Instance lambda_val_similar : Similar lambda_val lambda_val :=
  Build_Similar $ λ v1 v2,
    match v1, v2 with
    | LambdaUnit, LambdaUnit =>
        True
    | LambdaIndex idx1, LambdaIndex idx2 =>
        idx1 = idx2
    | LambdaTag tag1, LambdaTag tag2 =>
        tag1 = tag2
    | LambdaInt i1, LambdaInt i2 =>
        i1 = i2
    | LambdaBool b1, LambdaBool b2 =>
        b1 = b2
    | LambdaLoc _, LambdaLoc _ =>
        True
    | LambdaFunc func1, LambdaFunc func2 =>
        func1 = func2
    | _, _ =>
        False
    end.

Inductive lambda_unop :=
  | LambdaOpNeg
  | LambdaOpUminus.

#[global] Instance lambda_unop_eq_dec : EqDecision lambda_unop :=
  ltac:(solve_decision).
#[global] Instance lambda_unop_countable :
  Countable lambda_unop.
Proof.
  pose encode op :=
    match op with
    | LambdaOpNeg => 0
    | LambdaOpUminus => 1
    end.
  pose decode op :=
    match op with
    | 0 => LambdaOpNeg
    | _ => LambdaOpUminus
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive lambda_binop :=
  | LambdaOpPlus | LambdaOpMinus | LambdaOpMult | LambdaOpQuot | LambdaOpRem
  | LambdaOpLe | LambdaOpLt | LambdaOpEq.

#[global] Instance lambda_binop_eq_dec : EqDecision lambda_binop :=
  ltac:(solve_decision).
#[global] Instance lambda_binop_countable :
  Countable lambda_binop.
Proof.
  pose encode op :=
    match op with
    | LambdaOpPlus => 0
    | LambdaOpMinus => 1
    | LambdaOpMult => 2
    | LambdaOpQuot => 3
    | LambdaOpRem => 4
    | LambdaOpLe => 5
    | LambdaOpLt => 6
    | LambdaOpEq => 7
    end.
  pose decode op :=
    match op with
    | 0 => LambdaOpPlus
    | 1 => LambdaOpMinus
    | 2 => LambdaOpMult
    | 3 => LambdaOpQuot
    | 4 => LambdaOpRem
    | 5 => LambdaOpLe
    | 6 => LambdaOpLt
    | _ => LambdaOpEq
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive lambda_expr :=
  | LambdaVal (v : lambda_val)
  | LambdaVar (x : var)
  | LambdaLet (e1 : lambda_expr) (e2 : {bind lambda_expr})
  | LambdaCall (e1 e2 : lambda_expr)
  | LambdaUnop (op : lambda_unop) (e : lambda_expr)
  | LambdaBinop (op : lambda_binop) (e1 e2 : lambda_expr)
  | LambdaIf (e0 e1 e2 : lambda_expr)
  | LambdaConstr (tag : lambda_tag) (e1 e2 : lambda_expr)
  | LambdaConstrDet (tag : lambda_tag) (e1 e2 : lambda_expr)
  | LambdaLoad (e1 e2 : lambda_expr)
  | LambdaStore (e1 e2 e3 : lambda_expr).

#[global] Instance lambda_expr_inhabited : Inhabited lambda_expr :=
  populate (LambdaVal inhabitant).
#[global] Instance lambda_expr_eq_dec : EqDecision lambda_expr :=
  ltac:(solve_decision).
#[global] Instance lambda_expr_countable :
  Countable lambda_expr.
Proof.
  pose fix encode e :=
    match e with
    | LambdaVal v =>
        GenLeaf (inl v)
    | LambdaVar x =>
        GenLeaf (inr $ inl x)
    | LambdaLet e1 e2 =>
        GenNode 0 [encode e1; encode e2]
    | LambdaCall e1 e2 =>
        GenNode 1 [encode e1; encode e2]
    | LambdaUnop op e =>
        GenNode 2 [GenLeaf (inr $ inr $ inl op); encode e]
    | LambdaBinop op e1 e2 =>
        GenNode 3 [GenLeaf (inr $ inr $ inr $ inl op); encode e1; encode e2]
    | LambdaIf e0 e1 e2 =>
        GenNode 4 [encode e0; encode e1; encode e2]
    | LambdaConstr tag e1 e2 =>
        GenNode 5 [GenLeaf (inr $ inr $ inr $ inr tag); encode e1; encode e2]
    | LambdaConstrDet tag e1 e2 =>
        GenNode 6 [GenLeaf (inr $ inr $ inr $ inr tag); encode e1; encode e2]
    | LambdaLoad e1 e2 =>
        GenNode 7 [encode e1; encode e2]
    | LambdaStore e1 e2 e3 =>
        GenNode 8 [encode e1; encode e2; encode e3]
    end.
  pose fix decode e :=
    match e with
    | GenLeaf (inl v) =>
        LambdaVal v
    | GenLeaf (inr (inl x)) =>
        LambdaVar x
    | GenNode 0 [e1; e2] =>
        LambdaLet (decode e1) (decode e2)
    | GenNode 1 [e1; e2] =>
        LambdaCall (decode e1) (decode e2)
    | GenNode 2 [GenLeaf (inr (inr (inl op))); e] =>
        LambdaUnop op (decode e)
    | GenNode 3 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] =>
        LambdaBinop op (decode e1) (decode e2)
    | GenNode 4 [e0; e1; e2] =>
        LambdaIf (decode e0) (decode e1) (decode e2)
    | GenNode 5 [GenLeaf (inr (inr (inr (inr tag)))); e1; e2] =>
        LambdaConstr tag (decode e1) (decode e2)
    | GenNode 6 [GenLeaf (inr (inr (inr (inr tag)))); e1; e2] =>
        LambdaConstrDet tag (decode e1) (decode e2)
    | GenNode 7 [e1; e2] =>
        LambdaLoad (decode e1) (decode e2)
    | GenNode 8 [e1; e2; e3] =>
        LambdaStore (decode e1) (decode e2) (decode e3)
    | _ =>
        @inhabitant _ lambda_expr_inhabited
    end.
  apply (inj_countable' encode decode). intros e. induction e; simpl; congruence.
Qed.

#[global] Instance lambda_expr_ids : Ids lambda_expr. derive. Defined.
#[global] Instance lambda_expr_rename : Rename lambda_expr. derive. Defined.
#[global] Instance lambda_expr_subst : Subst lambda_expr. derive. Defined.
#[global] Instance lambda_expr_subst_lemmas : SubstLemmas lambda_expr. derive. Qed.

Definition lambda_program := gmap lambda_function lambda_expr.
