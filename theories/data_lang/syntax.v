From stdpp Require Export
  strings
  gmap.
From stdpp Require Import
  countable.

From camlcert Require Import
  prelude.
From camlcert.common Require Export
  autosubst
  loc
  typeclasses.
From camlcert Require Import
  options.
From camlcert Require Import
  options.

Implicit Types b : bool.
Implicit Types n : Z.
Implicit Types l : loc.
Implicit Types x : var.

Inductive data_index :=
  | DataZero
  | DataOne
  | DataTwo.
Implicit Types idx : data_index.

#[global] Instance data_index_eq_dec : EqDecision data_index :=
  ltac:(solve_decision).
#[global] Instance data_index_countable :
  Countable data_index.
Proof.
  pose encode idx :=
    match idx with
    | DataZero => 0
    | DataOne => 1
    | DataTwo => 2
    end.
  pose decode (idx : nat) :=
    match idx with
    | 0 => DataZero
    | 1 => DataOne
    | _ => DataTwo
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Definition data_tag :=
  nat.
Implicit Types tag : data_tag.

Notation data_function :=
  string
( only parsing
).
Implicit Types func : data_function.

Definition data_annotation :=
  list string.
Implicit Types annot : data_annotation.

Inductive data_val :=
  | DataUnit
  | DataIndex idx
  | DataTag tag
  | DataBool b
  | DataInt n
  | DataLoc l
  | DataFunc func annot.
Implicit Types v : data_val.

Definition DataFunc' func :=
  DataFunc func [].

#[global] Instance data_val_inhabited : Inhabited data_val :=
  populate DataUnit.
#[global] Instance data_val_eq_dec : EqDecision data_val :=
  ltac:(solve_decision).
#[global] Instance data_val_countable :
  Countable data_val.
Proof.
  pose encode v :=
    match v with
    | DataUnit =>
        inl ()
    | DataIndex idx =>
        inr $ inl idx
    | DataTag tag =>
        inr $ inr $ inl tag
    | DataBool b =>
        inr $ inr $ inr $ inl b
    | DataInt n =>
        inr $ inr $ inr $ inr $ inl n
    | DataLoc l =>
        inr $ inr $ inr $ inr $ inr $ inl l
    | DataFunc func annot =>
        inr $ inr $ inr $ inr $ inr $ inr (func, annot)
    end.
  pose decode _v :=
    match _v with
    | inl () =>
        DataUnit
    | inr (inl idx) =>
        DataIndex idx
    | inr (inr (inl tag)) =>
        DataTag tag
    | inr (inr (inr (inl b))) =>
        DataBool b
    | inr (inr (inr (inr (inl n)))) =>
        DataInt n
    | inr (inr (inr (inr (inr (inl l))))) =>
        DataLoc l
    | inr (inr (inr (inr (inr (inr (func, annot)))))) =>
        DataFunc func annot
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

#[global] Instance data_val_similar : Similar data_val data_val :=
  Build_Similar $ λ v1 v2,
    match v1, v2 with
    | DataUnit, DataUnit =>
        True
    | DataIndex idx1, DataIndex idx2 =>
        idx1 = idx2
    | DataTag tag1, DataTag tag2 =>
        tag1 = tag2
    | DataBool b1, DataBool b2 =>
        b1 = b2
    | DataInt n1, DataInt n2 =>
        n1 = n2
    | DataLoc _, DataLoc _ =>
        True
    | DataFunc func1 annot1, DataFunc func2 annot2 =>
        func1 = func2 ∧ annot1 = annot2
    | _, _ =>
        False
    end.

Inductive data_unop :=
  | DataOpNeg
  | DataOpUminus.

#[global] Instance data_unop_eq_dec : EqDecision data_unop :=
  ltac:(solve_decision).
#[global] Instance data_unop_countable :
  Countable data_unop.
Proof.
  pose encode op :=
    match op with
    | DataOpNeg => 0
    | DataOpUminus => 1
    end.
  pose decode op :=
    match op with
    | 0 => DataOpNeg
    | _ => DataOpUminus
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive data_binop :=
  | DataOpPlus | DataOpMinus | DataOpMult | DataOpQuot | DataOpRem
  | DataOpLe | DataOpLt | DataOpGe | DataOpGt | DataOpEq | DataOpNe.

#[global] Instance data_binop_eq_dec : EqDecision data_binop :=
  ltac:(solve_decision).
#[global] Instance data_binop_countable :
  Countable data_binop.
Proof.
  pose encode op :=
    match op with
    | DataOpPlus => 0
    | DataOpMinus => 1
    | DataOpMult => 2
    | DataOpQuot => 3
    | DataOpRem => 4
    | DataOpLe => 5
    | DataOpLt => 6
    | DataOpGe => 7
    | DataOpGt => 8
    | DataOpEq => 9
    | DataOpNe => 10
    end.
  pose decode op :=
    match op with
    | 0 => DataOpPlus
    | 1 => DataOpMinus
    | 2 => DataOpMult
    | 3 => DataOpQuot
    | 4 => DataOpRem
    | 5 => DataOpLe
    | 6 => DataOpLt
    | 7 => DataOpGe
    | 8 => DataOpGt
    | 9 => DataOpEq
    | _ => DataOpNe
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive data_expr :=
  | DataVal v
  | DataVar x
  | DataLet (e1 : data_expr) (e2 : {bind data_expr})
  | DataCall (e1 e2 : data_expr)
  | DataUnop (op : data_unop) (e : data_expr)
  | DataBinop (op : data_binop) (e1 e2 : data_expr)
  | DataBinopDet (op : data_binop) (e1 e2 : data_expr)
  | DataIf (e0 e1 e2 : data_expr)
  | DataBlock tag (e1 e2 : data_expr)
  | DataBlockDet tag (e1 e2 : data_expr)
  | DataLoad (e1 e2 : data_expr)
  | DataStore (e1 e2 e3 : data_expr).
Implicit Types e : data_expr.

#[global] Instance data_expr_inhabited : Inhabited data_expr :=
  populate (DataVal inhabitant).
#[global] Instance data_expr_eq_dec : EqDecision data_expr :=
  ltac:(solve_decision).
#[global] Instance data_expr_countable :
  Countable data_expr.
Proof.
  pose fix encode e :=
    match e with
    | DataVal v =>
        GenLeaf (inl v)
    | DataVar x =>
        GenLeaf (inr $ inl x)
    | DataLet e1 e2 =>
        GenNode 0 [encode e1; encode e2]
    | DataCall e1 e2 =>
        GenNode 1 [encode e1; encode e2]
    | DataUnop op e =>
        GenNode 2 [GenLeaf (inr $ inr $ inl op); encode e]
    | DataBinop op e1 e2 =>
        GenNode 3 [GenLeaf (inr $ inr $ inr $ inl op); encode e1; encode e2]
    | DataBinopDet op e1 e2 =>
        GenNode 4 [GenLeaf (inr $ inr $ inr $ inl op); encode e1; encode e2]
    | DataIf e0 e1 e2 =>
        GenNode 5 [encode e0; encode e1; encode e2]
    | DataBlock tag e1 e2 =>
        GenNode 6 [GenLeaf (inr $ inr $ inr $ inr tag); encode e1; encode e2]
    | DataBlockDet tag e1 e2 =>
        GenNode 7 [GenLeaf (inr $ inr $ inr $ inr tag); encode e1; encode e2]
    | DataLoad e1 e2 =>
        GenNode 8 [encode e1; encode e2]
    | DataStore e1 e2 e3 =>
        GenNode 9 [encode e1; encode e2; encode e3]
    end.
  pose fix decode _e :=
    match _e with
    | GenLeaf (inl v) =>
        DataVal v
    | GenLeaf (inr (inl x)) =>
        DataVar x
    | GenNode 0 [e1; e2] =>
        DataLet (decode e1) (decode e2)
    | GenNode 1 [e1; e2] =>
        DataCall (decode e1) (decode e2)
    | GenNode 2 [GenLeaf (inr (inr (inl op))); e] =>
        DataUnop op (decode e)
    | GenNode 3 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] =>
        DataBinop op (decode e1) (decode e2)
    | GenNode 4 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] =>
        DataBinopDet op (decode e1) (decode e2)
    | GenNode 5 [e0; e1; e2] =>
        DataIf (decode e0) (decode e1) (decode e2)
    | GenNode 6 [GenLeaf (inr (inr (inr (inr tag)))); e1; e2] =>
        DataBlock tag (decode e1) (decode e2)
    | GenNode 7 [GenLeaf (inr (inr (inr (inr tag)))); e1; e2] =>
        DataBlockDet tag (decode e1) (decode e2)
    | GenNode 8 [e1; e2] =>
        DataLoad (decode e1) (decode e2)
    | GenNode 9 [e1; e2; e3] =>
        DataStore (decode e1) (decode e2) (decode e3)
    | _ =>
        @inhabitant _ data_expr_inhabited
    end.
  apply (inj_countable' encode decode). intros e. induction e; simpl; congruence.
Qed.

#[global] Instance data_expr_ids : Ids data_expr. derive. Defined.
#[global] Instance data_expr_rename : Rename data_expr. derive. Defined.
#[global] Instance data_expr_subst : Subst data_expr. derive. Defined.
#[global] Instance data_expr_subst_lemmas : SubstLemmas data_expr. derive. Qed.

Record data_definition := {
  data_definition_annot : data_annotation ;
  data_definition_body : data_expr ;
}.
Implicit Types def : data_definition.

#[global] Instance data_definition_inhabited : Inhabited data_definition :=
  populate {|
    data_definition_annot := inhabitant ;
    data_definition_body := inhabitant ;
  |}.
#[global] Instance data_definition_eq_dec : EqDecision data_definition :=
  ltac:(solve_decision).
#[global] Instance data_definition_countable :
  Countable data_definition.
Proof.
  pose encode def :=
    ( def.(data_definition_annot),
      def.(data_definition_body)
    ).
  pose decode _def :=
    {|data_definition_annot := _def.1 ;
      data_definition_body := _def.2 ;
    |}.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Definition data_program :=
  gmap data_function data_definition.
