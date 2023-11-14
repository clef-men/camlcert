From stdpp Require Export
  binders.

From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  syntax.

Notation data_human_name :=
  string
( only parsing
).

Inductive data_human_val :=
  | DataHumanUnit
  | DataHumanIndex (idx : data_index)
  | DataHumanTag (tag : data_tag)
  | DataHumanInt (n : Z)
  | DataHumanBool (b : bool)
  | DataHumanFunc (func : data_function) (annot : data_annotation).

#[global] Instance data_human_val_inhabited : Inhabited data_human_val :=
  populate DataHumanUnit.
#[global] Instance data_human_val_eq_dec : EqDecision data_human_val :=
  ltac:(solve_decision).
#[global] Instance data_human_val_countable :
  Countable data_human_val.
Proof.
  pose encode v :=
    match v with
    | DataHumanUnit =>
        inl ()
    | DataHumanIndex idx =>
        inr $ inl idx
    | DataHumanTag tag =>
        inr $ inr $ inl tag
    | DataHumanInt n =>
        inr $ inr $ inr $ inl n
    | DataHumanBool b =>
        inr $ inr $ inr $ inr $ inl b
    | DataHumanFunc func annot =>
        inr $ inr $ inr $ inr $ inr (func, annot)
    end.
  pose decode v :=
    match v with
    | inl () =>
        DataHumanUnit
    | inr (inl idx) =>
        DataHumanIndex idx
    | inr (inr (inl tag)) =>
        DataHumanTag tag
    | inr (inr (inr (inl n))) =>
        DataHumanInt n
    | inr (inr (inr (inr (inl b)))) =>
        DataHumanBool b
    | inr (inr (inr (inr (inr (func, annot))))) =>
        DataHumanFunc func annot
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive data_human_expr :=
  | DataHumanVal (v : data_human_val)
  | DataHumanVar (x : data_human_name)
  | DataHumanLet (x : binder) (e1 e2 : data_human_expr)
  | DataHumanCall (e1 e2 : data_human_expr)
  | DataHumanUnop (op : data_unop) (e : data_human_expr)
  | DataHumanBinop (op : data_binop) (e1 e2 : data_human_expr)
  | DataHumanIf (e0 e1 e2 : data_human_expr)
  | DataHumanBlock (tag : data_tag) (e1 e2 : data_human_expr)
  | DataHumanLoad (e1 e2 : data_human_expr)
  | DataHumanStore (e1 e2 e3 : data_human_expr).

#[global] Instance data_human_expr_inhabited : Inhabited data_human_expr :=
  populate (DataHumanVal inhabitant).
#[global] Instance data_human_expr_eq_dec : EqDecision data_human_expr :=
  ltac:(solve_decision).
#[global] Instance data_human_expr_countable :
  Countable data_human_expr.
Proof.
  pose fix encode e :=
    match e with
    | DataHumanVal v =>
        GenLeaf (inl v)
    | DataHumanVar x =>
        GenLeaf (inr $ inl $ BNamed x)
    | DataHumanLet x e1 e2 =>
        GenNode 0 [GenLeaf (inr $ inl x); encode e1; encode e2]
    | DataHumanCall e1 e2 =>
        GenNode 1 [encode e1; encode e2]
    | DataHumanUnop op e =>
        GenNode 2 [GenLeaf (inr $ inr $ inl op); encode e]
    | DataHumanBinop op e1 e2 =>
        GenNode 3 [GenLeaf (inr $ inr $ inr $ inl op); encode e1; encode e2]
    | DataHumanIf e0 e1 e2 =>
        GenNode 4 [encode e0; encode e1; encode e2]
    | DataHumanBlock tag e1 e2 =>
        GenNode 5 [GenLeaf (inr $ inr $ inr $ inr tag); encode e1; encode e2]
    | DataHumanLoad e1 e2 =>
        GenNode 6 [encode e1; encode e2]
    | DataHumanStore e1 e2 e3 =>
        GenNode 7 [encode e1; encode e2; encode e3]
    end.
  pose fix decode e :=
    match e with
    | GenLeaf (inl v) =>
        DataHumanVal v
    | GenLeaf (inr (inl (BNamed x))) =>
        DataHumanVar x
    | GenNode 0 [GenLeaf (inr (inl x)); e1; e2] =>
        DataHumanLet x (decode e1) (decode e2)
    | GenNode 1 [e1; e2] =>
        DataHumanCall (decode e1) (decode e2)
    | GenNode 2 [GenLeaf (inr (inr (inl op))); e] =>
        DataHumanUnop op (decode e)
    | GenNode 3 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] =>
        DataHumanBinop op (decode e1) (decode e2)
    | GenNode 4 [e0; e1; e2] =>
        DataHumanIf (decode e0) (decode e1) (decode e2)
    | GenNode 5 [GenLeaf (inr (inr (inr (inr tag)))); e1; e2] =>
        DataHumanBlock tag (decode e1) (decode e2)
    | GenNode 6 [e1; e2] =>
        DataHumanLoad (decode e1) (decode e2)
    | GenNode 7 [e1; e2; e3] =>
        DataHumanStore (decode e1) (decode e2) (decode e3)
    | _ =>
        @inhabitant _ data_human_expr_inhabited
    end.
  apply (inj_countable' encode decode). intros e. induction e; simpl; congruence.
Qed.

Record data_human_definition := {
  data_human_definition_annot : data_annotation ;
  data_human_definition_param : binder ;
  data_human_definition_body : data_human_expr ;
}.

#[global] Instance data_human_definition_inhabited : Inhabited data_human_definition :=
  populate {|
    data_human_definition_annot := inhabitant ;
    data_human_definition_param := inhabitant ;
    data_human_definition_body := inhabitant ;
  |}.
#[global] Instance data_human_definition_eq_dec : EqDecision data_human_definition :=
  ltac:(solve_decision).
#[global] Instance data_human_definition_countable :
  Countable data_human_definition.
Proof.
  pose encode def :=
    ( def.(data_human_definition_annot),
      def.(data_human_definition_param),
      def.(data_human_definition_body)
    ).
  pose decode def :=
    {|data_human_definition_annot := def.1.1 ;
      data_human_definition_param := def.1.2 ;
      data_human_definition_body := def.2 ;
    |}.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Definition data_human_program :=
  gmap data_function data_human_definition.
