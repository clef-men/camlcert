From stdpp Require Export
  binders.

From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  syntax.
From camlcert Require Import
  options.

Implicit Types b : bool.
Implicit Types n : Z.
Implicit Types idx : data_index.
Implicit Types tag : data_tag.
Implicit Types func : data_function.
Implicit Types annot : data_annotation.

Notation data_human_name :=
  string
( only parsing
).

Inductive data_human_val :=
  | DataHumanUnit
  | DataHumanIndex idx
  | DataHumanTag tag
  | DataHumanBool b
  | DataHumanInt n
  | DataHumanFunc func annot.
Implicit Types v : data_human_val.

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
    | DataHumanBool b =>
        inr $ inr $ inr $ inl b
    | DataHumanInt n =>
        inr $ inr $ inr $ inr $ inl n
    | DataHumanFunc func annot =>
        inr $ inr $ inr $ inr $ inr (func, annot)
    end.
  pose decode _v :=
    match _v with
    | inl () =>
        DataHumanUnit
    | inr (inl idx) =>
        DataHumanIndex idx
    | inr (inr (inl tag)) =>
        DataHumanTag tag
    | inr (inr (inr (inl b))) =>
        DataHumanBool b
    | inr (inr (inr (inr (inl n)))) =>
        DataHumanInt n
    | inr (inr (inr (inr (inr (func, annot))))) =>
        DataHumanFunc func annot
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive data_human_expr :=
  | DataHumanVal v
  | DataHumanVar (x : data_human_name)
  | DataHumanLet (x : binder) (e1 e2 : data_human_expr)
  | DataHumanCall (e1 e2 : data_human_expr)
  | DataHumanUnop (op : data_unop) (e : data_human_expr)
  | DataHumanBinop (op : data_binop) (e1 e2 : data_human_expr)
  | DataHumanIf (e0 e1 e2 : data_human_expr)
  | DataHumanBlock tag (e1 e2 : data_human_expr)
  | DataHumanLoad (e1 e2 : data_human_expr)
  | DataHumanStore (e1 e2 e3 : data_human_expr).

#[global] Instance data_human_expr_inhabited : Inhabited data_human_expr :=
  populate (DataHumanVal inhabitant).
#[global] Instance data_human_expr_eq_dec : EqDecision data_human_expr :=
  ltac:(solve_decision).
Variant data_human_encode_leaf :=
  | DataHumanEncodeVal v
  | DataHumanEncodeVar (x : binder)
  | DataHumanEncodeUnop (op : data_unop)
  | DataHumanEncodeBinop (op : data_binop)
  | DataHumanEncodeTag tag.
#[local] Instance data_human_encode_leaf_eq_dec : EqDecision data_human_encode_leaf :=
  ltac:(solve_decision).
#[local] Instance data_human_encode_leaf_countable :
  Countable data_human_encode_leaf.
Proof.
  pose encode leaf :=
    match leaf with
    | DataHumanEncodeVal v =>
        inl $ inl $ inl $ inl v
    | DataHumanEncodeVar x =>
        inl $ inl $ inl $ inr x
    | DataHumanEncodeUnop op =>
        inl $ inl $ inr op
    | DataHumanEncodeBinop op =>
        inl $ inr op
    | DataHumanEncodeTag tag =>
        inr tag
    end.
  pose decode leaf :=
    match leaf with
    | inl (inl (inl (inl v))) =>
        DataHumanEncodeVal v
    | inl (inl (inl (inr x))) =>
        DataHumanEncodeVar x
    | inl (inl (inr op)) =>
        DataHumanEncodeUnop op
    | inl (inr op) =>
        DataHumanEncodeBinop op
    | inr tag =>
        DataHumanEncodeTag tag
    end.
  refine (inj_countable' encode decode _). intros []; done.
Qed.
#[global] Instance data_human_expr_countable :
  Countable data_human_expr.
Proof.
  #[local] Notation code_Let :=
    0.
  #[local] Notation code_Call :=
    1.
  #[local] Notation code_Unop :=
    2.
  #[local] Notation code_Binop :=
    3.
  #[local] Notation code_If :=
    4.
  #[local] Notation code_Block :=
    5.
  #[local] Notation code_Load :=
    6.
  #[local] Notation code_Store :=
    7.
  pose fix encode e :=
    match e with
    | DataHumanVal v =>
        GenLeaf (DataHumanEncodeVal v)
    | DataHumanVar x =>
        GenLeaf (DataHumanEncodeVar (BNamed x))
    | DataHumanLet x e1 e2 =>
        GenNode code_Let [GenLeaf (DataHumanEncodeVar x); encode e1; encode e2]
    | DataHumanCall e1 e2 =>
        GenNode code_Call [encode e1; encode e2]
    | DataHumanUnop op e =>
        GenNode code_Unop [GenLeaf (DataHumanEncodeUnop op); encode e]
    | DataHumanBinop op e1 e2 =>
        GenNode code_Binop [GenLeaf (DataHumanEncodeBinop op); encode e1; encode e2]
    | DataHumanIf e0 e1 e2 =>
        GenNode code_If [encode e0; encode e1; encode e2]
    | DataHumanBlock tag e1 e2 =>
        GenNode code_Block [GenLeaf (DataHumanEncodeTag tag); encode e1; encode e2]
    | DataHumanLoad e1 e2 =>
        GenNode code_Load [encode e1; encode e2]
    | DataHumanStore e1 e2 e3 =>
        GenNode code_Store [encode e1; encode e2; encode e3]
    end.
  pose fix decode _e :=
    match _e with
    | GenLeaf (DataHumanEncodeVal v) =>
        DataHumanVal v
    | GenLeaf (DataHumanEncodeVar (BNamed x)) =>
        DataHumanVar x
    | GenNode code_Let [GenLeaf (DataHumanEncodeVar x); e1; e2] =>
        DataHumanLet x (decode e1) (decode e2)
    | GenNode code_Call [e1; e2] =>
        DataHumanCall (decode e1) (decode e2)
    | GenNode code_Unop [GenLeaf (DataHumanEncodeUnop op); e] =>
        DataHumanUnop op (decode e)
    | GenNode code_Binop [GenLeaf (DataHumanEncodeBinop op); e1; e2] =>
        DataHumanBinop op (decode e1) (decode e2)
    | GenNode code_If [e0; e1; e2] =>
        DataHumanIf (decode e0) (decode e1) (decode e2)
    | GenNode code_Block [GenLeaf (DataHumanEncodeTag tag); e1; e2] =>
        DataHumanBlock tag (decode e1) (decode e2)
    | GenNode code_Load [e1; e2] =>
        DataHumanLoad (decode e1) (decode e2)
    | GenNode code_Store [e1; e2; e3] =>
        DataHumanStore (decode e1) (decode e2) (decode e3)
    | _ =>
        @inhabitant _ data_human_expr_inhabited
    end.
  apply (inj_countable' encode decode).
  intros e. induction e; simpl; congruence.
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
