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

Coercion data_index_to_Z idx : Z :=
  match idx with
  | DataZero => 0
  | DataOne => 1
  | DataTwo => 2
  end.

Definition data_tag :=
  nat.
Implicit Types tag : data_tag.

Definition data_tag_pair : data_tag :=
  0.

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
  | DataNeg
  | DataUminus.

#[global] Instance data_unop_eq_dec : EqDecision data_unop :=
  ltac:(solve_decision).
#[global] Instance data_unop_countable :
  Countable data_unop.
Proof.
  pose encode op :=
    match op with
    | DataNeg => 0
    | DataUminus => 1
    end.
  pose decode op :=
    match op with
    | 0 => DataNeg
    | _ => DataUminus
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive data_binop :=
  | DataPlus | DataMinus | DataMult | DataQuot | DataRem
  | DataLe | DataLt | DataGe | DataGt | DataEq | DataNe.

#[global] Instance data_binop_eq_dec : EqDecision data_binop :=
  ltac:(solve_decision).
#[global] Instance data_binop_countable :
  Countable data_binop.
Proof.
  pose encode op :=
    match op with
    | DataPlus => 0
    | DataMinus => 1
    | DataMult => 2
    | DataQuot => 3
    | DataRem => 4
    | DataLe => 5
    | DataLt => 6
    | DataGe => 7
    | DataGt => 8
    | DataEq => 9
    | DataNe => 10
    end.
  pose decode op :=
    match op with
    | 0 => DataPlus
    | 1 => DataMinus
    | 2 => DataMult
    | 3 => DataQuot
    | 4 => DataRem
    | 5 => DataLe
    | 6 => DataLt
    | 7 => DataGe
    | 8 => DataGt
    | 9 => DataEq
    | _ => DataNe
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
Variant data_encode_leaf :=
  | DataEncodeVal v
  | DataEncodeVar x
  | DataEncodeUnop (op : data_unop)
  | DataEncodeBinop (op : data_binop)
  | DataEncodeTag tag.
#[local] Instance data_encode_leaf_eq_dec : EqDecision data_encode_leaf :=
  ltac:(solve_decision).
#[local] Instance data_encode_leaf_countable :
  Countable data_encode_leaf.
Proof.
  pose encode leaf :=
    match leaf with
    | DataEncodeVal v =>
        inl $ inl $ inl $ inl v
    | DataEncodeVar x =>
        inl $ inl $ inl $ inr x
    | DataEncodeUnop op =>
        inl $ inl $ inr op
    | DataEncodeBinop op =>
        inl $ inr op
    | DataEncodeTag tag =>
        inr tag
    end.
  pose decode leaf :=
    match leaf with
    | inl (inl (inl (inl v))) =>
        DataEncodeVal v
    | inl (inl (inl (inr x))) =>
        DataEncodeVar x
    | inl (inl (inr op)) =>
        DataEncodeUnop op
    | inl (inr op) =>
        DataEncodeBinop op
    | inr tag =>
        DataEncodeTag tag
    end.
  refine (inj_countable' encode decode _). intros []; done.
Qed.
#[global] Instance data_expr_countable :
  Countable data_expr.
Proof.
  #[local] Notation code_Let :=
    0.
  #[local] Notation code_Call :=
    1.
  #[local] Notation code_Unop :=
    2.
  #[local] Notation code_Binop :=
    3.
  #[local] Notation code_BinopDet :=
    4.
  #[local] Notation code_If :=
    5.
  #[local] Notation code_Block :=
    6.
  #[local] Notation code_BlockDet :=
    7.
  #[local] Notation code_Load :=
    8.
  #[local] Notation code_Store :=
    9.
  pose fix encode e :=
    match e with
    | DataVal v =>
        GenLeaf (DataEncodeVal v)
    | DataVar x =>
        GenLeaf (DataEncodeVar x)
    | DataLet e1 e2 =>
        GenNode code_Let [encode e1; encode e2]
    | DataCall e1 e2 =>
        GenNode code_Call [encode e1; encode e2]
    | DataUnop op e =>
        GenNode code_Unop [GenLeaf (DataEncodeUnop op); encode e]
    | DataBinop op e1 e2 =>
        GenNode code_Binop [GenLeaf (DataEncodeBinop op); encode e1; encode e2]
    | DataBinopDet op e1 e2 =>
        GenNode code_BinopDet [GenLeaf (DataEncodeBinop op); encode e1; encode e2]
    | DataIf e0 e1 e2 =>
        GenNode code_If [encode e0; encode e1; encode e2]
    | DataBlock tag e1 e2 =>
        GenNode code_Block [GenLeaf (DataEncodeTag tag); encode e1; encode e2]
    | DataBlockDet tag e1 e2 =>
        GenNode code_BlockDet [GenLeaf (DataEncodeTag tag); encode e1; encode e2]
    | DataLoad e1 e2 =>
        GenNode code_Load [encode e1; encode e2]
    | DataStore e1 e2 e3 =>
        GenNode code_Store [encode e1; encode e2; encode e3]
    end.
  pose fix decode _e :=
    match _e with
    | GenLeaf (DataEncodeVal v) =>
        DataVal v
    | GenLeaf (DataEncodeVar x) =>
        DataVar x
    | GenNode code_Let [e1; e2] =>
        DataLet (decode e1) (decode e2)
    | GenNode code_Call [e1; e2] =>
        DataCall (decode e1) (decode e2)
    | GenNode code_Unop [GenLeaf (DataEncodeUnop op); e] =>
        DataUnop op (decode e)
    | GenNode code_Binop [GenLeaf (DataEncodeBinop op); e1; e2] =>
        DataBinop op (decode e1) (decode e2)
    | GenNode code_BinopDet [GenLeaf (DataEncodeBinop op); e1; e2] =>
        DataBinopDet op (decode e1) (decode e2)
    | GenNode code_If [e0; e1; e2] =>
        DataIf (decode e0) (decode e1) (decode e2)
    | GenNode code_Block [GenLeaf (DataEncodeTag tag); e1; e2] =>
        DataBlock tag (decode e1) (decode e2)
    | GenNode code_BlockDet [GenLeaf (DataEncodeTag tag); e1; e2] =>
        DataBlockDet tag (decode e1) (decode e2)
    | GenNode code_Load [e1; e2] =>
        DataLoad (decode e1) (decode e2)
    | GenNode code_Store [e1; e2; e3] =>
        DataStore (decode e1) (decode e2) (decode e3)
    | _ =>
        @inhabitant _ data_expr_inhabited
    end.
  apply (inj_countable' encode decode).
  intros e. induction e; simpl; congruence.
Qed.

#[global] Instance data_expr_ids : Ids data_expr :=
  ltac:(derive).
#[global] Instance data_expr_rename : Rename data_expr :=
  ltac:(derive).
#[global] Instance data_expr_subst : Subst data_expr :=
  ltac:(derive).
#[global] Instance data_expr_subst_lemmas :
  SubstLemmas data_expr.
Proof.
  derive.
Qed.

Notation data_of_val :=
  DataVal
( only parsing
).
Definition data_to_val e :=
  match e with
  | DataVal v =>
      Some v
  | _ =>
      None
  end.

Lemma data_to_of_val e v :
  e = data_of_val v →
  data_to_val e = Some v.
Proof.
  naive_solver.
Qed.
Lemma data_of_to_val e v :
  data_to_val e = Some v →
  data_of_val v = e.
Proof.
  destruct e => //=. by intros [= <-].
Qed.
#[global] Instance data_of_val_inj :
  Inj (=) (=) data_of_val.
Proof.
  intros ?*. congruence.
Qed.

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
