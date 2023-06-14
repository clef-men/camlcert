From stdpp Require Export
  strings
  gmap.
From stdpp Require Import
  countable.

From Autosubst Require Export
  Autosubst.

From simuliris Require Import
  prelude.
From simuliris.common Require Import
  typeclasses.
From simuliris.language Require Export
  loc.

Notation function := string.

Definition constructor := nat.

Inductive val :=
  | Unit
  | Int (n : Z)
  | Bool (b : bool)
  | Loc (l : loc)
  | Func (func : function).

#[global] Instance val_eq_dec : EqDecision val :=
  ltac:(solve_decision).
#[global] Instance val_countable :
  Countable val.
Proof.
  pose encode v :=
    match v with
    | Unit =>
        inl ()
    | Int n =>
        inr $ inl n
    | Bool b =>
        inr $ inr $ inl b
    | Loc l =>
        inr $ inr $ inr $ inl l
    | Func func =>
        inr $ inr $ inr $ inr func
    end.
  pose decode v :=
    match v with
    | inl () =>
        Unit
    | inr (inl n) =>
        Int n
    | inr (inr (inl b)) =>
        Bool b
    | inr (inr (inr (inl l))) =>
        Loc l
    | inr (inr (inr (inr func))) =>
        Func func
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.
#[global] Instance val_inhabited : Inhabited val :=
  populate (Int inhabitant).

Definition val_well_formed (funcs : gset function) v :=
  match v with
  | Loc _ =>
      False
  | Func func =>
      func ∈ funcs
  | _ =>
      True
  end.

#[global] Instance val_similar : Similar val val :=
  λ v1 v2,
    match v1, v2 with
    | Unit, Unit =>
        True
    | Int i1, Int i2 =>
        i1 = i2
    | Loc _, Loc _ =>
        True
    | Func func1, Func func2 =>
        func1 = func2
    | _, _ =>
        False
    end.

Inductive unop :=
  | OpNeg | OpUminus.

#[global] Instance unop_eq_dec : EqDecision unop :=
  ltac:(solve_decision).
#[global] Instance unop_countable :
  Countable unop.
Proof.
  pose encode op :=
    match op with
    | OpNeg => 0
    | OpUminus => 1
    end.
  pose decode op :=
    match op with
    | 0 => OpNeg
    | _ => OpUminus
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive binop :=
  | OpPlus | OpMinus | OpMult | OpQuot | OpRem
  | OpLe | OpLt | OpEq
  | OpOffset.

#[global] Instance binop_eq_dec : EqDecision binop :=
  ltac:(solve_decision).
#[global] Instance binop_countable :
  Countable binop.
Proof.
  pose encode op :=
    match op with
    | OpPlus => 0
    | OpMinus => 1
    | OpMult => 2
    | OpQuot => 3
    | OpRem => 4
    | OpLe => 5
    | OpLt => 6
    | OpEq => 7
    | OpOffset => 8
    end.
  pose decode op :=
    match op with
    | 0 => OpPlus
    | 1 => OpMinus
    | 2 => OpMult
    | 3 => OpQuot
    | 4 => OpRem
    | 5 => OpLe
    | 6 => OpLt
    | 7 => OpEq
    | _ => OpOffset
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.

Inductive expr :=
  | Val (v : val)
  | Var (x : var)
  | Let (e1 : expr) (e2 : {bind expr})
  | Call (e1 e2 : expr)
  | Unop (op : unop) (e : expr)
  | Binop (op : binop) (e1 e2 : expr)
  | If (e0 e1 e2 : expr)
  | Constr (constr : constructor) (e1 e2 : expr)
  | ConstrDet (constr : constructor) (e1 e2 : expr)
  | Load (e : expr)
  | Store (e1 e2 : expr).

#[global] Instance expr_eq_dec : EqDecision expr :=
  ltac:(solve_decision).
#[global] Instance expr_countable :
  Countable expr.
Proof.
  pose fix encode e :=
    match e with
    | Val v =>
        GenLeaf (inl v)
    | Var x =>
        GenLeaf (inr (inl x))
    | Let e1 e2 =>
        GenNode 0 [encode e1; encode e2]
    | Call e1 e2 =>
        GenNode 1 [encode e1; encode e2]
    | Unop op e =>
        GenNode 2 [GenLeaf (inr (inr (inl op))); encode e]
    | Binop op e1 e2 =>
        GenNode 3 [GenLeaf (inr (inr (inr (inl op)))); encode e1; encode e2]
    | If e0 e1 e2 =>
        GenNode 4 [encode e0; encode e1; encode e2]
    | Constr constr e1 e2 =>
        GenNode 5 [GenLeaf (inr (inr (inr (inr constr)))); encode e1; encode e2]
    | ConstrDet constr e1 e2 =>
        GenNode 6 [GenLeaf (inr (inr (inr (inr constr)))); encode e1; encode e2]
    | Load e =>
        GenNode 7 [encode e]
    | Store e1 e2 =>
        GenNode 8 [encode e1; encode e2]
    end.
  pose fix decode e :=
    match e with
    | GenLeaf (inl v) =>
        Val v
    | GenLeaf (inr (inl x)) =>
        Var x
    | GenNode 0 [e1; e2] =>
        Let (decode e1) (decode e2)
    | GenNode 1 [e1; e2] =>
        Call (decode e1) (decode e2)
    | GenNode 2 [GenLeaf (inr (inr (inl op))); e] =>
        Unop op (decode e)
    | GenNode 3 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] =>
        Binop op (decode e1) (decode e2)
    | GenNode 4 [e0; e1; e2] =>
        If (decode e0) (decode e1) (decode e2)
    | GenNode 5 [GenLeaf (inr (inr (inr (inr constr)))); e1; e2] =>
        Constr constr (decode e1) (decode e2)
    | GenNode 6 [GenLeaf (inr (inr (inr (inr constr)))); e1; e2] =>
        ConstrDet constr (decode e1) (decode e2)
    | GenNode 7 [e] =>
        Load (decode e)
    | GenNode 8 [e1; e2] =>
        Store (decode e1) (decode e2)
    | _ =>
        Val (Int 0)
    end.
  apply (inj_countable' encode decode). intros e. induction e; simpl; congruence.
Qed.
#[global] Instance expr_inhabited : Inhabited expr :=
  populate (Val inhabitant).

Fixpoint expr_well_formed funcs lvl e :=
  match e with
  | Val v =>
      val_well_formed funcs v
  | Var x =>
      x ≤ lvl
  | Let e1 e2 =>
      expr_well_formed funcs lvl e1 ∧
      expr_well_formed funcs (S lvl) e2
  | Call e1 e2 =>
      expr_well_formed funcs lvl e1 ∧
      expr_well_formed funcs lvl e2
  | Unop _ e =>
      expr_well_formed funcs lvl e
  | Binop _ e1 e2 =>
      expr_well_formed funcs lvl e1 ∧
      expr_well_formed funcs lvl e2
  | If e0 e1 e2 =>
      expr_well_formed funcs lvl e0 ∧
      expr_well_formed funcs lvl e1 ∧
      expr_well_formed funcs lvl e2
  | Constr constr e1 e2 =>
      expr_well_formed funcs lvl e1 ∧
      expr_well_formed funcs lvl e2
  | ConstrDet _ _ _ =>
      False
  | Load e =>
      expr_well_formed funcs lvl e
  | Store e1 e2 =>
      expr_well_formed funcs lvl e1 ∧
      expr_well_formed funcs lvl e2
  end.

#[global] Instance expr_ids : Ids expr. derive. Defined.
#[global] Instance expr_rename : Rename expr. derive. Defined.
#[global] Instance expr_subst : Subst expr. derive. Defined.
#[global] Instance expr_subst_lemmas : SubstLemmas expr. derive. Qed.

Definition program := gmap function expr.

Definition program_well_formed (prog : program) :=
  map_Forall (λ _, expr_well_formed (dom prog) 0) prog.
