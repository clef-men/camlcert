From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.program_logic Require Export
  ectxi_language.
From simuliris.tmc_lang Require Export
  semantics.

Implicit Types l : loc.
Implicit Types v w : val.
Implicit Types e : expr.
Implicit Types σ : state.

Notation of_val := Val.

Definition to_val e :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Canonical val_O := leibnizO val.
Canonical expr_O := leibnizO expr.
Canonical state_O := leibnizO state.

Inductive ectxi :=
  | EctxiLet e2
  | EctxiCall1 e1
  | EctxiCall2 v2
  | EctxiUnop (op : unop)
  | EctxiBinop1 (op : binop) e1
  | EctxiBinop2 (op : binop) v2
  | EctxiIf e1 e2
  | EctxiLoad1 e1
  | EctxiLoad2 v2
  | EctxiStore1 e1 e2
  | EctxiStore2 e1 v3
  | EctxiStore3 v2 v3.

Definition ectx := list ectxi.

Definition fill_item k e :=
  match k with
  | EctxiLet e2 =>
      Let e e2
  | EctxiCall1 e1 =>
      Call e1 e
  | EctxiCall2 v2 =>
      Call e (of_val v2)
  | EctxiUnop op =>
      Unop op e
  | EctxiBinop1 op e1 =>
      Binop op e1 e
  | EctxiBinop2 op v2 =>
      Binop op e (of_val v2)
  | EctxiIf e1 e2 =>
      If e e1 e2
  | EctxiLoad1 e1 =>
      Load e1 e
  | EctxiLoad2 v2 =>
      Load e (of_val v2)
  | EctxiStore1 e1 e2 =>
      Store e1 e2 e
  | EctxiStore2 e1 v3 =>
      Store e1 e (of_val v3)
  | EctxiStore3 v2 v3 =>
      Store e (of_val v2) (of_val v3)
  end.
#[global] Instance ectxi_fill : Fill ectxi expr :=
  Build_Fill fill_item.

Lemma tmc_ectxi_lang_mixin :
  EctxiLanguageMixin of_val to_val head_step ectxi.
Proof.
  split.
  - naive_solver.
  - intros []; naive_solver.
  - intros * []; naive_solver.
  - intros [] ?**; naive_solver.
  - intros []; naive_solver.
  - intros [] ? []; naive_solver.
  - intros ? [] * Hstep; invert Hstep; naive_solver.
Qed.
Canonical tmc_ectxi_lang :=
  Build_ectxi_language tmc_ectxi_lang_mixin.
Canonical tmc_ectx_lang :=
  ectx_language_of_ectxi_language tmc_ectxi_lang.
Canonical tmc_lang :=
  language_of_ectx_language tmc_ectx_lang.
