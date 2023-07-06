From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.program_logic Require Export
  ectxi_language.
From simuliris.lambda_lang Require Export
  semantics.

Implicit Types l : loc.
Implicit Types v w : lambda_val.
Implicit Types e : lambda_expr.
Implicit Types σ : lambda_state.

Notation lambda_of_val := LambdaVal.

Definition lambda_to_val e :=
  match e with
  | LambdaVal v => Some v
  | _ => None
  end.

Canonical lambda_val_O := leibnizO lambda_val.
Canonical lambda_expr_O := leibnizO lambda_expr.
Canonical lambda_state_O := leibnizO lambda_state.

Inductive lambda_ectxi :=
  | LambdaEctxiLet e2
  | LambdaEctxiCall1 e1
  | LambdaEctxiCall2 v2
  | LambdaEctxiUnop (op : lambda_unop)
  | LambdaEctxiIf e1 e2
  | LambdaEctxiLoad1 e1
  | LambdaEctxiLoad2 v2
  | LambdaEctxiStore1 e1 e2
  | LambdaEctxiStore2 e1 v3
  | LambdaEctxiStore3 v2 v3.

Definition lambda_ectx := list lambda_ectxi.

Definition lambda_fill_item k e :=
  match k with
  | LambdaEctxiLet e2 =>
      LambdaLet e e2
  | LambdaEctxiCall1 e1 =>
      LambdaCall e1 e
  | LambdaEctxiCall2 v2 =>
      LambdaCall e (lambda_of_val v2)
  | LambdaEctxiUnop op =>
      LambdaUnop op e
  | LambdaEctxiIf e1 e2 =>
      LambdaIf e e1 e2
  | LambdaEctxiLoad1 e1 =>
      LambdaLoad e1 e
  | LambdaEctxiLoad2 v2 =>
      LambdaLoad e (lambda_of_val v2)
  | LambdaEctxiStore1 e1 e2 =>
      LambdaStore e1 e2 e
  | LambdaEctxiStore2 e1 v3 =>
      LambdaStore e1 e (lambda_of_val v3)
  | LambdaEctxiStore3 v2 v3 =>
      LambdaStore e (lambda_of_val v2) (lambda_of_val v3)
  end.
#[global] Instance lambda_ectxi_fill : Fill lambda_ectxi lambda_expr :=
  Build_Fill lambda_fill_item.

Lemma lambda_ectxi_lang_mixin :
  EctxiLanguageMixin
    lambda_of_val
    lambda_to_val
    lambda_head_step
    lambda_ectxi.
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
Canonical lambda_ectxi_lang :=
  Build_ectxi_language lambda_ectxi_lang_mixin.
Canonical lambda_ectx_lang :=
  ectx_language_of_ectxi_language lambda_ectxi_lang.
Canonical lambda_lang :=
  language_of_ectx_language lambda_ectx_lang.
