From simuliris Require Import
  prelude.
From simuliris.iris.program_logic Require Export
  ectxi_language.
From simuliris.data_lang Require Export
  semantics.

Implicit Types l : loc.
Implicit Types v w : data_val.
Implicit Types e : data_expr.
Implicit Types σ : data_state.

Notation data_of_val :=
  DataVal.

Definition data_to_val e :=
  match e with
  | DataVal v => Some v
  | _ => None
  end.

Canonical data_val_O :=
  leibnizO data_val.
Canonical data_expr_O :=
  leibnizO data_expr.
Canonical data_state_O :=
  leibnizO data_state.

Inductive data_ectxi :=
  | DataEctxiLet e2
  | DataEctxiCall1 e1
  | DataEctxiCall2 v2
  | DataEctxiUnop (op : data_unop)
  | DataEctxiIf e1 e2
  | DataEctxiLoad1 e1
  | DataEctxiLoad2 v2
  | DataEctxiStore1 e1 e2
  | DataEctxiStore2 e1 v3
  | DataEctxiStore3 v2 v3.

Definition data_ectx :=
  list data_ectxi.

Definition data_fill_item k e :=
  match k with
  | DataEctxiLet e2 =>
      DataLet e e2
  | DataEctxiCall1 e1 =>
      DataCall e1 e
  | DataEctxiCall2 v2 =>
      DataCall e (data_of_val v2)
  | DataEctxiUnop op =>
      DataUnop op e
  | DataEctxiIf e1 e2 =>
      DataIf e e1 e2
  | DataEctxiLoad1 e1 =>
      DataLoad e1 e
  | DataEctxiLoad2 v2 =>
      DataLoad e (data_of_val v2)
  | DataEctxiStore1 e1 e2 =>
      DataStore e1 e2 e
  | DataEctxiStore2 e1 v3 =>
      DataStore e1 e (data_of_val v3)
  | DataEctxiStore3 v2 v3 =>
      DataStore e (data_of_val v2) (data_of_val v3)
  end.
#[global] Instance data_ectxi_fill : Fill data_ectxi data_expr :=
  Build_Fill data_fill_item.

Lemma data_ectxi_lang_mixin :
  EctxiLanguageMixin
    data_of_val
    data_to_val
    data_head_step
    data_ectxi.
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
Canonical data_ectxi_lang :=
  Build_ectxi_language data_ectxi_lang_mixin.
Canonical data_ectx_lang :=
  ectx_language_of_ectxi_language data_ectxi_lang.
Canonical data_lang :=
  language_of_ectx_language data_ectx_lang.
