From simuliris Require Import
  prelude.
From simuliris.data_human_lang Require Export
  syntax.

Implicit Types prog : data_human_program.

Definition data_human_val_well_formed prog v :=
  match v with
  | DataHumanFunc func _ =>
      func ∈ dom prog
  | _ =>
      True
  end.

Fixpoint data_human_expr_well_formed prog e :=
  match e with
  | DataHumanVal v =>
      data_human_val_well_formed prog v
  | DataHumanVar _ =>
      True
  | DataHumanLet _ e1 e2 =>
      data_human_expr_well_formed prog e1 ∧
      data_human_expr_well_formed prog e2
  | DataHumanCall e1 e2 =>
      data_human_expr_well_formed prog e1 ∧
      data_human_expr_well_formed prog e2
  | DataHumanUnop _ e =>
      data_human_expr_well_formed prog e
  | DataHumanBinop _ e1 e2 =>
      data_human_expr_well_formed prog e1 ∧
      data_human_expr_well_formed prog e2
  | DataHumanIf e0 e1 e2 =>
      data_human_expr_well_formed prog e0 ∧
      data_human_expr_well_formed prog e1 ∧
      data_human_expr_well_formed prog e2
  | DataHumanBlock _ e1 e2 =>
      data_human_expr_well_formed prog e1 ∧
      data_human_expr_well_formed prog e2
  | DataHumanLoad e1 e2 =>
      data_human_expr_well_formed prog e1 ∧
      data_human_expr_well_formed prog e2
  | DataHumanStore e1 e2 e3 =>
      data_human_expr_well_formed prog e1 ∧
      data_human_expr_well_formed prog e2 ∧
      data_human_expr_well_formed prog e3
  end.

Definition data_human_program_well_formed prog :=
  map_Forall (λ _ def,
    data_human_expr_well_formed prog def.(data_human_definition_body)
  ) prog.
