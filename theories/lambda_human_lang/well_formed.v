From simuliris Require Import
  prelude.
From simuliris.lambda_human_lang Require Export
  syntax.

Implicit Types prog : lambda_human_program.

Definition lambda_human_val_well_formed prog v :=
  match v with
  | LambdaHumanFunc func =>
      func ∈ dom prog
  | _ =>
      True
  end.

Fixpoint lambda_human_expr_well_formed prog e :=
  match e with
  | LambdaHumanVal v =>
      lambda_human_val_well_formed prog v
  | LambdaHumanVar _ =>
      True
  | LambdaHumanLet _ e1 e2 =>
      lambda_human_expr_well_formed prog e1 ∧
      lambda_human_expr_well_formed prog e2
  | LambdaHumanCall e1 e2 =>
      lambda_human_expr_well_formed prog e1 ∧
      lambda_human_expr_well_formed prog e2
  | LambdaHumanUnop _ e =>
      lambda_human_expr_well_formed prog e
  | LambdaHumanBinop _ e1 e2 =>
      lambda_human_expr_well_formed prog e1 ∧
      lambda_human_expr_well_formed prog e2
  | LambdaHumanIf e0 e1 e2 =>
      lambda_human_expr_well_formed prog e0 ∧
      lambda_human_expr_well_formed prog e1 ∧
      lambda_human_expr_well_formed prog e2
  | LambdaHumanConstr _ e1 e2 =>
      lambda_human_expr_well_formed prog e1 ∧
      lambda_human_expr_well_formed prog e2
  | LambdaHumanLoad e1 e2 =>
      lambda_human_expr_well_formed prog e1 ∧
      lambda_human_expr_well_formed prog e2
  | LambdaHumanStore e1 e2 e3 =>
      lambda_human_expr_well_formed prog e1 ∧
      lambda_human_expr_well_formed prog e2 ∧
      lambda_human_expr_well_formed prog e3
  end.

Definition lambda_human_program_well_formed prog :=
  map_Forall (λ _ '(_, e), lambda_human_expr_well_formed prog e) prog.
