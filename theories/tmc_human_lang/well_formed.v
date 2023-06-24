From simuliris Require Import
  prelude.
From simuliris.tmc_human_lang Require Export
  syntax.

Implicit Types prog : human_program.

Definition human_val_well_formed prog v :=
  match v with
  | HumanFunc func =>
      func ∈ dom prog
  | _ =>
      True
  end.

Fixpoint human_expr_well_formed prog e :=
  match e with
  | HumanVal v =>
      human_val_well_formed prog v
  | HumanVar _ =>
      True
  | HumanLet _ e1 e2 =>
      human_expr_well_formed prog e1 ∧
      human_expr_well_formed prog e2
  | HumanCall e1 e2 =>
      human_expr_well_formed prog e1 ∧
      human_expr_well_formed prog e2
  | HumanUnop _ e =>
      human_expr_well_formed prog e
  | HumanBinop _ e1 e2 =>
      human_expr_well_formed prog e1 ∧
      human_expr_well_formed prog e2
  | HumanIf e0 e1 e2 =>
      human_expr_well_formed prog e0 ∧
      human_expr_well_formed prog e1 ∧
      human_expr_well_formed prog e2
  | HumanConstr _ e1 e2 =>
      human_expr_well_formed prog e1 ∧
      human_expr_well_formed prog e2
  | HumanLoad e1 e2 =>
      human_expr_well_formed prog e1 ∧
      human_expr_well_formed prog e2
  | HumanStore e1 e2 e3 =>
      human_expr_well_formed prog e1 ∧
      human_expr_well_formed prog e2 ∧
      human_expr_well_formed prog e3
  end.

Definition human_program_well_formed prog :=
  map_Forall (λ _ '(_, e), human_expr_well_formed prog e) prog.
