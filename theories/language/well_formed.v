From simuliris Require Import
  prelude.
From simuliris.language Require Export
  syntax.

Implicit Types prog : program.

Definition val_well_formed prog v :=
  match v with
  | Loc _ =>
      False
  | Func func =>
      func ∈ dom prog
  | _ =>
      True
  end.

Fixpoint expr_well_formed prog lvl e :=
  match e with
  | Val v =>
      val_well_formed prog v
  | Var x =>
      x ≤ lvl
  | Let e1 e2 =>
      expr_well_formed prog lvl e1 ∧
      expr_well_formed prog (S lvl) e2
  | Call e1 e2 =>
      expr_well_formed prog lvl e1 ∧
      expr_well_formed prog lvl e2
  | Unop _ e =>
      expr_well_formed prog lvl e
  | Binop _ e1 e2 =>
      expr_well_formed prog lvl e1 ∧
      expr_well_formed prog lvl e2
  | If e0 e1 e2 =>
      expr_well_formed prog lvl e0 ∧
      expr_well_formed prog lvl e1 ∧
      expr_well_formed prog lvl e2
  | Constr constr e1 e2 =>
      expr_well_formed prog lvl e1 ∧
      expr_well_formed prog lvl e2
  | ConstrDet _ _ _ =>
      False
  | Load e1 e2 =>
      expr_well_formed prog lvl e1 ∧
      expr_well_formed prog lvl e2
  | Store e1 e2 e3 =>
      expr_well_formed prog lvl e1 ∧
      expr_well_formed prog lvl e2 ∧
      expr_well_formed prog lvl e3
  end.

Definition expr_well_formed' prog e :=
  ∃ lvl, expr_well_formed prog lvl e.

Definition program_well_formed prog :=
  map_Forall (λ _, expr_well_formed prog 0) prog.

