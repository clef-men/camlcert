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

Lemma expr_well_formed_subst ς1 ς2 prog lvl e :
  (∀ x, x ≤ lvl → ς1 x = ς2 x) →
  expr_well_formed prog lvl e →
  e.[ς1] = e.[ς2].
Proof.
  revert ς1 ς2 lvl. induction e as
    [ v
    | x
    | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2
    | e IHe
    | e1 IHe1 e2 IHe2
    | e0 IHe0 e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2 e3 IHe3
    ];
    intros ς1 ς2 lvl Hς Hwf;
    asimpl;
    try (f_equal; naive_solver).
  f_equal; first naive_solver.
  eapply IHe2; last naive_solver.
  intros x Hx. destruct x; first done. asimpl. f_equal. naive_solver lia.
Qed.
Lemma expr_well_formed_0_subst ς1 ς2 prog e :
  ς1 0 = ς2 0 →
  expr_well_formed prog 0 e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hς Hwf.
  eapply expr_well_formed_subst; last done.
  setoid_rewrite Nat.le_0_r. naive_solver.
Qed.

Lemma program_well_formed_subst ς1 ς2 prog func e :
  ς1 0 = ς2 0 →
  program_well_formed prog →
  prog !! func = Some e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hσ Hwf Hlookup.
  eapply expr_well_formed_0_subst; first done.
  pose proof (map_Forall_lookup_1 _ _ _ _ Hwf Hlookup). eauto.
Qed.
