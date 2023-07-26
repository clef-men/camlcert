From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  syntax.

Implicit Types prog : lambda_program.

Definition lambda_val_well_formed prog v :=
  match v with
  | LambdaLoc _ =>
      False
  | LambdaFunc func =>
      func ∈ dom prog
  | _ =>
      True
  end.

Fixpoint lambda_expr_well_formed prog e :=
  match e with
  | LambdaVal v =>
      lambda_val_well_formed prog v
  | LambdaVar _ =>
      True
  | LambdaLet e1 e2 =>
      lambda_expr_well_formed prog e1 ∧
      lambda_expr_well_formed prog e2
  | LambdaCall e1 e2 =>
      lambda_expr_well_formed prog e1 ∧
      lambda_expr_well_formed prog e2
  | LambdaUnop _ e =>
      lambda_expr_well_formed prog e
  | LambdaBinop _ e1 e2 =>
      lambda_expr_well_formed prog e1 ∧
      lambda_expr_well_formed prog e2
  | LambdaBinopDet _ _ _ =>
      False
  | LambdaIf e0 e1 e2 =>
      lambda_expr_well_formed prog e0 ∧
      lambda_expr_well_formed prog e1 ∧
      lambda_expr_well_formed prog e2
  | LambdaConstr _ e1 e2 =>
      lambda_expr_well_formed prog e1 ∧
      lambda_expr_well_formed prog e2
  | LambdaConstrDet _ _ _ =>
      False
  | LambdaLoad e1 e2 =>
      lambda_expr_well_formed prog e1 ∧
      lambda_expr_well_formed prog e2
  | LambdaStore e1 e2 e3 =>
      lambda_expr_well_formed prog e1 ∧
      lambda_expr_well_formed prog e2 ∧
      lambda_expr_well_formed prog e3
  end.

Fixpoint lambda_expr_scope scope e :=
  match e with
  | LambdaVal _ =>
      True
  | LambdaVar x =>
      x < scope
  | LambdaLet e1 e2 =>
      lambda_expr_scope scope e1 ∧
      lambda_expr_scope (S scope) e2
  | LambdaCall e1 e2 =>
      lambda_expr_scope scope e1 ∧
      lambda_expr_scope scope e2
  | LambdaUnop _ e =>
      lambda_expr_scope scope e
  | LambdaBinop _ e1 e2 =>
      lambda_expr_scope scope e1 ∧
      lambda_expr_scope scope e2
  | LambdaBinopDet _ e1 e2 =>
      lambda_expr_scope scope e1 ∧
      lambda_expr_scope scope e2
  | LambdaIf e0 e1 e2 =>
      lambda_expr_scope scope e0 ∧
      lambda_expr_scope scope e1 ∧
      lambda_expr_scope scope e2
  | LambdaConstr _ e1 e2 =>
      lambda_expr_scope scope e1 ∧
      lambda_expr_scope scope e2
  | LambdaConstrDet _ e1 e2 =>
      lambda_expr_scope scope e1 ∧
      lambda_expr_scope scope e2
  | LambdaLoad e1 e2 =>
      lambda_expr_scope scope e1 ∧
      lambda_expr_scope scope e2
  | LambdaStore e1 e2 e3 =>
      lambda_expr_scope scope e1 ∧
      lambda_expr_scope scope e2 ∧
      lambda_expr_scope scope e3
  end.

Definition lambda_program_well_formed prog :=
  map_Forall (λ _, lambda_expr_well_formed prog) prog.

Definition lambda_program_scope prog :=
  map_Forall (λ _, lambda_expr_scope 1) prog.

Definition lambda_program_valid prog :=
  lambda_program_well_formed prog ∧ lambda_program_scope prog.

Lemma subst_lambda_expr_scope ς1 ς2 scope e :
  (∀ x, x < scope → ς1 x = ς2 x) →
  lambda_expr_scope scope e →
  e.[ς1] = e.[ς2].
Proof.
  revert ς1 ς2 scope. induction e as
    [ v
    | x
    | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2
    | e IHe
    | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2
    | e0 IHe0 e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2
    | e1 IHe1 e2 IHe2 e3 IHe3
    ];
    intros ς1 ς2 scope Hς Hscope;
    asimpl;
    try (f_equal; naive_solver).
  f_equal; first naive_solver.
  eapply IHe2; last naive_solver.
  intros x Hx. destruct x; first done. asimpl. f_equal. naive_solver lia.
Qed.
Lemma subst_lambda_expr_scope_0 ς1 ς2 e :
  lambda_expr_scope 0 e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hscope.
  eapply subst_lambda_expr_scope; last done.
  lia.
Qed.
Lemma subst_lambda_expr_scope_1 ς1 ς2 e :
  ς1 0 = ς2 0 →
  lambda_expr_scope 1 e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hς Hscope.
  eapply subst_lambda_expr_scope; last done.
  setoid_rewrite Nat.lt_1_r. naive_solver.
Qed.
Lemma subst_lambda_expr_scope_1' ς1 ς2 v e :
  lambda_expr_scope 1 e →
  e.[v .: ς1] = e.[v .: ς2].
Proof.
  apply subst_lambda_expr_scope_1. done.
Qed.

Lemma subst_lambda_program_scope ς1 ς2 prog func e :
  ς1 0 = ς2 0 →
  lambda_program_scope prog →
  prog !! func = Some e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hσ Hwf Hlookup.
  eapply subst_lambda_expr_scope_1; first done.
  eapply map_Forall_lookup_1 in Hwf; naive_solver.
Qed.
Lemma subst_lambda_program_scope' ς1 ς2 v prog func e :
  lambda_program_scope prog →
  prog !! func = Some e →
  e.[v .: ς1] = e.[v .: ς2].
Proof.
  apply subst_lambda_program_scope. done.
Qed.

Lemma lambda_expr_scope_le scope1 scope2 e :
  scope1 ≤ scope2 →
  lambda_expr_scope scope1 e →
  lambda_expr_scope scope2 e.
Proof.
  revert scope1 scope2. elim e; try naive_solver lia.
  intros e1 IH1 e2 IH2 scope1 scope2 Hscope (Hscope1 & Hscope2).
  split; first naive_solver. eapply IH2; last done. lia.
Qed.

Lemma lambda_expr_scope_upn_subst_lambda_val n v scope e :
  n < scope →
  lambda_expr_scope scope e →
  lambda_expr_scope (scope - 1) e.[upn n (LambdaVal v .: ids)].
Proof.
  revert n scope. induction e; intros n scope; try naive_solver; simpl.
  - intros Hn Hx.
    destruct (Nat.lt_ge_cases x n) as [Hx' | (dx & ->)%Nat.le_sum].
    + rewrite upn_lt //=. lia.
    + rewrite upn_ge; first lia.
      rewrite Nat.sub_add'. destruct dx; first done. simpl. lia.
  - intros Hn (Hscope1 & Hscope2). split; first naive_solver.
    rewrite fold_up_upn.
    destruct scope; first lia.
    rewrite /= Nat.sub_0_r -(Nat.pred_succ (S scope)) -Nat.sub_1_r.
    auto with lia.
Qed.
Lemma lambda_expr_scope_subst_lambda_val scope e v :
  lambda_expr_scope scope e →
  lambda_expr_scope (scope - 1) e.[LambdaVal v/].
Proof.
  destruct scope.
  - intros Hscope%(lambda_expr_scope_le _ 1)%(lambda_expr_scope_upn_subst_lambda_val 0 v); naive_solver lia.
  - apply (lambda_expr_scope_upn_subst_lambda_val 0). lia.
Qed.

Lemma lambda_expr_scope_ren ξ n scope e :
  (∀ x, ξ x ≤ x + n) →
  lambda_expr_scope scope e →
  lambda_expr_scope (scope + n) e.[ren ξ].
Proof.
  revert scope ξ n. elim e; try naive_solver lia.
  - intros x scope ξ n Hξ Hscope.
    eapply (Nat.le_lt_trans _ (x + n)); naive_solver lia.
  - intros e1 IH1 e2 IH2 scope ξ n Hξ (Hscope1 & Hscope2).
    split; first naive_solver.
    asimpl. rewrite -Nat.add_succ_l. apply IH2; last done.
    intros []; simpl; [lia | rewrite -Nat.succ_le_mono //].
Qed.
Lemma lambda_expr_scope_lift n scope e :
  lambda_expr_scope scope e →
  lambda_expr_scope (scope + n) e.[ren (+n)].
Proof.
  apply lambda_expr_scope_ren. naive_solver lia.
Qed.
Lemma lambda_expr_scope_lift1 scope e :
  lambda_expr_scope scope e →
  lambda_expr_scope (S scope) e.[ren (+1)].
Proof.
  rewrite -Nat.add_1_r. apply lambda_expr_scope_lift.
Qed.
