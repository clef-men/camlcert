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

Fixpoint lambda_expr_closed lvl e :=
  match e with
  | LambdaVal _ =>
      True
  | LambdaVar x =>
      x < lvl
  | LambdaLet e1 e2 =>
      lambda_expr_closed lvl e1 ∧
      lambda_expr_closed (S lvl) e2
  | LambdaCall e1 e2 =>
      lambda_expr_closed lvl e1 ∧
      lambda_expr_closed lvl e2
  | LambdaUnop _ e =>
      lambda_expr_closed lvl e
  | LambdaBinop _ e1 e2 =>
      lambda_expr_closed lvl e1 ∧
      lambda_expr_closed lvl e2
  | LambdaIf e0 e1 e2 =>
      lambda_expr_closed lvl e0 ∧
      lambda_expr_closed lvl e1 ∧
      lambda_expr_closed lvl e2
  | LambdaConstr _ e1 e2 =>
      lambda_expr_closed lvl e1 ∧
      lambda_expr_closed lvl e2
  | LambdaConstrDet _ _ _ =>
      False
  | LambdaLoad e1 e2 =>
      lambda_expr_closed lvl e1 ∧
      lambda_expr_closed lvl e2
  | LambdaStore e1 e2 e3 =>
      lambda_expr_closed lvl e1 ∧
      lambda_expr_closed lvl e2 ∧
      lambda_expr_closed lvl e3
  end.

Definition lambda_program_well_formed prog :=
  map_Forall (λ _, lambda_expr_well_formed prog) prog.

Definition lambda_program_closed prog :=
  map_Forall (λ _, lambda_expr_closed 1) prog.

Definition lambda_program_valid prog :=
  lambda_program_well_formed prog ∧ lambda_program_closed prog.

Lemma subst_lambda_expr_closed ς1 ς2 lvl e :
  (∀ x, x < lvl → ς1 x = ς2 x) →
  lambda_expr_closed lvl e →
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
    intros ς1 ς2 lvl Hς Hclosed;
    asimpl;
    try (f_equal; naive_solver).
  f_equal; first naive_solver.
  eapply IHe2; last naive_solver.
  intros x Hx. destruct x; first done. asimpl. f_equal. naive_solver lia.
Qed.
Lemma subst_lambda_expr_closed_0 ς1 ς2 e :
  lambda_expr_closed 0 e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hclosed.
  eapply subst_lambda_expr_closed; last done.
  lia.
Qed.
Lemma subst_lambda_expr_closed_1 ς1 ς2 e :
  ς1 0 = ς2 0 →
  lambda_expr_closed 1 e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hς Hclosed.
  eapply subst_lambda_expr_closed; last done.
  setoid_rewrite Nat.lt_1_r. naive_solver.
Qed.
Lemma subst_lambda_expr_closed_1' ς1 ς2 v e :
  lambda_expr_closed 1 e →
  e.[v .: ς1] = e.[v .: ς2].
Proof.
  apply subst_lambda_expr_closed_1. done.
Qed.

Lemma subst_lambda_program_closed ς1 ς2 prog func e :
  ς1 0 = ς2 0 →
  lambda_program_closed prog →
  prog !! func = Some e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hσ Hwf Hlookup.
  eapply subst_lambda_expr_closed_1; first done.
  eapply map_Forall_lookup_1 in Hwf; naive_solver.
Qed.
Lemma subst_lambda_program_closed' ς1 ς2 v prog func e :
  lambda_program_closed prog →
  prog !! func = Some e →
  e.[v .: ς1] = e.[v .: ς2].
Proof.
  apply subst_lambda_program_closed. done.
Qed.

Lemma lambda_expr_closed_le lvl1 lvl2 e :
  lvl1 ≤ lvl2 →
  lambda_expr_closed lvl1 e →
  lambda_expr_closed lvl2 e.
Proof.
  revert lvl1 lvl2. elim e; try naive_solver lia.
  intros e1 IH1 e2 IH2 lvl1 lvl2 Hlvl (Hclosed1 & Hclosed2).
  split; first naive_solver. eapply IH2; last done. lia.
Qed.

Lemma lambda_expr_closed_upn_subst_lambda_val n v lvl e :
  n < lvl →
  lambda_expr_closed lvl e →
  lambda_expr_closed (lvl - 1) e.[upn n (LambdaVal v .: ids)].
Proof.
  revert n lvl. induction e; intros n lvl; try naive_solver; simpl.
  - intros Hn Hx.
    destruct (Nat.lt_ge_cases x n) as [Hx' | (dx & ->)%Nat.le_sum].
    + rewrite upn_lt //=. lia.
    + rewrite upn_ge; first lia.
      rewrite Nat.sub_add'. destruct dx; first done. simpl. lia.
  - intros Hn (Hclosed1 & Hclosed2). split; first naive_solver.
    rewrite fold_up_upn.
    destruct lvl; first lia.
    rewrite /= Nat.sub_0_r -(Nat.pred_succ (S lvl)) -Nat.sub_1_r.
    auto with lia.
Qed.
Lemma lambda_expr_closed_subst_lambda_val lvl e v :
  lambda_expr_closed lvl e →
  lambda_expr_closed (lvl - 1) e.[LambdaVal v/].
Proof.
  destruct lvl.
  - intros Hclosed%(lambda_expr_closed_le _ 1)%(lambda_expr_closed_upn_subst_lambda_val 0 v); naive_solver lia.
  - apply (lambda_expr_closed_upn_subst_lambda_val 0). lia.
Qed.

Lemma lambda_expr_closed_ren ξ n lvl e :
  (∀ x, ξ x ≤ x + n) →
  lambda_expr_closed lvl e →
  lambda_expr_closed (lvl + n) e.[ren ξ].
Proof.
  revert lvl ξ n. elim e; try naive_solver lia.
  - intros x lvl ξ n Hξ Hclosed.
    eapply (Nat.le_lt_trans _ (x + n)); naive_solver lia.
  - intros e1 IH1 e2 IH2 lvl ξ n Hξ (Hclosed1 & Hclosed2).
    split; first naive_solver.
    asimpl. rewrite -Nat.add_succ_l. apply IH2; last done.
    intros []; simpl; [lia | rewrite -Nat.succ_le_mono //].
Qed.
Lemma lambda_expr_closed_lift n lvl e :
  lambda_expr_closed lvl e →
  lambda_expr_closed (lvl + n) e.[ren (+n)].
Proof.
  apply lambda_expr_closed_ren. naive_solver lia.
Qed.
Lemma lambda_expr_closed_lift1 lvl e :
  lambda_expr_closed lvl e →
  lambda_expr_closed (S lvl) e.[ren (+1)].
Proof.
  rewrite -Nat.add_1_r. apply lambda_expr_closed_lift.
Qed.
