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
      x < lvl
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
  map_Forall (λ _, expr_well_formed prog 1) prog.

Lemma subst_expr_well_formed ς1 ς2 prog lvl e :
  (∀ x, x < lvl → ς1 x = ς2 x) →
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
Lemma subst_expr_well_formed_0 ς1 ς2 prog e :
  expr_well_formed prog 0 e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hwf.
  eapply subst_expr_well_formed; last done.
  lia.
Qed.
Lemma subst_expr_well_formed_1 ς1 ς2 prog e :
  ς1 0 = ς2 0 →
  expr_well_formed prog 1 e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hς Hwf.
  eapply subst_expr_well_formed; last done.
  setoid_rewrite Nat.lt_1_r. naive_solver.
Qed.
Lemma subst_expr_well_formed_1' ς1 ς2 v prog e :
  expr_well_formed prog 1 e →
  e.[v .: ς1] = e.[v .: ς2].
Proof.
  apply subst_expr_well_formed_1. done.
Qed.
Lemma subst_program_well_formed ς1 ς2 prog func e :
  ς1 0 = ς2 0 →
  program_well_formed prog →
  prog !! func = Some e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hσ Hwf Hlookup.
  eapply subst_expr_well_formed_1; first done.
  pose proof (map_Forall_lookup_1 _ _ _ _ Hwf Hlookup). eauto.
Qed.
Lemma subst_program_well_formed' ς1 ς2 v prog func e :
  program_well_formed prog →
  prog !! func = Some e →
  e.[v .: ς1] = e.[v .: ς2].
Proof.
  apply subst_program_well_formed. done.
Qed.

Lemma expr_well_formed_le prog lvl1 lvl2 e :
  lvl1 ≤ lvl2 →
  expr_well_formed prog lvl1 e →
  expr_well_formed prog lvl2 e.
Proof.
  revert lvl1 lvl2. elim e; try naive_solver lia.
  intros e1 IH1 e2 IH2 lvl1 lvl2 Hlvl (Hwf1 & Hwf2).
  split; first naive_solver. eapply IH2; last done. lia.
Qed.

Lemma expr_well_formed_upn_subst_val n v prog lvl e :
  n < lvl →
  val_well_formed prog v →
  expr_well_formed prog lvl e →
  expr_well_formed prog (lvl - 1) e.[upn n (Val v .: ids)].
Proof.
  revert n lvl. induction e; intros n lvl; try naive_solver; simpl.
  - intros Hn Hv Hx.
    destruct (Nat.lt_ge_cases x n) as [Hx' | (dx & ->)%Nat.le_sum].
    + rewrite upn_lt //=. lia.
    + rewrite upn_ge; first lia.
      rewrite Nat.sub_add'. destruct dx; first done. simpl. lia.
  - intros Hn Hv (Hwf1 & Hwf2). split; first naive_solver.
    rewrite fold_up_upn.
    destruct lvl; first lia.
    rewrite /= Nat.sub_0_r -(Nat.pred_succ (S lvl)) -Nat.sub_1_r.
    auto with lia.
Qed.
Lemma expr_well_formed_subst_val prog lvl e v :
  val_well_formed prog v →
  expr_well_formed prog lvl e →
  expr_well_formed prog (lvl - 1) e.[Val v/].
Proof.
  destruct lvl.
  - intros Hv Hwf%(expr_well_formed_le _ _ 1)%(expr_well_formed_upn_subst_val 0 v); naive_solver lia.
  - apply (expr_well_formed_upn_subst_val 0). lia.
Qed.

Lemma expr_well_formed_ren ξ n prog lvl e :
  (∀ x, ξ x ≤ x + n) →
  expr_well_formed prog lvl e →
  expr_well_formed prog (lvl + n) e.[ren ξ].
Proof.
  revert lvl ξ n. elim e; try naive_solver lia.
  - intros x lvl ξ n Hξ Hwf.
    eapply (Nat.le_lt_trans _ (x + n)); naive_solver lia.
  - intros e1 IH1 e2 IH2 lvl ξ n Hξ (Hwf1 & Hwf2).
    split; first naive_solver.
    asimpl. rewrite -Nat.add_succ_l. apply IH2; last done.
    intros []; simpl; [lia | rewrite -Nat.succ_le_mono //].
Qed.
Lemma expr_well_formed_lift n prog lvl e :
  expr_well_formed prog lvl e →
  expr_well_formed prog (lvl + n) e.[ren (+n)].
Proof.
  apply expr_well_formed_ren. naive_solver lia.
Qed.
Lemma expr_well_formed_lift1 prog lvl e :
  expr_well_formed prog lvl e →
  expr_well_formed prog (S lvl) e.[ren (+1)].
Proof.
  rewrite -Nat.add_1_r. apply expr_well_formed_lift.
Qed.
