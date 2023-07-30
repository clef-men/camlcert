From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  syntax.

Implicit Types prog : data_program.

Definition data_val_well_formed prog v :=
  match v with
  | DataLoc _ =>
      False
  | DataFunc func =>
      func ∈ dom prog
  | _ =>
      True
  end.

Fixpoint data_expr_well_formed prog e :=
  match e with
  | DataVal v =>
      data_val_well_formed prog v
  | DataVar _ =>
      True
  | DataLet e1 e2 =>
      data_expr_well_formed prog e1 ∧
      data_expr_well_formed prog e2
  | DataCall e1 e2 =>
      data_expr_well_formed prog e1 ∧
      data_expr_well_formed prog e2
  | DataUnop _ e =>
      data_expr_well_formed prog e
  | DataBinop _ e1 e2 =>
      data_expr_well_formed prog e1 ∧
      data_expr_well_formed prog e2
  | DataBinopDet _ _ _ =>
      False
  | DataIf e0 e1 e2 =>
      data_expr_well_formed prog e0 ∧
      data_expr_well_formed prog e1 ∧
      data_expr_well_formed prog e2
  | DataConstr _ e1 e2 =>
      data_expr_well_formed prog e1 ∧
      data_expr_well_formed prog e2
  | DataConstrDet _ _ _ =>
      False
  | DataLoad e1 e2 =>
      data_expr_well_formed prog e1 ∧
      data_expr_well_formed prog e2
  | DataStore e1 e2 e3 =>
      data_expr_well_formed prog e1 ∧
      data_expr_well_formed prog e2 ∧
      data_expr_well_formed prog e3
  end.

Fixpoint data_expr_scoped scope e :=
  match e with
  | DataVal _ =>
      True
  | DataVar x =>
      x < scope
  | DataLet e1 e2 =>
      data_expr_scoped scope e1 ∧
      data_expr_scoped (S scope) e2
  | DataCall e1 e2 =>
      data_expr_scoped scope e1 ∧
      data_expr_scoped scope e2
  | DataUnop _ e =>
      data_expr_scoped scope e
  | DataBinop _ e1 e2 =>
      data_expr_scoped scope e1 ∧
      data_expr_scoped scope e2
  | DataBinopDet _ e1 e2 =>
      data_expr_scoped scope e1 ∧
      data_expr_scoped scope e2
  | DataIf e0 e1 e2 =>
      data_expr_scoped scope e0 ∧
      data_expr_scoped scope e1 ∧
      data_expr_scoped scope e2
  | DataConstr _ e1 e2 =>
      data_expr_scoped scope e1 ∧
      data_expr_scoped scope e2
  | DataConstrDet _ e1 e2 =>
      data_expr_scoped scope e1 ∧
      data_expr_scoped scope e2
  | DataLoad e1 e2 =>
      data_expr_scoped scope e1 ∧
      data_expr_scoped scope e2
  | DataStore e1 e2 e3 =>
      data_expr_scoped scope e1 ∧
      data_expr_scoped scope e2 ∧
      data_expr_scoped scope e3
  end.

Definition data_program_well_formed prog :=
  map_Forall (λ _, data_expr_well_formed prog) prog.

Definition data_program_scoped prog :=
  map_Forall (λ _, data_expr_scoped 1) prog.

Definition data_program_valid prog :=
  data_program_well_formed prog ∧ data_program_scoped prog.

Lemma subst_data_expr_scoped ς1 ς2 scope e :
  (∀ x, x < scope → ς1 x = ς2 x) →
  data_expr_scoped scope e →
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
    intros ς1 ς2 scope Hς Hscoped;
    asimpl;
    try (f_equal; naive_solver).
  f_equal; first naive_solver.
  eapply IHe2; last naive_solver.
  intros x Hx. destruct x; first done. asimpl. f_equal. naive_solver lia.
Qed.
Lemma subst_data_expr_scoped_0 ς1 ς2 e :
  data_expr_scoped 0 e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hscoped.
  eapply subst_data_expr_scoped; last done.
  lia.
Qed.
Lemma subst_data_expr_scoped_1 ς1 ς2 e :
  ς1 0 = ς2 0 →
  data_expr_scoped 1 e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hς Hscoped.
  eapply subst_data_expr_scoped; last done.
  setoid_rewrite Nat.lt_1_r. naive_solver.
Qed.
Lemma subst_data_expr_scoped_1' ς1 ς2 v e :
  data_expr_scoped 1 e →
  e.[v .: ς1] = e.[v .: ς2].
Proof.
  apply subst_data_expr_scoped_1. done.
Qed.

Lemma subst_data_program_scoped ς1 ς2 prog func e :
  ς1 0 = ς2 0 →
  data_program_scoped prog →
  prog !! func = Some e →
  e.[ς1] = e.[ς2].
Proof.
  intros Hσ Hscoped Hlookup.
  eapply subst_data_expr_scoped_1; first done.
  eapply map_Forall_lookup_1 in Hscoped; naive_solver.
Qed.
Lemma subst_data_program_scoped' ς1 ς2 v prog func e :
  data_program_scoped prog →
  prog !! func = Some e →
  e.[v .: ς1] = e.[v .: ς2].
Proof.
  apply subst_data_program_scoped. done.
Qed.

Lemma data_expr_scoped_le scope1 scope2 e :
  scope1 ≤ scope2 →
  data_expr_scoped scope1 e →
  data_expr_scoped scope2 e.
Proof.
  revert scope1 scope2. elim e; try naive_solver lia.
  intros e1 IH1 e2 IH2 scope1 scope2 Hscoped (Hscoped1 & Hscoped2).
  split; first naive_solver. eapply IH2; last done. lia.
Qed.

Lemma data_expr_scoped_upn_subst_data_val n v scope e :
  n < scope →
  data_expr_scoped scope e →
  data_expr_scoped (scope - 1) e.[upn n (DataVal v .: ids)].
Proof.
  revert n scope. induction e; intros n scope; try naive_solver; simpl.
  - intros Hn Hx.
    destruct (Nat.lt_ge_cases x n) as [Hx' | (dx & ->)%Nat.le_sum].
    + rewrite upn_lt //=. lia.
    + rewrite upn_ge; first lia.
      rewrite Nat.sub_add'. destruct dx; first done. simpl. lia.
  - intros Hn (Hscoped1 & Hscoped2). split; first naive_solver.
    rewrite fold_up_upn.
    destruct scope; first lia.
    rewrite /= Nat.sub_0_r -(Nat.pred_succ (S scope)) -Nat.sub_1_r.
    auto with lia.
Qed.
Lemma data_expr_scoped_subst_data_val scope e v :
  data_expr_scoped scope e →
  data_expr_scoped (scope - 1) e.[DataVal v/].
Proof.
  destruct scope.
  - intros Hscoped%(data_expr_scoped_le _ 1)%(data_expr_scoped_upn_subst_data_val 0 v); naive_solver lia.
  - apply (data_expr_scoped_upn_subst_data_val 0). lia.
Qed.

Lemma data_expr_scoped_ren ξ n scope e :
  (∀ x, ξ x ≤ x + n) →
  data_expr_scoped scope e →
  data_expr_scoped (scope + n) e.[ren ξ].
Proof.
  revert scope ξ n. elim e; try naive_solver lia.
  - intros x scope ξ n Hξ Hscoped.
    eapply (Nat.le_lt_trans _ (x + n)); naive_solver lia.
  - intros e1 IH1 e2 IH2 scope ξ n Hξ (Hscoped1 & Hscoped2).
    split; first naive_solver.
    asimpl. rewrite -Nat.add_succ_l. apply IH2; last done.
    intros []; simpl; [lia | rewrite -Nat.succ_le_mono //].
Qed.
Lemma data_expr_scoped_lift n scope e :
  data_expr_scoped scope e →
  data_expr_scoped (scope + n) e.[ren (+n)].
Proof.
  apply data_expr_scoped_ren. naive_solver lia.
Qed.
Lemma data_expr_scoped_lift1 scope e :
  data_expr_scoped scope e →
  data_expr_scoped (S scope) e.[ren (+1)].
Proof.
  rewrite -Nat.add_1_r. apply data_expr_scoped_lift.
Qed.
