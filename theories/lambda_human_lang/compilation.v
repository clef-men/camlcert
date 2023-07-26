From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  metatheory.
From simuliris.lambda_lang Require Import
  notations.
From simuliris.lambda_human_lang Require Export
  metatheory.

Definition lambda_human_bindings := list binder.
Implicit Types bdgs : lambda_human_bindings.

Fixpoint lambda_human_bindings_lookup_aux i bdgs x :=
  match bdgs with
  | [] =>
      None
  | y :: bdgs =>
      if bool_decide (y = BNamed x)
      then Some i
      else lambda_human_bindings_lookup_aux (S i) bdgs x
  end.
Definition lambda_human_bindings_lookup bdgs x :=
  lambda_human_bindings_lookup_aux 0 bdgs x.

Definition lambda_human_val_compile v :=
  match v with
  | LambdaHumanUnit =>
      LambdaUnit
  | LambdaHumanIndex idx =>
      LambdaIndex idx
  | LambdaHumanTag tag =>
      LambdaTag tag
  | LambdaHumanInt n =>
      LambdaInt n
  | LambdaHumanBool b =>
      LambdaBool b
  | LambdaHumanFunc func =>
      LambdaFunc func
  end.

Fixpoint lambda_human_expr_compile bdgs e :=
  match e with
  | LambdaHumanVal v =>
      LambdaVal (lambda_human_val_compile v)
  | LambdaHumanVar x =>
      from_option LambdaVar Fail%lambda_expr (lambda_human_bindings_lookup bdgs x)
  | LambdaHumanLet x e1 e2 =>
      LambdaLet
        (lambda_human_expr_compile bdgs e1)
        (lambda_human_expr_compile (x :: bdgs) e2)
  | LambdaHumanCall e1 e2 =>
      LambdaCall
        (lambda_human_expr_compile bdgs e1)
        (lambda_human_expr_compile bdgs e2)
  | LambdaHumanUnop op e =>
      LambdaUnop op
        (lambda_human_expr_compile bdgs e)
  | LambdaHumanBinop op e1 e2 =>
      LambdaBinop op
        (lambda_human_expr_compile bdgs e1)
        (lambda_human_expr_compile bdgs e2)
  | LambdaHumanIf e0 e1 e2 =>
      LambdaIf
        (lambda_human_expr_compile bdgs e0)
        (lambda_human_expr_compile bdgs e1)
        (lambda_human_expr_compile bdgs e2)
  | LambdaHumanConstr tag e1 e2 =>
      LambdaConstr tag
        (lambda_human_expr_compile bdgs e1)
        (lambda_human_expr_compile bdgs e2)
  | LambdaHumanLoad e1 e2 =>
      LambdaLoad
        (lambda_human_expr_compile bdgs e1)
        (lambda_human_expr_compile bdgs e2)
  | LambdaHumanStore e1 e2 e3 =>
      LambdaStore
        (lambda_human_expr_compile bdgs e1)
        (lambda_human_expr_compile bdgs e2)
        (lambda_human_expr_compile bdgs e3)
  end.

Definition lambda_human_program_compile (prog : lambda_human_program) : lambda_program :=
  (λ '(x, e), lambda_human_expr_compile [x] e) <$> prog.

Lemma lambda_human_val_compile_well_formed prog v :
  lambda_human_program_well_formed prog →
  lambda_human_val_well_formed prog v →
  lambda_val_well_formed (lambda_human_program_compile prog) (lambda_human_val_compile v).
Proof.
  intros Hprog Hv. destruct v; try done. rewrite /= dom_fmap_L //.
Qed.
Lemma lambda_human_expr_compile_well_formed prog bdgs e :
  lambda_human_program_well_formed prog →
  lambda_human_expr_well_formed prog e →
  lambda_expr_well_formed (lambda_human_program_compile prog) (lambda_human_expr_compile bdgs e).
Proof.
  intros Hprog He. revert bdgs. induction e; intros bdgs; try naive_solver; simpl.
  - apply lambda_human_val_compile_well_formed; done.
  - destruct (lambda_human_bindings_lookup bdgs _); done.
Qed.
Lemma lambda_human_program_compile_well_formed prog :
  lambda_human_program_well_formed prog →
  lambda_program_well_formed (lambda_human_program_compile prog).
Proof.
  intros Hprog. apply map_Forall_lookup. intros func ? ((x & e) & <- & Hfunc)%lookup_fmap_Some.
  apply lambda_human_expr_compile_well_formed; first done.
  rewrite /lambda_human_program_well_formed map_Forall_lookup in Hprog. naive_solver.
Qed.

Lemma lambda_human_bindings_lookup_aux_Some i bdgs x j :
  lambda_human_bindings_lookup_aux i bdgs x = Some j →
  i ≤ j < i + length bdgs.
Proof.
  revert i. induction bdgs as [| bdg bdgs]; simpl; intros i Hlookup; first done.
  case_bool_decide.
  - naive_solver lia.
  - apply IHbdgs in Hlookup. lia.
Qed.
Lemma lambda_human_bindings_lookup_Some bdgs x i :
  lambda_human_bindings_lookup bdgs x = Some i →
  i < length bdgs.
Proof.
  apply lambda_human_bindings_lookup_aux_Some.
Qed.

Lemma lambda_human_expr_compile_scope scope bdgs e :
  length bdgs = scope →
  lambda_expr_scope scope (lambda_human_expr_compile bdgs e).
Proof.
  revert scope bdgs. induction e; simpl; intros scope bdgs Hlength; try naive_solver.
  destruct (lambda_human_bindings_lookup _ _) eqn:Hlookup; last done.
  rewrite -Hlength. eapply lambda_human_bindings_lookup_Some. done.
Qed.
Lemma lambda_human_program_compile_scope prog :
  lambda_program_scope (lambda_human_program_compile prog).
Proof.
  apply map_Forall_lookup. intros func ? ((x & e) & <- & Hfunc)%lookup_fmap_Some.
  apply lambda_human_expr_compile_scope. done.
Qed.
