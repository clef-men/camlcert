From simuliris Require Import
  prelude.
From simuliris.tmc_lang Require Export
  well_formed.
From simuliris.tmc_lang Require Import
  notations.
From simuliris.tmc_human_lang Require Export
  well_formed.

Definition bindings := list binder.
Implicit Types bdgs : bindings.

Fixpoint bindings_lookup_aux i bdgs x :=
  match bdgs with
  | [] =>
      None
  | y :: bdgs =>
      if bool_decide (y = BNamed x)
      then Some i
      else bindings_lookup_aux (S i) bdgs x
  end.
Definition bindings_lookup bdgs x :=
  bindings_lookup_aux 0 bdgs x.

Definition human_val_compile v :=
  match v with
  | HumanUnit =>
      Unit
  | HumanIndex idx =>
      Index idx
  | HumanInt n =>
      Int n
  | HumanBool b =>
      Bool b
  | HumanFunc func =>
      Func func
  end.

Fixpoint human_expr_compile bdgs e :=
  match e with
  | HumanVal v =>
      Val (human_val_compile v)
  | HumanVar x =>
      from_option Var Fail%E (bindings_lookup bdgs x)
  | HumanLet x e1 e2 =>
      Let
        (human_expr_compile bdgs e1)
        (human_expr_compile (x :: bdgs) e2)
  | HumanCall e1 e2 =>
      Call
        (human_expr_compile bdgs e1)
        (human_expr_compile bdgs e2)
  | HumanUnop op e =>
      Unop op
        (human_expr_compile bdgs e)
  | HumanBinop op e1 e2 =>
      Binop op
        (human_expr_compile bdgs e1)
        (human_expr_compile bdgs e2)
  | HumanIf e0 e1 e2 =>
      If
        (human_expr_compile bdgs e0)
        (human_expr_compile bdgs e1)
        (human_expr_compile bdgs e2)
  | HumanConstr constr e1 e2 =>
      Constr constr
        (human_expr_compile bdgs e1)
        (human_expr_compile bdgs e2)
  | HumanLoad e1 e2 =>
      Load
        (human_expr_compile bdgs e1)
        (human_expr_compile bdgs e2)
  | HumanStore e1 e2 e3 =>
      Store
        (human_expr_compile bdgs e1)
        (human_expr_compile bdgs e2)
        (human_expr_compile bdgs e3)
  end.

Definition human_program_compile (prog : human_program) : program :=
  (λ '(x, e), human_expr_compile [x] e) <$> prog.

Lemma human_val_compile_well_formed prog v :
  human_program_well_formed prog →
  human_val_well_formed prog v →
  val_well_formed (human_program_compile prog) (human_val_compile v).
Proof.
  intros Hprog Hv. destruct v; try done. rewrite /= dom_fmap_L //.
Qed.
Lemma human_expr_compile_well_formed prog e bdgs :
  human_program_well_formed prog →
  human_expr_well_formed prog e →
  expr_well_formed (human_program_compile prog) (human_expr_compile bdgs e).
Proof.
  intros Hprog He. revert bdgs. induction e; intros bdgs; try naive_solver; simpl.
  - apply human_val_compile_well_formed; done.
  - destruct (bindings_lookup bdgs _); done.
Qed.
Lemma human_program_compile_well_formed prog :
  human_program_well_formed prog →
  program_well_formed (human_program_compile prog).
Proof.
  intros Hprog. apply map_Forall_lookup.
  intros func e ((x & he) & <- & Hfunc)%lookup_fmap_Some.
  apply human_expr_compile_well_formed; first done.
  rewrite /human_program_well_formed map_Forall_lookup in Hprog. naive_solver.
Qed.
