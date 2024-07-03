From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  metatheory.
From camlcert.data_lang Require Import
  notations.
From camlcert.data_human_lang Require Export
  metatheory.
From camlcert Require Import
  options.

Definition data_human_bindings :=
  list binder.
Implicit Types bdgs : data_human_bindings.

Fixpoint data_human_bindings_lookup_aux i bdgs x :=
  match bdgs with
  | [] =>
      None
  | y :: bdgs =>
      if bool_decide (y = BNamed x)
      then Some i
      else data_human_bindings_lookup_aux (S i) bdgs x
  end.
Definition data_human_bindings_lookup bdgs x :=
  data_human_bindings_lookup_aux 0 bdgs x.

Definition data_human_val_compile v :=
  match v with
  | DataHumanUnit =>
      DataUnit
  | DataHumanIndex idx =>
      DataIndex idx
  | DataHumanTag tag =>
      DataTag tag
  | DataHumanInt n =>
      DataInt n
  | DataHumanBool b =>
      DataBool b
  | DataHumanFunc func annot =>
      DataFunc func annot
  end.

Fixpoint data_human_expr_compile bdgs e :=
  match e with
  | DataHumanVal v =>
      DataVal (data_human_val_compile v)
  | DataHumanVar x =>
      from_option DataVar Fail%data_expr (data_human_bindings_lookup bdgs x)
  | DataHumanLet x e1 e2 =>
      DataLet
        (data_human_expr_compile bdgs e1)
        (data_human_expr_compile (x :: bdgs) e2)
  | DataHumanCall e1 e2 =>
      DataCall
        (data_human_expr_compile bdgs e1)
        (data_human_expr_compile bdgs e2)
  | DataHumanUnop op e =>
      DataUnop op
        (data_human_expr_compile bdgs e)
  | DataHumanBinop op e1 e2 =>
      DataBinop op
        (data_human_expr_compile bdgs e1)
        (data_human_expr_compile bdgs e2)
  | DataHumanIf e0 e1 e2 =>
      DataIf
        (data_human_expr_compile bdgs e0)
        (data_human_expr_compile bdgs e1)
        (data_human_expr_compile bdgs e2)
  | DataHumanBlock tag e1 e2 =>
      DataBlock tag
        (data_human_expr_compile bdgs e1)
        (data_human_expr_compile bdgs e2)
  | DataHumanLoad e1 e2 =>
      DataLoad
        (data_human_expr_compile bdgs e1)
        (data_human_expr_compile bdgs e2)
  | DataHumanStore e1 e2 e3 =>
      DataStore
        (data_human_expr_compile bdgs e1)
        (data_human_expr_compile bdgs e2)
        (data_human_expr_compile bdgs e3)
  end.

Definition data_human_program_compile (prog : data_human_program) : data_program :=
  (λ def,
    let annot := def.(data_human_definition_annot) in
    let param := def.(data_human_definition_param) in
    let body := def.(data_human_definition_body) in
    {|data_definition_annot := annot ;
      data_definition_body := data_human_expr_compile [param] body ;
    |}
  ) <$> prog.

Lemma data_human_val_compile_well_formed prog v :
  data_human_program_well_formed prog →
  data_human_val_well_formed prog v →
  data_val_well_formed (data_human_program_compile prog) (data_human_val_compile v).
Proof.
  intros Hprog Hv. destruct v; try done. rewrite /= dom_fmap_L //.
Qed.
Lemma data_human_expr_compile_well_formed prog bdgs e :
  data_human_program_well_formed prog →
  data_human_expr_well_formed prog e →
  data_expr_well_formed (data_human_program_compile prog) (data_human_expr_compile bdgs e).
Proof.
  intros Hprog He. revert bdgs. induction e; intros bdgs; try naive_solver; simpl.
  - apply data_human_val_compile_well_formed; done.
  - destruct (data_human_bindings_lookup bdgs _); done.
Qed.
Lemma data_human_program_compile_well_formed prog :
  data_human_program_well_formed prog →
  data_program_well_formed (data_human_program_compile prog).
Proof.
  intros Hprog. apply map_Forall_lookup. intros func ? (def & <- & Hfunc)%lookup_fmap_Some.
  apply data_human_expr_compile_well_formed; first done.
  rewrite /data_human_program_well_formed map_Forall_lookup in Hprog. naive_solver.
Qed.

Lemma data_human_bindings_lookup_aux_Some i bdgs x j :
  data_human_bindings_lookup_aux i bdgs x = Some j →
  i ≤ j < i + length bdgs.
Proof.
  revert i. induction bdgs as [| bdg bdgs]; simpl; intros i Hlookup; first done.
  case_bool_decide.
  - naive_solver lia.
  - apply IHbdgs in Hlookup. lia.
Qed.
Lemma data_human_bindings_lookup_Some bdgs x i :
  data_human_bindings_lookup bdgs x = Some i →
  i < length bdgs.
Proof.
  apply data_human_bindings_lookup_aux_Some.
Qed.

Lemma data_human_expr_compile_scoped scope bdgs e :
  length bdgs = scope →
  data_expr_scoped scope (data_human_expr_compile bdgs e).
Proof.
  revert scope bdgs. induction e; simpl; intros scope bdgs Hlength; try naive_solver.
  destruct (data_human_bindings_lookup _ _) eqn:Hlookup; last done.
  rewrite -Hlength. eapply data_human_bindings_lookup_Some. done.
Qed.
Lemma data_human_program_compile_scoped prog :
  data_program_scoped (data_human_program_compile prog).
Proof.
  apply map_Forall_lookup. intros func ? (def & <- & Hfunc)%lookup_fmap_Some.
  apply data_human_expr_compile_scoped. done.
Qed.
