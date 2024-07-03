From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  language.
From camlcert.data_lang Require Import
  ectx_decompositions
  metatheory.
From camlcert Require Import
  options.

Create HintDb data_lang.

#[global] Hint Extern 0 (
  reducible _ _ _
) => (
  eapply head_reducible_reducible
) : data_lang.
#[global] Hint Extern 0 (
  head_reducible _ _ _
) => (
  eexists _, _; simpl
) : data_lang.
#[global] Hint Extern 1 (
  data_head_step _ _ _ _ _
) => (
  econstructor
) : data_lang.
#[global] Hint Extern 1 (
  ectx_language.head_step _ _ _ _ _
) => (
  econstructor
) : data_lang.
#[global] Hint Extern 0 (
  data_head_step _ (DataBlockDet _ _ _) _ _ _
) => (
  eapply data_head_step_block_det'
) : data_lang.
#[global] Hint Extern 0 (
  ectx_language.head_step _ (DataBlockDet _ _ _) _ _ _
) => (
  eapply data_head_step_block_det'
) : data_lang.
#[global] Hint Extern 0 (
  pure_step _ _ _
) => (
  eapply pure_exec_pure_step; [apply _ |]
) : data_lang.
#[global] Hint Extern 0 (
  pure_head_step _ _ _
) => (
  eapply pure_head_exec_pure_head_step; [apply _ |]
) : data_lang.
#[global] Hint Extern 0 (
  strongly_stuck _ _
) => (
  eapply @is_strongly_stuck; [apply _ |]
) : data_lang.
#[global] Hint Extern 0 (
  strongly_head_stuck _ _
) => (
  eapply @is_strongly_head_stuck; [apply _ |]
) : data_lang.

#[global] Hint Extern 1 (
  sub_redexes_are_values _
) => (
  let Hdecomps := fresh "Hdecomps" in
  intros ?* Hdecomps%data_ectx_decompositions_spec;
    invert Hdecomps; first done;
    decompose_elem_of_list; simplify
) : data_lang.

Ltac data_expr_simplifier :=
  repeat_on_hyps ltac:(fun H =>
    match type of H with
    | data_val_well_formed _ ?v =>
        solve [by destruct v]
    | data_expr_well_formed _ _ =>
        simpl in H; destruct_and? H
    | data_expr_scoped _ _ =>
        simpl in H; destruct_and? H
    end
  );
  try done.
#[global] Hint Extern 0 => (
  solve [data_expr_simplifier]
) : data_lang.
#[global] Hint Extern 1 (
  data_expr_well_formed _ _
) => (
  progress data_expr_simplifier
) : data_lang.
#[global] Hint Extern 1 (
  data_expr_scoped _ _
) => (
  progress data_expr_simplifier
) : data_lang.

Ltac invert_data_head_step :=
  repeat_on_hyps ltac:(fun H =>
    let ty := type of H in
    let ty := eval simpl in ty in
    match ty with data_head_step _ ?e _ _ _ =>
      try (is_var e; fail 1);
      invert H
    end
  ).

#[local] Ltac solve_strongly_head_stuck :=
  split;
  [ intros ?** ?** ?; invert_data_head_step; done
  | auto with data_lang
  ].
#[global] Instance strongly_head_stuck_data_var prog x :
  IsStronglyHeadStuck prog
    True
    (DataVar x).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_data_call prog v1 v2 :
  IsStronglyHeadStuck prog
    (if v1 is DataFunc _ _ then False else True)
    (DataCall (DataVal v1) (DataVal v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_data_unop prog op v :
  IsStronglyHeadStuck prog
    (data_unop_eval op v = None)
    (DataUnop op (DataVal v)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_data_binop_det prog op v1 v2 :
  IsStronglyHeadStuck prog
    (data_binop_eval op v1 v2 = None)
    (DataBinopDet op (DataVal v1) (DataVal v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_data_if prog v0 e1 e2 :
  IsStronglyHeadStuck prog
    (if v0 is DataBool _ then False else True)
    (DataIf (DataVal v0) e1 e2).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_data_load_1 prog v1 v2 :
  IsStronglyHeadStuck prog
    (if (v1, v2) is (DataLoc _, DataIndex _) then False else True)
    (DataLoad (DataVal v1) (DataVal v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_data_store_1 prog v1 v2 v3 :
  IsStronglyHeadStuck prog
    (if (v1, v2) is (DataLoc _, DataIndex _) then False else True)
    (DataStore (DataVal v1) (DataVal v2) (DataVal v3)).
Proof.
  solve_strongly_head_stuck.
Qed.

#[local] Ltac solve_pure_head_exec :=
  intros ?; simplify; apply nsteps_once; constructor;
  [ auto with data_lang
  | intros; invert_data_head_step; auto
  ].
#[global] Instance pure_exec_data_let prog v e :
  PureHeadExec prog 1
    True
    (DataLet (DataVal v) e)
    e.[DataVal v/].
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_data_call prog func annot v e :
  PureHeadExec prog 1
    (∃ def, prog !! func = Some def ∧ e = def.(data_definition_body))
    (DataCall (DataVal (DataFunc func annot)) (DataVal v))
    e.[DataVal v/].
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_data_unop prog op v w :
  PureHeadExec prog 1
    (data_unop_eval op v = Some w)
    (DataUnop op (DataVal v))
    (DataVal w).
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_data_binop_det prog op v1 v2 w :
  PureHeadExec prog 1
    (data_binop_eval op v1 v2 = Some w)
    (DataBinopDet op (DataVal v1) (DataVal v2))
    (DataVal w).
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_data_if_true prog e1 e2 :
  PureHeadExec prog 1
    True
    (DataIf (DataVal (DataBool true)) e1 e2)
    e1.
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_data_if_false prog e1 e2 :
  PureHeadExec prog 1
    True
    (DataIf (DataVal (DataBool false)) e1 e2)
    e2.
Proof.
  solve_pure_head_exec.
Qed.
