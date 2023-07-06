From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.lambda_lang Require Export
  language.
From simuliris.lambda_lang Require Import
  ectx_decompositions
  well_formed.

Create HintDb lambda_lang.

#[global] Hint Extern 0 (
  reducible _ _ _
) => (
  eapply head_reducible_reducible
) : lambda_lang.
#[global] Hint Extern 0 (
  head_reducible _ _ _
) => (
  eexists _, _; simpl
) : lambda_lang.
#[global] Hint Extern 1 (
  lambda_head_step _ _ _ _ _
) => (
  econstructor
) : lambda_lang.
#[global] Hint Extern 1 (
  ectx_language.head_step _ _ _ _ _
) => (
  econstructor
) : lambda_lang.
#[global] Hint Extern 0 (
  lambda_head_step _ (LambdaConstrDet _ _ _) _ _ _
) => (
  eapply lambda_head_step_constr_det'
) : lambda_lang.
#[global] Hint Extern 0 (
  ectx_language.head_step _ (LambdaConstrDet _ _ _) _ _ _
) => (
  eapply lambda_head_step_constr_det'
) : lambda_lang.
#[global] Hint Extern 0 (
  pure_step _ _ _
) => (
  eapply pure_exec_pure_step; [apply _ |]
) : lambda_lang.
#[global] Hint Extern 0 (
  pure_head_step _ _ _
) => (
  eapply pure_head_exec_pure_head_step; [apply _ |]
) : lambda_lang.
#[global] Hint Extern 0 (
  strongly_stuck _ _
) => (
  eapply @is_strongly_stuck; [apply _]
) : lambda_lang.
#[global] Hint Extern 0 (
  strongly_head_stuck _ _
) => (
  eapply @is_strongly_head_stuck; [apply _]
) : lambda_lang.

#[global] Hint Extern 1 (
  sub_redexes_are_values _
) => (
  let Hdecomps := fresh "Hdecomps" in
  intros ?* Hdecomps%lambda_ectx_decompositions_spec;
    invert Hdecomps; first done;
    decompose_elem_of_list; simplify
) : lambda_lang.

Ltac lambda_expr_simplifier :=
  repeat_on_hyps ltac:(fun H =>
    match type of H with
    | lambda_val_well_formed _ ?v =>
        solve [by destruct v]
    | lambda_expr_well_formed _ _ =>
        simpl in H; destruct_and? H
    | lambda_expr_closed _ _ =>
        simpl in H; destruct_and? H
    end
  );
  try done.
#[global] Hint Extern 0 => (
  solve [lambda_expr_simplifier]
) : lambda_lang.
#[global] Hint Extern 1 (
  lambda_expr_well_formed _ _
) => (
  progress lambda_expr_simplifier
) : lambda_lang.
#[global] Hint Extern 1 (
  lambda_expr_closed _ _
) => (
  progress lambda_expr_simplifier
) : lambda_lang.

Ltac invert_lambda_head_step :=
  repeat_on_hyps ltac:(fun H =>
    let ty := type of H in
    let ty := eval simpl in ty in
    match ty with lambda_head_step _ ?e _ _ _ =>
      try (is_var e; fail 1);
      invert H
    end
  ).

#[local] Ltac solve_strongly_head_stuck :=
  split;
  [ intros ?** ?** ?; invert_lambda_head_step; done
  | auto with lambda_lang
  ].
#[global] Instance strongly_head_stuck_lambda_var prog x :
  IsStronglyHeadStuck prog (LambdaVar x).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_lambda_call prog v1 v2 :
  (if v1 is LambdaFunc _ then False else True) →
  IsStronglyHeadStuck prog (LambdaCall (LambdaVal v1) (LambdaVal v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_lambda_unop prog op v :
  lambda_unop_eval op v = None →
  IsStronglyHeadStuck prog (LambdaUnop op (LambdaVal v)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_lambda_binop_det prog op v1 v2 :
  lambda_binop_eval op v1 v2 = None →
  IsStronglyHeadStuck prog (LambdaBinopDet op (LambdaVal v1) (LambdaVal v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_lambda_if prog v0 e1 e2 :
  (if v0 is LambdaBool _ then False else True) →
  IsStronglyHeadStuck prog (LambdaIf (LambdaVal v0) e1 e2).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_lambda_load_1 prog v1 v2 :
  (if v1 is LambdaLoc _ then False else True) →
  IsStronglyHeadStuck prog (LambdaLoad (LambdaVal v1) (LambdaVal v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_lambda_load_2 prog v1 v2 :
  (if v2 is LambdaIndex _ then False else True) →
  IsStronglyHeadStuck prog (LambdaLoad (LambdaVal v1) (LambdaVal v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_lambda_store_1 prog v1 v2 v3 :
  (if v1 is LambdaLoc _ then False else True) →
  IsStronglyHeadStuck prog (LambdaStore (LambdaVal v1) (LambdaVal v2) (LambdaVal v3)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_lambda_store_2 prog v1 v2 v3 :
  (if v2 is LambdaIndex _ then False else True) →
  IsStronglyHeadStuck prog (LambdaStore (LambdaVal v1) (LambdaVal v2) (LambdaVal v3)).
Proof.
  solve_strongly_head_stuck.
Qed.

#[local] Ltac solve_pure_head_exec :=
  intros ?; apply nsteps_once; constructor;
  [ auto with lambda_lang
  | intros; invert_lambda_head_step; auto
  ].
#[global] Instance pure_exec_lambda_let prog v e :
  PureHeadExec prog True 1 (LambdaLet (LambdaVal v) e) e.[LambdaVal v/].
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_lambda_call prog func v e :
  PureHeadExec prog (prog !! func = Some e) 1 (LambdaCall (LambdaVal (LambdaFunc func)) (LambdaVal v)) e.[LambdaVal v/].
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_lambda_unop prog op v w :
  PureHeadExec prog (lambda_unop_eval op v = Some w) 1 (LambdaUnop op (LambdaVal v)) (LambdaVal w).
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_lambda_binop_det prog op v1 v2 w :
  PureHeadExec prog (lambda_binop_eval op v1 v2 = Some w) 1 (LambdaBinopDet op (LambdaVal v1) (LambdaVal v2)) (LambdaVal w).
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_lambda_if_true prog e1 e2 :
  PureHeadExec prog True 1 (LambdaIf (LambdaVal (LambdaBool true)) e1 e2) e1.
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_lambda_if_false prog e1 e2 :
  PureHeadExec prog True 1 (LambdaIf (LambdaVal (LambdaBool false)) e1 e2) e2.
Proof.
  solve_pure_head_exec.
Qed.

#[global] Hint Extern 0 True => exact I
: typeclass_instances.
#[global] Hint Extern 0 (lambda_unop_eval _ _ = _) => reflexivity
: typeclass_instances.
#[global] Hint Extern 0 (lambda_binop_eval _ _ _ = _) => reflexivity
: typeclass_instances.
