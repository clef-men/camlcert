From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.language Require Export
  language.
From simuliris.language Require Import
  ectx_decompositions
  well_formed.

Create HintDb language.

#[global] Hint Extern 0 (
  reducible _ _ _
) => (
  eapply head_reducible_reducible
) : language.
#[global] Hint Extern 0 (
  head_reducible _ _ _
) => (
  eexists _, _; simpl
) : language.
#[global] Hint Extern 1 (
  head_step _ _ _ _ _
) => (
  econstructor
) : language.
#[global] Hint Extern 1 (
  ectx_language.head_step _ _ _ _ _
) => (
  econstructor
) : language.
#[global] Hint Extern 0 (
  head_step _ (ConstrDet _ _ _) _ _ _
) => (
  eapply head_step_constr_det'
) : language.
#[global] Hint Extern 0 (
  ectx_language.head_step _ (ConstrDet _ _ _) _ _ _
) => (
  eapply head_step_constr_det'
) : language.
#[global] Hint Extern 0 (
  pure_step _ _ _
) => (
  eapply pure_exec_pure_step; [apply _ |]
) : language.
#[global] Hint Extern 0 (
  pure_head_step _ _ _
) => (
  eapply pure_head_exec_pure_head_step; [apply _ |]
) : language.
#[global] Hint Extern 0 (
  strongly_stuck _ _
) => (
  eapply @is_strongly_stuck; [apply _]
) : language.
#[global] Hint Extern 0 (
  strongly_head_stuck _ _
) => (
  eapply @is_strongly_head_stuck; [apply _]
) : language.

#[global] Hint Extern 1 (
  sub_redexes_are_values _
) => (
  let Hdecomps := fresh "Hdecomps" in
  intros ?* Hdecomps%ectx_decompositions_spec; invert Hdecomps; first done;
    decompose_elem_of_list; simplify
) : language.

Ltac invert_well_formed :=
  repeat_on_hyps ltac:(fun H =>
    match type of H with
    | val_well_formed _ ?v =>
        solve [by destruct v]
    | expr_well_formed _ _ _ =>
        invert H; simplify
    | expr_well_formed' _ _ =>
        let lvl := fresh "lvl" in
        destruct H as (lvl & H)
    end
  );
  try done.
#[global] Hint Extern 0 => (
  solve [invert_well_formed]
) : language.
#[global] Hint Extern 1 (
  expr_well_formed _ _ _
) => (
  progress invert_well_formed
) : language.
#[global] Hint Extern 1 (
  expr_well_formed' _ _
) => (
  invert_well_formed; eexists
) : language.

Ltac invert_head_step :=
  repeat_on_hyps ltac:(fun H =>
    let ty := type of H in
    let ty := eval simpl in ty in
    match ty with head_step _ ?e _ _ _ =>
      try (is_var e; fail 1);
      invert H
    end
  ).

#[local] Ltac solve_strongly_head_stuck :=
  intros ?; split;
  [ intros ?** ?** ?; invert_head_step; done
  | auto with language
  ].
#[global] Instance strongly_head_stuck_call prog v1 v2 :
  (if v1 is Func _ then False else True) →
  IsStronglyHeadStuck prog (Call (Val v1) (Val v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_unop prog op v :
  unop_eval op v = None →
  IsStronglyHeadStuck prog (Unop op (Val v)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_binop prog op v1 v2 :
  binop_eval op v1 v2 = None →
  IsStronglyHeadStuck prog (Binop op (Val v1) (Val v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_if prog v0 e1 e2 :
  (if v0 is Bool _ then False else True) →
  IsStronglyHeadStuck prog (If (Val v0) e1 e2).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_load_1 prog v1 v2 :
  (if v1 is Loc _ then False else True) →
  IsStronglyHeadStuck prog (Load (Val v1) (Val v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_load_2 prog v1 v2 :
  (if v2 is Index _ then False else True) →
  IsStronglyHeadStuck prog (Load (Val v1) (Val v2)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_store_1 prog v1 v2 v3 :
  (if v1 is Loc _ then False else True) →
  IsStronglyHeadStuck prog (Store (Val v1) (Val v2) (Val v3)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Instance strongly_head_stuck_store_2 prog v1 v2 v3 :
  (if v2 is Index _ then False else True) →
  IsStronglyHeadStuck prog (Store (Val v1) (Val v2) (Val v3)).
Proof.
  solve_strongly_head_stuck.
Qed.
#[global] Hint Extern 0 True => exact I
: typeclass_instances.
#[global] Hint Extern 0 (unop_eval _ _ = _) => reflexivity
: typeclass_instances.
#[global] Hint Extern 0 (binop_eval _ _ _ = _) => reflexivity
: typeclass_instances.

#[local] Ltac solve_pure_head_exec :=
  intros ?; apply nsteps_once; constructor;
  [ auto with language
  | intros; invert_head_step; auto
  ].
#[global] Instance pure_exec_let prog v e :
  PureHeadExec prog True 1 (Let (Val v) e) e.[Val v/].
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_call prog func v e :
  PureHeadExec prog (prog !! func = Some e) 1 (Call (Val (Func func)) (Val v)) e.[Val v/].
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_unop prog op v w :
  PureHeadExec prog (unop_eval op v = Some w) 1 (Unop op (Val v)) (Val w).
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_binop prog op v1 v2 w :
  PureHeadExec prog (binop_eval op v1 v2 = Some w) 1 (Binop op (Val v1) (Val v2)) (Val w).
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_if_true prog e1 e2 :
  PureHeadExec prog True 1 (If (Val (Bool true)) e1 e2) e1.
Proof.
  solve_pure_head_exec.
Qed.
#[global] Instance pure_exec_if_false prog e1 e2 :
  PureHeadExec prog True 1 (If (Val (Bool false)) e1 e2) e2.
Proof.
  solve_pure_head_exec.
Qed.
