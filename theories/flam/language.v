From camlcert Require Import
  prelude.
From camlcert.iris.program_logic Require Export
  language.
From camlcert.flam Require Export
  semantics.
From camlcert Require Import
  options.

Implicit Types simple : flam_simple.
Implicit Types env : flam_env.

Definition flam_expr : Set :=
  flam_env * flam_term.
Implicit Types e : flam_expr.

Canonical flam_expr_O :=
  leibnizO flam_expr.

Canonical flam_state_O :=
  leibnizO flam_state.

Definition flam_prim_step prog e σ e' σ' :=
  flam_step prog e.1 e.2 σ e'.1 e'.2 σ'.

Inductive flam_res :=
  | FlamResRet env simple
  | FlamResExn env simple.

Canonical flam_res_O :=
  leibnizO flam_res.

Definition flam_expr_of_res res : flam_expr :=
  match res with
  | FlamResRet env simple =>
      (env, FlamApplyCont FlamRet [simple])
  | FlamResExn env simple =>
      (env, FlamApplyCont FlamExn [simple])
  end.
#[global] Arguments flam_expr_of_res !_ : assert.

Definition flam_expr_to_res expr :=
  match expr.2 with
  | FlamApplyCont FlamRet [simple] =>
      Some $ FlamResRet expr.1 simple
  | FlamApplyCont FlamExn [simple] =>
      Some $ FlamResExn expr.1 simple
  | _ =>
      None
  end.

Lemma flam_lang_mixin :
  LanguageMixin
    flam_expr_of_res
    flam_expr_to_res
    flam_prim_step.
Proof.
  split.
  - intros ? []; naive_solver.
  - intros (env, [| | | | [] [| ? []] |]) ?; cbn; naive_solver.
  - intros prog (env1, tm1) σ1 (env2, tm2) σ2 Hstep.
    invert Hstep; done.
Qed.
