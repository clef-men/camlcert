From stdpp Require Import
  countable.

From camlcert Require Import
  prelude.

Inductive three :=
  | Zero
  | One
  | Two.

#[global] Instance three_eq_dec : EqDecision three :=
  ltac:(solve_decision).
#[global] Instance three_countable :
  Countable three.
Proof.
  pose encode idx :=
    match idx with
    | Zero => 0
    | One => 1
    | Two => 2
    end.
  pose decode idx :=
    match idx with
    | 0 => Zero
    | 1 => One
    | _ => Two
    end.
  apply (inj_countable' encode decode). intros []; done.
Qed.
