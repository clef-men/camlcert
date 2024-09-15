From stdpp Require Export
  strings
  gmap.

From camlcert Require Import
  prelude.
From camlcert Require Import
  options.

Implicit Types i : nat.
Implicit Types n : Z.

Definition flam_symbol :=
  string.
Implicit Types symb : flam_symbol.

Definition flam_func :=
  string.
Implicit Types func : flam_func.
Implicit Types funcs : list flam_func.

Definition flam_var :=
  nat.
Implicit Types x f : flam_var.

Definition flam_cont :=
  nat.
Implicit Types k : flam_cont.

Inductive flam_cont' :=
  | FlamRet
  | FlamExn
  | FlamCont (k : flam_cont).

#[global] Instance flam_cont'_inhabited : Inhabited flam_cont' :=
  populate FlamRet.

Inductive flam_simple :=
  | FlamSymbol symb
  | FlamInt n
  | FlamVar x.
Implicit Types simple : flam_simple.
Implicit Types simples : list flam_simple.

Definition FlamBool b :=
  FlamInt (Z.b2z b).

Inductive flam_mut :=
  | FlamMutable
  | FlamImmutable.
Implicit Types mut : flam_mut.

Inductive flam_rec :=
  | FlamRecursive
  | FlamNonrecursive.
Implicit Types rec : flam_rec.

Definition flam_tag :=
  nat.
Implicit Types tag : flam_tag.

Inductive flam_op1 :=
  | FlamNeg
  | FlamNot.

Inductive flam_prim1 :=
  | FlamIsInt
  | FlamTag
  | FlamSize
  | FlamOp1 (op : flam_op1)
  | FlamClosVal i1 i2
  | FlamClosFunc i1 i2.

Inductive flam_op2 :=
  | FlamPlus
  | FlamMinus
  | FlamMult
  | FlamQuot
  | FlamRem
  | FlamLe
  | FlamLt
  | FlamGe
  | FlamGt.

Inductive flam_prim2 :=
  | FlamOp2 (op : flam_op2)
  | FlamEqual
  | FlamLoad.

Inductive flam_prim3 :=
  | FlamStore.

Inductive flam_prim :=
  | FlamBlock mut tag.

Inductive flam_named :=
  | FlamSimple simple
  | FlamPrim1 (prim : flam_prim1) simple
  | FlamPrim2 (prim : flam_prim2) simple1 simple2
  | FlamPrim3 (prim : flam_prim3) simple1 simple2 simple3
  | FlamPrim (prim : flam_prim) simples.
Implicit Types named : flam_named.

Definition flam_arity :=
  nat.
Implicit Types arity : flam_arity.

Inductive flam_call_kind :=
  | FlamDirect func
  | FlamIndirect.
Implicit Types kind : flam_call_kind.

Record flam_arm := {
  flam_arm_cont : flam_cont' ;
  flam_arm_args : list flam_simple ;
}.
Implicit Types arm : flam_arm.
Implicit Types arms : gmap flam_tag flam_arm.

Inductive flam_term :=
  | FlamLet named (tm : flam_term)
  | FlamLetClos funcs simples (tm : flam_term)
  | FlamLetCont rec arity (tm1 tm2 : flam_term)
  | FlamApply kind f simples k1 k2
  | FlamApplyCont (k : flam_cont') simples
  | FlamSwitch simple arms.
Implicit Types tm : flam_term.

#[global] Instance flam_term_inhabited : Inhabited flam_term :=
  populate (FlamApplyCont inhabitant inhabitant).
