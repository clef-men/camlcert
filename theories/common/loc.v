From stdpp Require Import
  countable
  numbers
  gmap.

From simuliris Require Import
  prelude.

#[local] Open Scope Z_scope.

Record loc := {
  loc_car : Z ;
}.
Add Printing Constructor loc.

Lemma loc_eq_spec l1 l2 :
  l1 = l2 ↔
  loc_car l1 = loc_car l2.
Proof.
  destruct l1, l2; naive_solver.
Qed.

#[global] Instance loc_inhabited : Inhabited loc :=
  populate {| loc_car := 0 |}.
#[global] Instance loc_eq_dec :
  EqDecision loc.
Proof.
  solve_decision.
Defined.
#[global] Instance loc_countable :
  Countable loc.
Proof.
  by apply (inj_countable' loc_car Build_loc); intros [].
Defined.
#[global] Program Instance loc_infinite : Infinite loc :=
  inj_infinite (λ p, {| loc_car := p |}) (λ l, Some (loc_car l)) _.
Next Obligation.
  done.
Qed.

Definition loc_add l off :=
  {| loc_car := loc_car l + off |}.
Definition loc_le l1 l2 :=
  loc_car l1 ≤ loc_car l2.
Definition loc_lt l1 l2 :=
  loc_car l1 < loc_car l2.

Notation "l +ₗ off" := (
  loc_add l off
)(at level 50,
  left associativity
) : stdpp_scope.
Notation "l1 ≤ₗ l2" := (
  loc_le l1 l2
)(at level 70
) : stdpp_scope.
Notation "l1 <ₗ l2" := (
  loc_lt l1 l2
)(at level 70
) : stdpp_scope.

#[global] Instance loc_add_inj l :
  Inj (=) (=) (loc_add l).
Proof.
  intros x1 x2. rewrite loc_eq_spec /=. lia.
Qed.

Lemma loc_add_assoc l i j :
  l +ₗ i +ₗ j = l +ₗ (i + j).
Proof.
  rewrite loc_eq_spec /=. lia.
Qed.
Lemma loc_add_0 l :
  l +ₗ 0 = l.
Proof.
  rewrite loc_eq_spec /=; lia.
Qed.

#[global] Instance loc_le_dec l1 l2 :
  Decision (l1 ≤ₗ l2).
Proof.
  rewrite /loc_le. apply _.
Qed.
#[global] Instance loc_le_po :
  PartialOrder loc_le.
Proof.
  rewrite /loc_le. split; [split|].
  - by intros ?.
  - intros [x] [y] [z]; lia.
  - intros [x] [y] ??; f_equal/=; lia.
Qed.
#[global] Instance loc_le_total :
  Total loc_le.
Proof.
  rewrite /Total /loc_le. lia.
Qed.

Lemma loc_add_le_mono l1 l2 i1 i2 :
  l1 ≤ₗ l2 →
  i1 ≤ i2 →
  l1 +ₗ i1 ≤ₗ l2 +ₗ i2.
Proof.
  apply Z.add_le_mono.
Qed.

#[global] Instance loc_lt_dec l1 l2 :
  Decision (l1 <ₗ l2).
Proof.
  rewrite /loc_lt. apply _.
Qed.

Lemma loc_le_ngt l1 l2 :
  l1 ≤ₗ l2 ↔
  ¬l2 <ₗ l1.
Proof.
  apply Z.le_ngt.
Qed.
Lemma loc_le_lteq l1 l2 :
  l1 ≤ₗ l2 ↔
  l1 <ₗ l2 ∨ l1 = l2.
Proof.
  rewrite loc_eq_spec. apply Z.le_lteq.
Qed.

Definition loc_fresh (ls : gset loc) := {|
  loc_car := set_fold (λ k r, (1 + loc_car k) `max` r) 1 ls
|}.

Lemma loc_fresh_fresh ls i :
  0 ≤ i →
  loc_fresh ls +ₗ i ∉ ls.
Proof.
  intros Hi. cut (∀ l, l ∈ ls → loc_car l < loc_car (loc_fresh ls) + i).
  { intros help Hf%help. simpl in *. lia. }
  apply (set_fold_ind_L (λ r ls, ∀ l, l ∈ ls → (loc_car l < r + i)));
    set_solver by eauto with lia.
Qed.

#[global] Opaque loc_fresh.
