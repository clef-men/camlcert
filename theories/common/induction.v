From simuliris Require Import
  prelude.

Section nat_strong_ind.
  Variable P : nat → Prop.
  Variable H : ∀ n, (∀ m, m < n → P m) → P n.

  Lemma nat_strong_ind n :
    P n.
  Proof.
    cut (∀ m, m ≤ n → P m); first naive_solver lia.
    induction n; naive_solver lia.
  Qed.
End nat_strong_ind.
