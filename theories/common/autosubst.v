From Autosubst Require Export
  Autosubst.

From camlcert Require Export
  prelude.
From camlcert Require Import
  options.

Definition sapp {term} (tms : list term) ς :=
  foldr scons ς tms.

Notation "tms .+ ς" := (
  sapp tms ς
)(at level 60,
  right associativity
) : subst_scope.
Notation "ς .[ tms //]" := (
  subst (sapp tms ids) ς
)(at level 2,
  tms at level 200,
  left associativity,
  format "ς .[ tms //]"
) : subst_scope.

Section subst.
  Context `{!Ids term, !Rename term, !Subst term, !SubstLemmas term}.

  Implicit Types x : var.
  Implicit Types ς : var → term.

  Lemma upn_lt x n ς :
    x < n →
    upn n ς x = ids x.
  Proof.
    move: x. induction n; intros x Hx; first lia.
    rewrite upnSE. destruct x; first done.
    rewrite /= IHn; [lia | autosubst].
  Qed.
  Lemma upn_ge x n ς :
    n ≤ x →
    upn n ς x = (ς (x - n)).[ren (+n)].
  Proof.
    move: x. induction n; intros x Hx.
    - rewrite upn0 Nat.sub_0_r. autosubst.
    - rewrite upnSE. destruct x; first lia.
      asimpl. rewrite IHn; first lia. autosubst.
  Qed.
End subst.
