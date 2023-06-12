From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.language Require Export
  language.

Fixpoint ectx_decompositions e :=
  let ectx_decompositions_with k e :=
    (λ '(K, e), ([k] ⋅ K, e)) <$> ectx_decompositions e
  in
  ([], e) ::
  match e with
  | Var _
  | Val _
  | Constr _ _ _
  | ConstrDet _ _ _ =>
      []
  | Let e1 e2 =>
      ectx_decompositions_with (EctxiLet e2) e1
  | Call e1 e2 =>
      ectx_decompositions_with (EctxiCall1 e1) e2 ++
      match to_val e2 with
      | None => []
      | Some v2 =>
          ectx_decompositions_with (EctxiCall2 v2) e1
      end
  | Unop op e =>
      ectx_decompositions_with (EctxiUnop op) e
  | Binop op e1 e2 =>
      ectx_decompositions_with (EctxiBinop1 op e1) e2 ++
      match to_val e2 with
      | None => []
      | Some v2 =>
          ectx_decompositions_with (EctxiBinop2 op v2) e1
      end
  | If e0 e1 e2 =>
      ectx_decompositions_with (EctxiIf e1 e2) e0
  | Load e =>
      ectx_decompositions_with EctxiLoad e
  | Store e1 e2 =>
      ectx_decompositions_with (EctxiStore1 e1) e2 ++
      match to_val e2 with
      | None => []
      | Some v2 =>
          ectx_decompositions_with (EctxiStore2 v2) e1
      end
  end.

Lemma ectx_decompositions_sound e K e' :
  (K, e') ∈ ectx_decompositions e →
  e = K @@ e'.
Proof.
  revert K e'. induction e; simpl; intros;
    repeat match goal with
    | _ =>
        progress decompose_elem_of_list
    | H : _ ∈ _ <$> _ |- _ =>
        apply elem_of_list_fmap in H as ([] & ? & ?); simplify
    | H : _ ∈ match to_val ?e with None => _ | Some _ => _ end |- _ =>
        let Heq := fresh "Heq" in
        destruct (to_val e) eqn:Heq; first apply of_to_val in Heq
    end;
    rewrite -?fill_op; naive_solver.
Qed.

Lemma ectx_decompositions_base e :
  (∅, e) ∈ ectx_decompositions e.
Proof.
  destruct e; econstructor.
Qed.

Lemma ectx_decompositions_complete K e :
  (K, e) ∈ ectx_decompositions (K @@ e).
Proof.
  revert K e.
  assert (∀ K e, (reverse K, e) ∈ ectx_decompositions ((reverse K) @@ e)).
  { intros. induction K as [| k K]; first apply ectx_decompositions_base.
    rewrite reverse_cons -fill_op /=. destruct k; simpl;
    repeat match goal with
    | |- _ ∈ _ :: _ =>
        econstructor
    | |- _ ∈ _ <$> _ =>
        apply elem_of_list_fmap; by exists (reverse K, e)
    | |- _ ∈ _ ++ _ =>
        apply elem_of_app; left
    | _ =>
        simpl
    end.
  }
  intros. by rewrite -(reverse_involutive K).
Qed.
Lemma ectx_decompositions_complete' e K e' :
  e = K @@ e' →
  (K, e') ∈ ectx_decompositions e.
Proof.
  intros ->. apply ectx_decompositions_complete.
Qed.

Lemma ectx_decompositions_spec e K e' :
  e = K @@ e' ↔
  (K, e') ∈ ectx_decompositions e.
Proof.
  split; eauto using ectx_decompositions_sound, ectx_decompositions_complete'.
Qed.
