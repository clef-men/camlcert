From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.lambda_lang Require Export
  language.

Fixpoint lambda_ectx_decompositions e :=
  let lambda_ectx_decompositions_with k e :=
    (λ '(K, e), ([k] ⋅ K, e)) <$> lambda_ectx_decompositions e
  in
  ([], e) ::
  match e with
  | LambdaVar _
  | LambdaVal _
  | LambdaConstr _ _ _
  | LambdaConstrDet _ _ _ =>
      []
  | LambdaLet e1 e2 =>
      lambda_ectx_decompositions_with (LambdaEctxiLet e2) e1
  | LambdaCall e1 e2 =>
      lambda_ectx_decompositions_with (LambdaEctxiCall1 e1) e2 ++
      match lambda_to_val e2 with
      | None => []
      | Some v2 =>
          lambda_ectx_decompositions_with (LambdaEctxiCall2 v2) e1
      end
  | LambdaUnop op e =>
      lambda_ectx_decompositions_with (LambdaEctxiUnop op) e
  | LambdaBinop op e1 e2 =>
      lambda_ectx_decompositions_with (LambdaEctxiBinop1 op e1) e2 ++
      match lambda_to_val e2 with
      | None => []
      | Some v2 =>
          lambda_ectx_decompositions_with (LambdaEctxiBinop2 op v2) e1
      end
  | LambdaIf e0 e1 e2 =>
      lambda_ectx_decompositions_with (LambdaEctxiIf e1 e2) e0
  | LambdaLoad e1 e2 =>
      lambda_ectx_decompositions_with (LambdaEctxiLoad1 e1) e2 ++
      match lambda_to_val e2 with
      | None => []
      | Some v2 =>
          lambda_ectx_decompositions_with (LambdaEctxiLoad2 v2) e1
      end
  | LambdaStore e1 e2 e3 =>
      lambda_ectx_decompositions_with (LambdaEctxiStore1 e1 e2) e3 ++
      match lambda_to_val e3 with
      | None => []
      | Some v3 =>
          lambda_ectx_decompositions_with (LambdaEctxiStore2 e1 v3) e2 ++
          match lambda_to_val e2 with
          | None => []
          | Some v2 =>
              lambda_ectx_decompositions_with (LambdaEctxiStore3 v2 v3) e1
          end
      end
  end.

Lemma lambda_ectx_decompositions_sound e K e' :
  (K, e') ∈ lambda_ectx_decompositions e →
  e = K @@ e'.
Proof.
  revert K e'. induction e; simpl; intros;
    repeat match goal with
    | _ =>
        progress decompose_elem_of_list
    | H : _ ∈ _ <$> _ |- _ =>
        apply elem_of_list_fmap in H as ([] & ? & ?); simplify
    | H : _ ∈ match lambda_to_val ?e with None => _ | Some _ => _ end |- _ =>
        let Heq := fresh "Heq" in
        destruct (lambda_to_val e) eqn:Heq; first apply of_to_val in Heq
    end;
    rewrite -?fill_op; naive_solver.
Qed.

Lemma lambda_ectx_decompositions_base e :
  (∅, e) ∈ lambda_ectx_decompositions e.
Proof.
  destruct e; econstructor.
Qed.

Lemma lambda_ectx_decompositions_complete K e :
  (K, e) ∈ lambda_ectx_decompositions (K @@ e).
Proof.
  revert K e.
  assert (∀ K e, (reverse K, e) ∈ lambda_ectx_decompositions ((reverse K) @@ e)).
  { intros. induction K as [| k K]; first apply lambda_ectx_decompositions_base.
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
Lemma lambda_ectx_decompositions_complete' e K e' :
  e = K @@ e' →
  (K, e') ∈ lambda_ectx_decompositions e.
Proof.
  intros ->. apply lambda_ectx_decompositions_complete.
Qed.

Lemma lambda_ectx_decompositions_spec e K e' :
  e = K @@ e' ↔
  (K, e') ∈ lambda_ectx_decompositions e.
Proof.
  split; eauto using lambda_ectx_decompositions_sound, lambda_ectx_decompositions_complete'.
Qed.
