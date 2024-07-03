From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  language.
From camlcert Require Import
  options.

Fixpoint data_ectx_decompositions e :=
  let data_ectx_decompositions_with k e :=
    (λ '(K, e), ([k] ⋅ K, e)) <$> data_ectx_decompositions e
  in
  ([], e) ::
  match e with
  | DataVar _
  | DataVal _
  | DataBinop _ _ _
  | DataBinopDet _ _ _
  | DataBlock _ _ _
  | DataBlockDet _ _ _ =>
      []
  | DataLet e1 e2 =>
      data_ectx_decompositions_with (DataEctxiLet e2) e1
  | DataCall e1 e2 =>
      data_ectx_decompositions_with (DataEctxiCall1 e1) e2 ++
      match data_to_val e2 with
      | None => []
      | Some v2 =>
          data_ectx_decompositions_with (DataEctxiCall2 v2) e1
      end
  | DataUnop op e =>
      data_ectx_decompositions_with (DataEctxiUnop op) e
  | DataIf e0 e1 e2 =>
      data_ectx_decompositions_with (DataEctxiIf e1 e2) e0
  | DataLoad e1 e2 =>
      data_ectx_decompositions_with (DataEctxiLoad1 e1) e2 ++
      match data_to_val e2 with
      | None => []
      | Some v2 =>
          data_ectx_decompositions_with (DataEctxiLoad2 v2) e1
      end
  | DataStore e1 e2 e3 =>
      data_ectx_decompositions_with (DataEctxiStore1 e1 e2) e3 ++
      match data_to_val e3 with
      | None => []
      | Some v3 =>
          data_ectx_decompositions_with (DataEctxiStore2 e1 v3) e2 ++
          match data_to_val e2 with
          | None => []
          | Some v2 =>
              data_ectx_decompositions_with (DataEctxiStore3 v2 v3) e1
          end
      end
  end.

Lemma data_ectx_decompositions_sound e K e' :
  (K, e') ∈ data_ectx_decompositions e →
  e = K @@ e'.
Proof.
  revert K e'. induction e; simpl; intros;
    repeat match goal with
    | _ =>
        progress decompose_elem_of_list
    | H : _ ∈ _ <$> _ |- _ =>
        apply elem_of_list_fmap in H as ([] & ? & ?); simplify
    | H : _ ∈ match data_to_val ?e with None => _ | Some _ => _ end |- _ =>
        let Heq := fresh "Heq" in
        destruct (data_to_val e) eqn:Heq; first apply of_to_val in Heq
    end;
    rewrite -?fill_op; naive_solver.
Qed.

Lemma data_ectx_decompositions_base e :
  (∅, e) ∈ data_ectx_decompositions e.
Proof.
  destruct e; econstructor.
Qed.

Lemma data_ectx_decompositions_complete K e :
  (K, e) ∈ data_ectx_decompositions (K @@ e).
Proof.
  revert K e.
  assert (∀ K e, (reverse K, e) ∈ data_ectx_decompositions ((reverse K) @@ e)).
  { intros. induction K as [| k K]; first apply data_ectx_decompositions_base.
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
Lemma data_ectx_decompositions_complete' e K e' :
  e = K @@ e' →
  (K, e') ∈ data_ectx_decompositions e.
Proof.
  intros ->. apply data_ectx_decompositions_complete.
Qed.

Lemma data_ectx_decompositions_spec e K e' :
  e = K @@ e' ↔
  (K, e') ∈ data_ectx_decompositions e.
Proof.
  split; eauto using data_ectx_decompositions_sound, data_ectx_decompositions_complete'.
Qed.
