From stdpp Require Export
  gmap.

From camlcert Require Import
  prelude.
From camlcert Require Import
  options.

Section map_fold.
  #[local] Lemma gmap_dep_fold_ind {A B} f {P} (Q : B → gmap_dep A P → Prop) b j mt :
    Q b GEmpty →
    ( ∀ i p x mt' r,
      gmap.gmap_dep_lookup i mt = Some x →
      gmap.gmap_dep_lookup i mt' = None →
      Q r mt' →
      Q (f (Pos.reverse_go i j) x r) (gmap.gmap_dep_partial_alter (λ _, Some x) i p mt')
    ) →
    Q (gmap.gmap_dep_fold f j b mt) mt.
  Proof.
    intros Hemp Hinsert. revert Q b j Hemp Hinsert.
    induction mt as [|P ml mx mr ? IHl IHr] using gmap.gmap_dep_ind;
      intros Q b j Hemp Hinsert; [done|].
    rewrite gmap.gmap_dep_fold_GNode; first done.
    apply (IHr (λ y mt, Q y (gmap.GNode ml mx mt))).
    { apply (IHl (λ y mt, Q y (gmap.GNode mt mx GEmpty))).
      { destruct mx as [[p x]|]; [|done].
        replace (gmap.GNode GEmpty (Some (p,x)) GEmpty) with
          (gmap.gmap_dep_partial_alter (λ _, Some x) 1 p GEmpty) by done.
        apply Hinsert; try done.
        rewrite gmap.gmap_dep_lookup_GNode //.
      }
      intros i p x mt r ??.
      replace (gmap.GNode (gmap.gmap_dep_partial_alter (λ _, Some x) i p mt) mx GEmpty)
        with (gmap.gmap_dep_partial_alter (λ _, Some x) (i~0)%positive p (gmap.GNode mt mx GEmpty))
        by (by destruct mt, mx as [[] |]).
      apply Hinsert; rewrite ?gmap.gmap_dep_lookup_GNode //.
    }
    intros i p x mt r ??.
    replace (gmap.GNode ml mx (gmap.gmap_dep_partial_alter (λ _, Some x) i p mt))
      with (gmap.gmap_dep_partial_alter (λ _, Some x) (i~1)%positive p (gmap.GNode ml mx mt))
      by (by destruct ml, mx as [[]|], mt).
    apply Hinsert; rewrite ?gmap.gmap_dep_lookup_GNode //.
  Qed.

  Context `{Countable K} {V : Type}.

  Lemma map_fold_ind {A} (P : A → gmap K V → Prop) f acc m :
    P acc ∅ →
    ( ∀ k v m' acc,
      m !! k = Some v →
      m' !! k = None →
      P acc m' →
      P (f k v acc) (<[k := v]> m')
    ) →
    P (map_fold f acc m) m.
  Proof.
    intros Hempty Hinsert.
    destruct m as [mt].
    apply (gmap_dep_fold_ind _ (λ r mt, P r (GMap mt))); first done.
    intros i [Hk] x mt' r ? ?; simpl. destruct (fmap_Some_1 _ _ _ Hk) as (k & -> & ->).
    assert (GMapKey Hk = gmap_key_encode k) as -> by (apply proof_irrel).
    apply (Hinsert _ _ (GMap mt')); done.
  Qed.
  Lemma map_fold_strong_ind {A} (P : A → gmap K V → Prop) f acc m :
    P acc ∅ →
    ( ∀ k v m' acc,
      m' ⊆ m →
      m !! k = Some v →
      m' !! k = None →
      P acc m' →
      P (f k v acc) (<[k := v]> m')
    ) →
    P (map_fold f acc m) m.
  Proof.
    intros Hempty Hinsert.
    pose (Q acc m' := m' ⊆ m ∧ P acc m').
    apply (map_fold_ind Q).
    - split; last done. apply map_empty_subseteq.
    - intros k v m' acc' Hlookup Hlookup' (Hm' & IH).
      split; last naive_solver.
      apply insert_subseteq_l; done.
  Qed.
End map_fold.

Section restrict.
  Context `{Countable K} {V : Type}.

  Implicit Types m : gmap K V.

  Definition restrict (s : gset K) m :=
    filter (λ p, p.1 ∈ s) m.

  Lemma restrict_empty m :
    restrict ∅ m = ∅.
  Proof.
    apply map_filter_empty_iff. done.
  Qed.

  Lemma restrict_singleton_None k m :
    m !! k = None →
    restrict {[k]} m = ∅.
  Proof.
    intros Hlookup.
    apply map_filter_empty_iff, map_Forall_lookup => k' v Hlookup' Hk'.
    rewrite elem_of_singleton /= in Hk'. congruence.
  Qed.
  Lemma restrict_singleton_Some {k m} v :
    m !! k = Some v →
    restrict {[k]} m = {[k := v]}.
  Proof.
    intros Hlookup.
    assert ({[k := v]} = restrict {[k]} {[k := v]}) as ->.
    { symmetry. apply map_filter_singleton_True. set_solver. }
    apply map_filter_strong_ext_1 => k' v' /=. split.
    - intros (->%elem_of_singleton & _Hlookup). simplify.
      rewrite lookup_insert. set_solver.
    - intros (->%elem_of_singleton & (_ & ->)%lookup_singleton_Some).
      set_solver.
  Qed.

  Lemma restrict_subseteq s m :
    dom m ⊆ s →
    restrict s m = m.
  Proof.
    intros Hdom.
    apply map_filter_id. intros ? ? ?%elem_of_dom_2. set_solver.
  Qed.

  Lemma restrict_union s1 s2 m :
    restrict (s1 ∪ s2) m = restrict s1 m ∪ restrict s2 m.
  Proof.
    rewrite /restrict (map_filter_strong_ext_1 _ (λ p, p.1 ∈ s1 ∨ p.1 ∈ s2) m m); first set_solver.
    apply map_filter_or.
  Qed.

  Lemma restrict_disjoint s1 m1 s2 m2 :
    s1 ## s2 →
    restrict s1 m1 ##ₘ restrict s2 m2.
  Proof.
    intros Hdisj.
    apply map_disjoint_spec. intros k v1 v2 ?%map_filter_lookup_Some_1_2 ?%map_filter_lookup_Some_1_2.
    set_solver.
  Qed.
End restrict.
