From camlcert Require Import
  prelude.
From camlcert.common Require Import
  gmap.
From camlcert.aps_plus_1 Require Export
  metatheory.
From camlcert Require Import
  options.

Implicit Types prog progₛ progₜ : data_program.
Implicit Types ξ : aps_plus_mapping.

Definition aps_plus_annotation :=
  "aps_plus".

Inductive aps_plus_hint :=
  | ApsPlusYes
  | ApsPlusNo
  | ApsPlusMaybe.
Implicit Types hint : aps_plus_hint.

#[global] Instance aps_plus_hint_join : Join aps_plus_hint :=
  λ hint1 hint2,
    match hint1 with
    | ApsPlusYes =>
        ApsPlusYes
    | ApsPlusNo =>
        hint2
    | ApsPlusMaybe =>
        match hint2 with
        | ApsPlusNo =>
            ApsPlusMaybe
        | _ =>
            hint2
        end
    end.

Definition aps_plus_hint_le hint1 hint2 :=
  match hint2 with
  | ApsPlusYes =>
      true
  | ApsPlusNo =>
      if hint1 is ApsPlusNo then true else false
  | ApsPlusMaybe =>
      if hint1 is ApsPlusYes then false else true
  end.
#[global] Instance aps_plus_hint_sqsubseteq : SqSubsetEq aps_plus_hint :=
  λ hint1 hint2,
    aps_plus_hint_le hint1 hint2 = true.
#[global] Instance aps_plus_hint_sqsubseteq_dec hint1 hint2 : Decision (hint1 ⊑ hint2) :=
  decide (aps_plus_hint_le hint1 hint2 = true).

Record aps_plus_result := {
  aps_plus_result_hint : aps_plus_hint ;
  aps_plus_result_dir : (var → data_expr) → data_expr ;
  aps_plus_result_aps : (var → data_expr) → data_expr ;
}.

Fixpoint aps_plus_compile_expr ξ acc e :=
  let acc' := DataVar acc in
  match e with
  | DataVal _ =>
      let dir := e in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir ς :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' dir
      |}
  | DataVar x =>
      let dir ς := ς x in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' (dir ς) ;
      |}
  | DataLet e1 e2 =>
      let res1 := aps_plus_compile_expr ξ acc e1 in
      let res2 := aps_plus_compile_expr ξ (S acc) e2 in
      {|aps_plus_result_hint :=
          res2.(aps_plus_result_hint) ;
        aps_plus_result_dir ς :=
          DataLet (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_dir) (up ς)) ;
        aps_plus_result_aps ς :=
          DataLet (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_aps) (up ς)) ;
      |}
  | DataCall (DataVal (DataFunc func annot)) e =>
      let res := aps_plus_compile_expr ξ acc e in
      let dir ς := DataCall (DataVal $ DataFunc func annot) (res.(aps_plus_result_dir) ς) in
      match ξ !! func with
      | None =>
          {|aps_plus_result_hint :=
              ApsPlusNo ;
            aps_plus_result_dir :=
              dir ;
            aps_plus_result_aps ς :=
              DataBinop DataPlus acc' (dir ς) ;
          |}
      | Some func_aps =>
          {|aps_plus_result_hint :=
              if decide (aps_plus_annotation ∈ annot) then ApsPlusYes else ApsPlusMaybe ;
            aps_plus_result_dir :=
              dir ;
            aps_plus_result_aps ς :=
              DataLet (res.(aps_plus_result_dir) ς) $
              DataCall (DataVal $ DataFunc func_aps annot) (DataBlock data_tag_pair (DataVar $ S acc) (DataVar 0)) ;
          |}
      end
  | DataCall e1 e2 =>
      let res1 := aps_plus_compile_expr ξ acc e1 in
      let res2 := aps_plus_compile_expr ξ acc e2 in
      let dir ς := DataCall (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_dir) ς) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' (dir ς) ;
      |}
  | DataUnop op e =>
      let res := aps_plus_compile_expr ξ acc e in
      let dir ς := DataUnop op (res.(aps_plus_result_dir) ς) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' (dir ς) ;
      |}
  | DataBinop DataPlus (DataVal (DataInt n)) e =>
      let res := aps_plus_compile_expr ξ 0 e in
      if decide (ApsPlusMaybe ⊑ res.(aps_plus_result_hint)) then
        {|aps_plus_result_hint :=
            res.(aps_plus_result_hint) ;
          aps_plus_result_dir ς :=
            DataLet (DataVal $ DataInt n) $
            res.(aps_plus_result_aps) (ς >> ren (+1))  ;
          aps_plus_result_aps ς :=
            DataLet (DataBinop DataPlus acc' (DataVal $ DataInt n)) $
            res.(aps_plus_result_aps) (ς >> ren (+1)) ;
        |}
      else
        let dir ς := DataBinop DataPlus (DataVal (DataInt n)) (res.(aps_plus_result_dir) ς) in
        {|aps_plus_result_hint :=
            ApsPlusNo ;
          aps_plus_result_dir :=
            dir ;
          aps_plus_result_aps ς :=
            DataBinop DataPlus acc' (dir ς) ;
        |}
  (* | DataBinop DataPlus e (DataVal (DataInt n)) => *)
  (*     let res := aps_plus_compile_expr ξ 0 e in *)
  (*     if decide (ApsPlusMaybe ⊑ res.(aps_plus_result_hint)) then *)
  (*       {|aps_plus_result_hint := *)
  (*           res.(aps_plus_result_hint) ; *)
  (*         aps_plus_result_dir ς := *)
  (*           DataLet (DataVal $ DataInt n) $ *)
  (*           res.(aps_plus_result_aps) (ς >> ren (+1)) ; *)
  (*         aps_plus_result_aps ς := *)
  (*           DataLet (DataBinop DataPlus acc' (DataVal $ DataInt n)) $ *)
  (*           res.(aps_plus_result_aps) (ς >> ren (+1)) ; *)
  (*       |} *)
  (*     else *)
  (*       let dir ς := DataBinop DataPlus (res.(aps_plus_result_dir) ς) (DataVal (DataInt n)) in *)
  (*       {|aps_plus_result_hint := *)
  (*           ApsPlusNo ; *)
  (*         aps_plus_result_dir := *)
  (*           dir ; *)
  (*         aps_plus_result_aps ς := *)
  (*           DataBinop DataPlus acc' (dir ς) ; *)
  (*       |} *)
  | DataBinop op e1 e2 =>
      let res1 := aps_plus_compile_expr ξ acc e1 in
      let res2 := aps_plus_compile_expr ξ acc e2 in
      let dir ς := DataBinop op (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_dir) ς) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' (dir ς) ;
      |}
  | DataBinopDet op e1 e2 =>
      let res1 := aps_plus_compile_expr ξ acc e1 in
      let res2 := aps_plus_compile_expr ξ acc e2 in
      let dir ς := DataBinopDet op (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_dir) ς) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' (dir ς) ;
      |}
  | DataIf e0 e1 e2 =>
      let res0 := aps_plus_compile_expr ξ acc e0 in
      let res1 := aps_plus_compile_expr ξ acc e1 in
      let res2 := aps_plus_compile_expr ξ acc e2 in
      {|aps_plus_result_hint :=
          res1.(aps_plus_result_hint) ⊔ res2.(aps_plus_result_hint) ;
        aps_plus_result_dir ς :=
          DataIf (res0.(aps_plus_result_dir) ς) (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_dir) ς) ;
        aps_plus_result_aps ς :=
          DataIf (res0.(aps_plus_result_dir) ς) (res1.(aps_plus_result_aps) ς) (res2.(aps_plus_result_aps) ς) ;
      |}
  | DataBlock tag e1 e2 =>
      let res1 := aps_plus_compile_expr ξ acc e1 in
      let res2 := aps_plus_compile_expr ξ acc e2 in
      let dir ς := DataBlock tag (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_dir) ς) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' (dir ς) ;
      |}
  | DataBlockDet tag e1 e2 =>
      let res1 := aps_plus_compile_expr ξ acc e1 in
      let res2 := aps_plus_compile_expr ξ acc e2 in
      let dir ς := DataBlockDet tag (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_dir) ς) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' (dir ς) ;
      |}
  | DataLoad e1 e2 =>
      let res1 := aps_plus_compile_expr ξ acc e1 in
      let res2 := aps_plus_compile_expr ξ acc e2 in
      let dir ς := DataLoad (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_dir) ς) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' (dir ς) ;
      |}
  | DataStore e1 e2 e3 =>
      let res1 := aps_plus_compile_expr ξ acc e1 in
      let res2 := aps_plus_compile_expr ξ acc e2 in
      let res3 := aps_plus_compile_expr ξ acc e3 in
      let dir ς := DataStore (res1.(aps_plus_result_dir) ς) (res2.(aps_plus_result_dir) ς) (res3.(aps_plus_result_dir) ς) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps ς :=
          DataBinop DataPlus acc' (dir ς) ;
      |}
  end.
#[global] Arguments aps_plus_compile_expr _ _ !_ / : assert.

Definition aps_plus_compute_mapping' progₛ : aps_plus_mapping * _ :=
  map_fold (λ func defₛ '(ξ, img),
    if decide (aps_plus_annotation ∈ defₛ.(data_definition_annot)) then
      let func_aps := fresh (dom progₛ ∪ img) in
      (<[func := func_aps]> ξ, {[func_aps]} ∪ img)
    else
      (ξ, img)
  ) (∅, ∅) progₛ.
Definition aps_plus_compute_mapping progₛ :=
  (aps_plus_compute_mapping' progₛ).1.

Definition aps_plus_compile' progₛ ξ :=
  map_fold (λ func defₛ progₜ,
    let annot := defₛ.(data_definition_annot) in
    let res := aps_plus_compile_expr ξ 1 defₛ.(data_definition_body) in
    let progₜ :=
      <[func :=
        {|data_definition_annot :=
            annot ;
          data_definition_body :=
            res.(aps_plus_result_dir) ids ;
        |}
      ]> progₜ
    in
    let progₜ :=
      match ξ !! func with
      | None =>
          progₜ
      | Some func_aps =>
          <[func_aps :=
            {|data_definition_annot :=
                annot ;
              data_definition_body :=
                DataLet (DataLoad (DataVar 0) (DataVal $ DataIndex DataOne)) $
                DataLet (DataLoad (DataVar 1) (DataVal $ DataIndex DataTwo)) $
                res.(aps_plus_result_aps) ids ;
            |}
          ]> progₜ
      end
    in
    progₜ
  ) ∅ progₛ.
Definition aps_plus_compile progₛ :=
  aps_plus_compile' progₛ (aps_plus_compute_mapping progₛ).

Lemma aps_plus_compile_expr_sound' ξ acc ς e :
  let res := aps_plus_compile_expr ξ acc e in
  aps_plus_expr_dir ξ e.[ς] (res.(aps_plus_result_dir) ς) ∧
  aps_plus_expr_aps ξ (DataVar acc) e.[ς] (res.(aps_plus_result_aps) ς).
Proof.
  move: acc ς. induction e as [| | | e1 | | op e1 ? e2 | | | | | |] => acc ς res /=.
  - auto with aps_plus.
  - auto with aps_plus.
  - naive_solver eauto with aps_plus.
  - rewrite {}/res /aps_plus_compile_expr -/aps_plus_compile_expr.
    destruct e1 as [[| | | | | | func annot] | | | | | | | | | | |].
    all: try naive_solver auto with aps_plus.
    destruct (ξ !! func) as [func_aps |] eqn:?.
    all: naive_solver eauto with aps_plus.
  - naive_solver auto with aps_plus.
  - destruct op.
    all: try naive_solver auto with aps_plus.
    destruct e1 as [[] | | | | | | | | | | |].
    5: {
      rewrite {}/res /=.
      case_decide.
      - split; econstructor; asimpl; naive_solver.
      - naive_solver auto with aps_plus.
    }
    all: naive_solver auto with aps_plus.
  - naive_solver auto with aps_plus.
  - naive_solver auto with aps_plus.
  - naive_solver auto with aps_plus.
  - naive_solver auto with aps_plus.
  - naive_solver auto with aps_plus.
  - naive_solver auto with aps_plus.
Qed.
Lemma aps_plus_compile_expr_sound ξ acc e :
  let res := aps_plus_compile_expr ξ acc e in
  aps_plus_expr_dir ξ e (res.(aps_plus_result_dir) ids) ∧
  aps_plus_expr_aps ξ (DataVar acc) e (res.(aps_plus_result_aps) ids).
Proof.
  rewrite -{-1}(subst_id e). apply aps_plus_compile_expr_sound'.
Qed.
Lemma aps_plus_compile_expr_sound_dir ξ acc e :
  aps_plus_expr_dir ξ e ((aps_plus_compile_expr ξ acc e).(aps_plus_result_dir) ids).
Proof.
  apply aps_plus_compile_expr_sound.
Qed.
Lemma aps_plus_compile_expr_sound_aps ξ acc e :
  aps_plus_expr_aps ξ (DataVar acc) e ((aps_plus_compile_expr ξ acc e).(aps_plus_result_aps) ids).
Proof.
  apply aps_plus_compile_expr_sound.
Qed.

Record aps_plus_mapping_wf progₛ ξ := {
  aps_plus_mapping_wf_dom :
    dom ξ ⊆ dom progₛ ;
  aps_plus_mapping_wf_img :
    map_img ξ ## dom progₛ ;
  aps_plus_mapping_wf_inj func1 func2 func_aps :
    ξ !! func1 = Some func_aps →
    ξ !! func2 = Some func_aps →
    func1 = func2 ;
}.
Lemma aps_plus_compute_mapping'_sound progₛ :
  let res := aps_plus_compute_mapping' progₛ in
  aps_plus_mapping_wf progₛ res.1 ∧
  res.2 = map_img res.1.
Proof.
  pose (P (acc : aps_plus_mapping * gset _) progₛ' :=
    let ξ := acc.1 in
    let img := acc.2 in
    ( img = map_img ξ
    ) ∧ (
      dom ξ ⊆ dom progₛ'
    ) ∧ (
      map_img ξ ## dom progₛ
    ) ∧ (
      ∀ func1 func2 func_aps,
      ξ !! func1 = Some func_aps →
      ξ !! func2 = Some func_aps →
      func1 = func2
    )
  ).
  cut (P (aps_plus_compute_mapping' progₛ) progₛ).
  { intros (? & ? & ? & ?). repeat split; done. }
  apply (map_fold_strong_ind P).
  - repeat split; done.
  - intros func defₛ progₛ' (ξ, img) Hprogₛ' Hprogₛ_lookup Hprogₛ'_lookup (? & Hξ_dom & Hξ_img & Hξ_inj). simplify.
    case_decide.
    + repeat split.
      * rewrite map_img_insert_notin_L //.
        apply not_elem_of_dom => Hξ_lookup.
        apply not_elem_of_dom in Hprogₛ'_lookup.
        naive_solver.
      * set_solver.
      * rewrite map_img_insert disjoint_union_l. split.
        { pose proof (is_fresh (dom progₛ ∪ map_img ξ)). set_solver. }
        { pose proof (map_img_delete_subseteq (SA := gset _) func ξ). set_solver. }
      * simpl. intros func1 func2 func_aps [(<- & ?) | (? & Hξ_lookup_1)]%lookup_insert_Some [(<- & ?) | (? & Hξ_lookup_2)]%lookup_insert_Some.
        { done. }
        { pose proof (is_fresh (dom progₛ ∪ map_img ξ)).
          apply (elem_of_map_img_2 (SA := gset _)) in Hξ_lookup_2.
          set_solver.
        } {
          pose proof (is_fresh (dom progₛ ∪ map_img ξ)).
          apply (elem_of_map_img_2 (SA := gset _)) in Hξ_lookup_1.
          set_solver.
        } {
          naive_solver.
        }
    + repeat split; set_solver.
Qed.
Lemma aps_plus_compute_mapping_sound progₛ :
  aps_plus_mapping_wf progₛ (aps_plus_compute_mapping progₛ).
Proof.
  pose proof aps_plus_compute_mapping'_sound. naive_solver.
Qed.

Lemma aps_plus_compile'_sound progₛ ξ :
  aps_plus_mapping_wf progₛ ξ →
  aps_plus progₛ (aps_plus_compile' progₛ ξ).
Proof.
  intros (Hξ_dom, Hξ_img, Hξ_inj).
  pose (P progₜ progₛ :=
    ( dom progₜ = dom progₛ ∪ map_img (restrict (dom progₛ) ξ)
    ) ∧ (
      ∀ func defₛ,
      progₛ !! func = Some defₛ →
        ∃ eₜ,
        aps_plus_expr_dir ξ defₛ.(data_definition_body) eₜ ∧
        progₜ !! func =
          Some {|
            data_definition_annot :=
              defₛ.(data_definition_annot) ;
            data_definition_body :=
              eₜ ;
          |}
    ) ∧ (
      ∀ func defₛ func_aps,
      progₛ !! func = Some defₛ →
      ξ !! func = Some func_aps →
        ∃ eₜ,
        aps_plus_expr_aps ξ (DataVar 1) defₛ.(data_definition_body) eₜ ∧
        progₜ !! func_aps =
          Some {|
            data_definition_annot :=
              defₛ.(data_definition_annot) ;
            data_definition_body :=
              DataLet (DataLoad (DataVar 0) (DataVal $ DataIndex DataOne)) $
              DataLet (DataLoad (DataVar 1) (DataVal $ DataIndex DataTwo)) $
              eₜ ;
          |}
    )
  ).
  cut (P (aps_plus_compile' progₛ ξ) progₛ).
  { intros (Hprogₜ_dom & Hdir & Haps). exists ξ; try naive_solver.
    rewrite Hprogₜ_dom restrict_subseteq //.
  }
  eapply (map_fold_strong_ind P).
  - split_and!; [| done..].
    rewrite dom_empty_L restrict_empty //.
  - intros func defₛ progₛ' progₜ Hprogₛ' Hprogₛ_lookup Hprogₛ'_lookup (Hprogₜ_dom & Hdir & Haps). split_and!.
    + destruct (ξ !! func) as [func_aps |] eqn:Hξ_lookup; simpl.
      * rewrite !dom_insert_L Hprogₜ_dom restrict_union map_img_union_disjoint_L.
        { apply restrict_disjoint, disjoint_singleton_l, not_elem_of_dom_2. done. }
        rewrite (restrict_singleton_Some func_aps) // map_img_singleton_L //.
        set_solver.
      * rewrite !dom_insert_L Hprogₜ_dom restrict_union map_img_union_disjoint_L.
        { apply restrict_disjoint, disjoint_singleton_l, not_elem_of_dom_2. done. }
        rewrite restrict_singleton_None //.
        set_solver.
    + intros func' defₛ' [(<- & <-) | (Hfunc' & Hprogₛ'_lookup')]%lookup_insert_Some.
      * eexists. split.
        { apply aps_plus_compile_expr_sound_dir. }
        { destruct (ξ !! func) as [func_aps |] eqn:Hξ_lookup; simpl.
          - rewrite lookup_insert_ne.
            { intros ->.
              apply elem_of_dom_2 in Hprogₛ_lookup.
              apply (elem_of_map_img_2 (SA := gset _)) in Hξ_lookup.
              naive_solver.
            }
            rewrite lookup_insert //.
          - rewrite lookup_insert //.
        }
      * efeed destruct Hdir as (eₜ & ? & Hprogₜ_lookup'); first done.
        eexists. split.
        { done. }
        { destruct (ξ !! func) as [func_aps |] eqn:Hξ_lookup; simpl.
          - rewrite lookup_insert_ne.
            { intros ->.
              assert (func' ∈ dom progₛ).
              { apply elem_of_dom, (lookup_weaken_is_Some progₛ'); done. }
              apply (elem_of_map_img_2 (SA := gset _)) in Hξ_lookup.
              naive_solver.
            }
            rewrite lookup_insert_ne //.
          - rewrite lookup_insert_ne //.
        }
    + intros func' defₛ' func_aps' [(<- & <-) | (Hfunc' & Hprogₛ'_lookup')]%lookup_insert_Some Hξ_lookup'.
      * eexists. split.
        { apply aps_plus_compile_expr_sound_aps. }
        { destruct (ξ !! func) as [func_aps |] eqn:Hξ_lookup; simplify.
          rewrite lookup_insert //.
        }
      * efeed destruct Haps as (eₜ & ? & Hprogₜ_lookup'); [done.. |].
        eexists. split.
        { done. }
        { destruct (ξ !! func) as [func_aps |] eqn:Hξ_lookup; simpl.
          - rewrite lookup_insert_ne.
            { intros <-. eapply Hfunc', Hξ_inj; done. }
            rewrite lookup_insert_ne //.
            { intros <-.
              apply elem_of_dom_2 in Hprogₛ_lookup.
              apply (elem_of_map_img_2 (SA := gset _)) in Hξ_lookup'.
              naive_solver.
            }
          - rewrite lookup_insert_ne //.
            { intros <-.
              apply elem_of_dom_2 in Hprogₛ_lookup.
              apply (elem_of_map_img_2 (SA := gset _)) in Hξ_lookup'.
              naive_solver.
            }
        }
Qed.
Lemma aps_plus_compile_sound progₛ :
  aps_plus progₛ (aps_plus_compile progₛ).
Proof.
  apply aps_plus_compile'_sound, aps_plus_compute_mapping_sound.
Qed.
