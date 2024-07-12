From camlcert Require Import
  prelude.
From camlcert.common Require Import
  gmap.
From camlcert.aps_plus Require Export
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
  aps_plus_result_dir : data_expr ;
  aps_plus_result_aps : data_expr ;
}.

Fixpoint aps_plus_compile_expr' ξ acc ς e :=
  let acc' := DataVar acc in
  match e with
  | DataVal _ =>
      let dir := e in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir
      |}
  | DataVar x =>
      let dir := ς x in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir ;
      |}
  | DataLet e1 e2 =>
      let res1 := aps_plus_compile_expr' ξ acc ς e1 in
      let res2 := aps_plus_compile_expr' ξ (S acc) (up ς) e2 in
      {|aps_plus_result_hint :=
          res2.(aps_plus_result_hint) ;
        aps_plus_result_dir :=
          DataLet res1.(aps_plus_result_dir) res2.(aps_plus_result_dir) ;
        aps_plus_result_aps :=
          DataLet res1.(aps_plus_result_dir) res2.(aps_plus_result_aps) ;
      |}
  | DataCall (DataVal (DataFunc func annot)) e =>
      let res := aps_plus_compile_expr' ξ acc ς e in
      let dir := DataCall (DataVal $ DataFunc func annot) res.(aps_plus_result_dir) in
      match ξ !! func with
      | None =>
          {|aps_plus_result_hint :=
              ApsPlusNo ;
            aps_plus_result_dir :=
              dir ;
            aps_plus_result_aps :=
              DataBinop DataPlus acc' dir ;
          |}
      | Some func_aps =>
          {|aps_plus_result_hint :=
              if decide (aps_plus_annotation ∈ annot) then ApsPlusYes else ApsPlusMaybe ;
            aps_plus_result_dir :=
              dir ;
            aps_plus_result_aps :=
              DataLet res.(aps_plus_result_dir) $
              DataCall (DataVal $ DataFunc func_aps annot) (DataBlock data_tag_pair (DataVar $ S acc) (DataVar 0)) ;
          |}
      end
  | DataCall e1 e2 =>
      let res1 := aps_plus_compile_expr' ξ acc ς e1 in
      let res2 := aps_plus_compile_expr' ξ acc ς e2 in
      let dir := DataCall res1.(aps_plus_result_dir) res2.(aps_plus_result_dir) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir ;
      |}
  | DataUnop op e =>
      let res := aps_plus_compile_expr' ξ acc ς e in
      let dir := DataUnop op res.(aps_plus_result_dir) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir ;
      |}
  | DataBinop DataPlus (DataVal (DataInt n)) e =>
      let res := aps_plus_compile_expr' ξ 0 ς e in
      if decide (ApsPlusMaybe ⊑ res.(aps_plus_result_hint)) then
        let res := aps_plus_compile_expr' ξ 0 (ς >> ren (+1)) e in
        {|aps_plus_result_hint :=
            res.(aps_plus_result_hint) ;
          aps_plus_result_dir :=
            DataLet (DataVal $ DataInt n) $
            res.(aps_plus_result_aps) ;
          aps_plus_result_aps :=
            DataLet (DataBinop DataPlus acc' (DataVal $ DataInt n)) $
            res.(aps_plus_result_aps) ;
        |}
      else
        let dir := DataBinop DataPlus (DataVal (DataInt n)) res.(aps_plus_result_dir) in
        {|aps_plus_result_hint :=
            ApsPlusNo ;
          aps_plus_result_dir :=
            dir ;
          aps_plus_result_aps :=
            DataBinop DataPlus acc' dir ;
        |}
  (* | DataBinop DataPlus e (DataVal (DataInt n)) => *)
  (*     let res := aps_plus_compile_expr' ξ 0 ς e in *)
  (*     if decide (ApsPlusMaybe ⊑ res.(aps_plus_result_hint)) then *)
  (*       let res := aps_plus_compile_expr' ξ 0 (ς >> ren (+1)) e in *)
  (*       {|aps_plus_result_hint := *)
  (*           res.(aps_plus_result_hint) ; *)
  (*         aps_plus_result_dir := *)
  (*           DataLet (DataVal $ DataInt n) $ *)
  (*           res.(aps_plus_result_aps) ; *)
  (*         aps_plus_result_aps := *)
  (*           DataLet (DataBinop DataPlus acc' (DataVal $ DataInt n)) $ *)
  (*           res.(aps_plus_result_aps) ; *)
  (*       |} *)
  (*     else *)
  (*       let dir := DataBinop DataPlus res.(aps_plus_result_dir) (DataVal (DataInt n)) in *)
  (*       {|aps_plus_result_hint := *)
  (*           ApsPlusNo ; *)
  (*         aps_plus_result_dir := *)
  (*           dir ; *)
  (*         aps_plus_result_aps := *)
  (*           DataBinop DataPlus acc' dir ; *)
  (*       |} *)
  | DataBinop op e1 e2 =>
      let res1 := aps_plus_compile_expr' ξ acc ς e1 in
      let res2 := aps_plus_compile_expr' ξ acc ς e2 in
      let dir := DataBinop op res1.(aps_plus_result_dir) res2.(aps_plus_result_dir) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir ;
      |}
  | DataBinopDet op e1 e2 =>
      let res1 := aps_plus_compile_expr' ξ acc ς e1 in
      let res2 := aps_plus_compile_expr' ξ acc ς e2 in
      let dir := DataBinopDet op res1.(aps_plus_result_dir) res2.(aps_plus_result_dir) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir ;
      |}
  | DataIf e0 e1 e2 =>
      let res0 := aps_plus_compile_expr' ξ acc ς e0 in
      let res1 := aps_plus_compile_expr' ξ acc ς e1 in
      let res2 := aps_plus_compile_expr' ξ acc ς e2 in
      {|aps_plus_result_hint :=
          res1.(aps_plus_result_hint) ⊔ res2.(aps_plus_result_hint) ;
        aps_plus_result_dir :=
          DataIf res0.(aps_plus_result_dir) res1.(aps_plus_result_dir) res2.(aps_plus_result_dir) ;
        aps_plus_result_aps :=
          DataIf res0.(aps_plus_result_dir) res1.(aps_plus_result_aps) res2.(aps_plus_result_aps) ;
      |}
  | DataBlock tag e1 e2 =>
      let res1 := aps_plus_compile_expr' ξ acc ς e1 in
      let res2 := aps_plus_compile_expr' ξ acc ς e2 in
      let dir := DataBlock tag res1.(aps_plus_result_dir) res2.(aps_plus_result_dir) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir ;
      |}
  | DataBlockDet tag e1 e2 =>
      let res1 := aps_plus_compile_expr' ξ acc ς e1 in
      let res2 := aps_plus_compile_expr' ξ acc ς e2 in
      let dir := DataBlockDet tag res1.(aps_plus_result_dir) res2.(aps_plus_result_dir) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir ;
      |}
  | DataLoad e1 e2 =>
      let res1 := aps_plus_compile_expr' ξ acc ς e1 in
      let res2 := aps_plus_compile_expr' ξ acc ς e2 in
      let dir := DataLoad res1.(aps_plus_result_dir) res2.(aps_plus_result_dir) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir ;
      |}
  | DataStore e1 e2 e3 =>
      let res1 := aps_plus_compile_expr' ξ acc ς e1 in
      let res2 := aps_plus_compile_expr' ξ acc ς e2 in
      let res3 := aps_plus_compile_expr' ξ acc ς e3 in
      let dir := DataStore res1.(aps_plus_result_dir) res2.(aps_plus_result_dir) res3.(aps_plus_result_dir) in
      {|aps_plus_result_hint :=
          ApsPlusNo ;
        aps_plus_result_dir :=
          dir ;
        aps_plus_result_aps :=
          DataBinop DataPlus acc' dir ;
      |}
  end.
#[global] Arguments aps_plus_compile_expr' _ _ _ !_ / : assert.

Definition aps_plus_compile_expr ξ acc e :=
  aps_plus_compile_expr' ξ acc ids e.

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
            res.(aps_plus_result_dir) ;
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
                res.(aps_plus_result_aps) ;
            |}
          ]> progₜ
      end
    in
    progₜ
  ) ∅ progₛ.
Definition aps_plus_compile progₛ :=
  aps_plus_compile' progₛ (aps_plus_compute_mapping progₛ).

Lemma aps_plus_compile_expr'_sound ξ acc ς e :
  let res := aps_plus_compile_expr' ξ acc ς e in
  aps_plus_expr_dir ξ e.[ς] res.(aps_plus_result_dir) ∧
  aps_plus_expr_aps ξ (DataVar acc) e.[ς] res.(aps_plus_result_aps).
Proof.
  move: acc ς. induction e as [| | | e1 | | op e1 ? e2 | | | | | |] => acc ς res /=.
  - auto with aps_plus.
  - auto with aps_plus.
  - naive_solver eauto with aps_plus.
  - rewrite {}/res /aps_plus_compile_expr' -/aps_plus_compile_expr'.
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
  aps_plus_expr_dir ξ e res.(aps_plus_result_dir) ∧
  aps_plus_expr_aps ξ (DataVar acc) e res.(aps_plus_result_aps).
Proof.
  rewrite -{-1}(subst_id e). apply aps_plus_compile_expr'_sound.
Qed.
Lemma aps_plus_compile_expr_sound_dir ξ acc e :
  aps_plus_expr_dir ξ e (aps_plus_compile_expr ξ acc e).(aps_plus_result_dir).
Proof.
  apply aps_plus_compile_expr_sound.
Qed.
Lemma aps_plus_compile_expr_sound_aps ξ acc e :
  aps_plus_expr_aps ξ (DataVar acc) e (aps_plus_compile_expr ξ acc e).(aps_plus_result_aps).
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
