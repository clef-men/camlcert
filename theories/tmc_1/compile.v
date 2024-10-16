From camlcert Require Import
  prelude.
From camlcert.common Require Import
  gmap.
From camlcert.tmc_1 Require Export
  metatheory.
From camlcert Require Import
  options.

Implicit Types prog progₛ progₜ : data_program.
Implicit Types ξ : tmc_mapping.

Definition tmc_annotation :=
  "tmc".

Inductive tmc_hint :=
  | TmcYes
  | TmcNo
  | TmcMaybe.
Implicit Types hint : tmc_hint.

#[global] Instance tmc_hint_join : Join tmc_hint :=
  λ hint1 hint2,
    match hint1 with
    | TmcYes =>
        TmcYes
    | TmcNo =>
        hint2
    | TmcMaybe =>
        match hint2 with
        | TmcNo =>
            TmcMaybe
        | _ =>
            hint2
        end
    end.

Definition tmc_hint_le hint1 hint2 :=
  match hint2 with
  | TmcYes =>
      true
  | TmcNo =>
      if hint1 is TmcNo then true else false
  | TmcMaybe =>
      if hint1 is TmcYes then false else true
  end.
#[global] Instance tmc_hint_sqsubseteq : SqSubsetEq tmc_hint :=
  λ hint1 hint2,
    tmc_hint_le hint1 hint2 = true.
#[global] Instance tmc_hint_sqsubseteq_dec hint1 hint2 : Decision (hint1 ⊑ hint2) :=
  decide (tmc_hint_le hint1 hint2 = true).

Record tmc_result := {
  tmc_result_hint : tmc_hint ;
  tmc_result_dir : (var → data_expr) → data_expr ;
  tmc_result_dps : (var → data_expr) → data_expr ;
}.

Fixpoint tmc_compile_expr ξ dst idx e :=
  let dst' := DataVar dst in
  match e with
  | DataVal _ =>
      let dir := e in
      {|tmc_result_hint :=
          TmcNo ;
        tmc_result_dir ς :=
          dir ;
        tmc_result_dps ς :=
          DataStore dst' idx dir ;
      |}
  | DataVar x =>
      let dir ς := ς x in
      {|tmc_result_hint :=
          TmcNo ;
        tmc_result_dir :=
          dir ;
        tmc_result_dps ς :=
          DataStore dst' idx (dir ς) ;
      |}
  | DataLet e1 e2 =>
      let res1 := tmc_compile_expr ξ dst idx e1 in
      let res2 := tmc_compile_expr ξ (S dst) idx.[ren (+1)] e2 in
      {|tmc_result_hint :=
          res2.(tmc_result_hint) ;
        tmc_result_dir ς :=
          DataLet (res1.(tmc_result_dir) ς) (res2.(tmc_result_dir) (up ς)) ;
        tmc_result_dps ς :=
          DataLet (res1.(tmc_result_dir) ς) (res2.(tmc_result_dps) (up ς)) ;
      |}
  | DataCall (DataVal (DataFunc func annot)) e =>
      let res := tmc_compile_expr ξ dst idx e in
      let dir ς := DataCall (DataVal $ DataFunc func annot) (res.(tmc_result_dir) ς) in
      match ξ !! func with
      | None =>
          {|tmc_result_hint :=
              TmcNo ;
            tmc_result_dir :=
              dir ;
            tmc_result_dps ς :=
              DataStore dst' idx (dir ς) ;
          |}
      | Some func_dps =>
          {|tmc_result_hint :=
              if decide (tmc_annotation ∈ annot) then TmcYes else TmcMaybe ;
            tmc_result_dir :=
              dir ;
            tmc_result_dps ς :=
              DataLet (res.(tmc_result_dir) ς) $
              DataCall (DataVal $ DataFunc func_dps annot) (DataBlock data_tag_pair (DataBlock data_tag_pair (DataVar $ S dst) idx.[ren (+1)]) (DataVar 0)) ;
          |}
      end
  | DataCall e1 e2 =>
      let res1 := tmc_compile_expr ξ dst idx e1 in
      let res2 := tmc_compile_expr ξ dst idx e2 in
      let dir ς := DataCall (res1.(tmc_result_dir) ς) (res2.(tmc_result_dir) ς) in
      {|tmc_result_hint :=
          TmcNo ;
        tmc_result_dir :=
          dir ;
        tmc_result_dps ς :=
          DataStore dst' idx (dir ς) ;
      |}
  | DataUnop op e =>
      let res := tmc_compile_expr ξ dst idx e in
      let dir ς := DataUnop op (res.(tmc_result_dir) ς) in
      {|tmc_result_hint :=
          TmcNo ;
        tmc_result_dir :=
          dir ;
        tmc_result_dps ς :=
          DataStore dst' idx (dir ς) ;
      |}
  | DataBinop op e1 e2 =>
      let res1 := tmc_compile_expr ξ dst idx e1 in
      let res2 := tmc_compile_expr ξ dst idx e2 in
      let dir ς := DataBinop op (res1.(tmc_result_dir) ς) (res2.(tmc_result_dir) ς) in
      {|tmc_result_hint :=
          TmcNo ;
        tmc_result_dir :=
          dir ;
        tmc_result_dps ς :=
          DataStore dst' idx (dir ς) ;
      |}
  | DataBinopDet op e1 e2 =>
      let res1 := tmc_compile_expr ξ dst idx e1 in
      let res2 := tmc_compile_expr ξ dst idx e2 in
      let dir ς := DataBinopDet op (res1.(tmc_result_dir) ς) (res2.(tmc_result_dir) ς) in
      {|tmc_result_hint :=
          TmcNo ;
        tmc_result_dir :=
          dir ;
        tmc_result_dps ς :=
          DataStore dst' idx (dir ς) ;
      |}
  | DataIf e0 e1 e2 =>
      let res0 := tmc_compile_expr ξ dst idx e0 in
      let res1 := tmc_compile_expr ξ dst idx e1 in
      let res2 := tmc_compile_expr ξ dst idx e2 in
      {|tmc_result_hint :=
          res1.(tmc_result_hint) ⊔ res2.(tmc_result_hint) ;
        tmc_result_dir ς :=
          DataIf (res0.(tmc_result_dir) ς) (res1.(tmc_result_dir) ς) (res2.(tmc_result_dir) ς) ;
        tmc_result_dps ς :=
          DataIf (res0.(tmc_result_dir) ς) (res1.(tmc_result_dps) ς) (res2.(tmc_result_dps) ς) ;
      |}
  | DataBlock tag e1 e2 =>
      let res1 := tmc_compile_expr ξ 0 (DataVal $ DataIndex DataOne) e1 in
      let res2 := tmc_compile_expr ξ 0 (DataVal $ DataIndex DataTwo) e2 in
      if decide (res2.(tmc_result_hint) ⊔ TmcMaybe ⊑ res1.(tmc_result_hint)) then
        {|tmc_result_hint :=
            res1.(tmc_result_hint) ;
          tmc_result_dir ς :=
            DataLet (DataBlock tag (DataVal DataUnit) (res2.(tmc_result_dir) ς)) $
            DataLet (res1.(tmc_result_dps) (ς >> ren (+1))) $
            DataVar 1 ;
          tmc_result_dps ς :=
            DataLet (DataBlock tag (DataVal DataUnit) (res2.(tmc_result_dir) ς)) $
            DataLet (DataStore (DataVar $ S dst) idx.[ren (+1)] (DataVar 0)) $
            (res1.(tmc_result_dps) (ς >> ren (+1))).[ren (+1)] ;
        |}
      else if decide (TmcMaybe ⊑ res2.(tmc_result_hint)) then
        {|tmc_result_hint :=
            res2.(tmc_result_hint) ;
          tmc_result_dir ς :=
            DataLet (DataBlock tag (res1.(tmc_result_dir) ς) (DataVal DataUnit)) $
            DataLet (res2.(tmc_result_dps) (ς >> ren (+1))) $
            DataVar 1 ;
          tmc_result_dps ς :=
            DataLet (DataBlock tag (res1.(tmc_result_dir) ς) (DataVal DataUnit)) $
            DataLet (DataStore (DataVar $ S dst) idx.[ren (+1)] (DataVar 0)) $
            (res2.(tmc_result_dps) (ς >> ren (+1))).[ren (+1)] ;
        |}
      else
        let dir ς := DataBlock tag (res1.(tmc_result_dir) ς) (res2.(tmc_result_dir) ς) in
        {|tmc_result_hint :=
            TmcNo ;
          tmc_result_dir :=
            dir ;
          tmc_result_dps ς :=
            DataStore dst' idx (dir ς) ;
        |}
  | DataBlockDet tag e1 e2 =>
      let res1 := tmc_compile_expr ξ dst idx e1 in
      let res2 := tmc_compile_expr ξ dst idx e2 in
      let dir ς := DataBlockDet tag (res1.(tmc_result_dir) ς) (res2.(tmc_result_dir) ς) in
      {|tmc_result_hint :=
          TmcNo ;
        tmc_result_dir :=
          dir ;
        tmc_result_dps ς :=
          DataStore dst' idx (dir ς) ;
      |}
  | DataLoad e1 e2 =>
      let res1 := tmc_compile_expr ξ dst idx e1 in
      let res2 := tmc_compile_expr ξ dst idx e2 in
      let dir ς := DataLoad (res1.(tmc_result_dir) ς) (res2.(tmc_result_dir) ς) in
      {|tmc_result_hint :=
          TmcNo ;
        tmc_result_dir :=
          dir ;
        tmc_result_dps ς :=
          DataStore dst' idx (dir ς) ;
      |}
  | DataStore e1 e2 e3 =>
      let res1 := tmc_compile_expr ξ dst idx e1 in
      let res2 := tmc_compile_expr ξ dst idx e2 in
      let res3 := tmc_compile_expr ξ dst idx e3 in
      let dir ς := DataStore (res1.(tmc_result_dir) ς) (res2.(tmc_result_dir) ς) (res3.(tmc_result_dir) ς) in
      {|tmc_result_hint :=
          TmcNo ;
        tmc_result_dir :=
          dir ;
        tmc_result_dps ς :=
          DataStore dst' idx (dir ς) ;
      |}
  end.
#[global] Arguments tmc_compile_expr _ _ _ !_ / : assert.

Definition tmc_compute_mapping' progₛ : tmc_mapping * _ :=
  map_fold (λ func defₛ '(ξ, img),
    if decide (tmc_annotation ∈ defₛ.(data_definition_annot)) then
      let func_dps := fresh (dom progₛ ∪ img) in
      (<[func := func_dps]> ξ, {[func_dps]} ∪ img)
    else
      (ξ, img)
  ) (∅, ∅) progₛ.
Definition tmc_compute_mapping progₛ :=
  (tmc_compute_mapping' progₛ).1.

Definition tmc_compile' progₛ ξ :=
  map_fold (λ func defₛ progₜ,
    let annot := defₛ.(data_definition_annot) in
    let res := tmc_compile_expr ξ 1 (DataVar 2) defₛ.(data_definition_body) in
    let progₜ :=
      <[func :=
        {|data_definition_annot :=
            annot ;
          data_definition_body :=
            res.(tmc_result_dir) ids ;
        |}
      ]> progₜ
    in
    let progₜ :=
      match ξ !! func with
      | None =>
          progₜ
      | Some func_dps =>
          <[func_dps :=
            {|data_definition_annot :=
                annot ;
              data_definition_body :=
                DataLet (DataLoad (DataVar 0) (DataVal $ DataIndex DataOne)) $
                DataLet (DataLoad (DataVar 0) (DataVal $ DataIndex DataTwo)) $
                DataLet (DataLoad (DataVar 1) (DataVal $ DataIndex DataOne)) $
                DataLet (DataLoad (DataVar 3) (DataVal $ DataIndex DataTwo)) $
                res.(tmc_result_dps) ids ;
            |}
          ]> progₜ
      end
    in
    progₜ
  ) ∅ progₛ.
Definition tmc_compile progₛ :=
  tmc_compile' progₛ (tmc_compute_mapping progₛ).

Lemma tmc_compile_expr_sound' ξ dst idx ς e :
  let res := tmc_compile_expr ξ dst idx e in
  tmc_expr_dir ξ e.[ς] (res.(tmc_result_dir) ς) ∧
  tmc_expr_dps ξ (DataVar dst) idx e.[ς] (res.(tmc_result_dps) ς).
Proof.
  move: dst idx ς. induction e as [| | | e1 | | | | | | | |] => dst idx ς res /=.
  - auto with tmc.
  - auto with tmc.
  - split; constructor; naive_solver.
  - rewrite {}/res /tmc_compile_expr -/tmc_compile_expr.
    destruct e1 as [[| | | | | | func annot] | | | | | | | | | | |].
    all: try (split; constructor; naive_solver auto with tmc).
    destruct (ξ !! func) as [func_dps |] eqn:?.
    all: simpl; split; repeat econstructor; naive_solver.
  - split; repeat constructor; naive_solver.
  - split; repeat constructor; naive_solver.
  - split; repeat constructor; naive_solver.
  - split; constructor; naive_solver.
  - rewrite {}/res /=.
    case_match; last case_match.
    + split; econstructor; last autosubst; asimpl; naive_solver.
    + split; econstructor; last autosubst; asimpl; naive_solver.
    + split; repeat constructor; naive_solver.
  - split; repeat constructor; naive_solver.
  - split; repeat constructor; naive_solver.
  - split; repeat constructor; naive_solver.
Qed.
Lemma tmc_compile_expr_sound ξ dst idx e :
  let res := tmc_compile_expr ξ dst idx e in
  tmc_expr_dir ξ e (res.(tmc_result_dir) ids) ∧
  tmc_expr_dps ξ (DataVar dst) idx e (res.(tmc_result_dps) ids).
Proof.
  rewrite -{-1}(subst_id e). apply tmc_compile_expr_sound'.
Qed.
Lemma tmc_compile_expr_sound_dir ξ dst idx e :
  tmc_expr_dir ξ e ((tmc_compile_expr ξ dst idx e).(tmc_result_dir) ids).
Proof.
  apply tmc_compile_expr_sound.
Qed.
Lemma tmc_compile_expr_sound_dps ξ dst idx e :
  tmc_expr_dps ξ (DataVar dst) idx e ((tmc_compile_expr ξ dst idx e).(tmc_result_dps) ids).
Proof.
  apply tmc_compile_expr_sound.
Qed.

Record tmc_mapping_wf progₛ ξ := {
  tmc_mapping_wf_dom :
    dom ξ ⊆ dom progₛ ;
  tmc_mapping_wf_img :
    map_img ξ ## dom progₛ ;
  tmc_mapping_wf_inj func1 func2 func_dps :
    ξ !! func1 = Some func_dps →
    ξ !! func2 = Some func_dps →
    func1 = func2 ;
}.
Lemma tmc_compute_mapping'_sound progₛ :
  let res := tmc_compute_mapping' progₛ in
  tmc_mapping_wf progₛ res.1 ∧
  res.2 = map_img res.1.
Proof.
  pose (P (acc : tmc_mapping * gset _) progₛ' :=
    let ξ := acc.1 in
    let img := acc.2 in
    ( img = map_img ξ
    ) ∧ (
      dom ξ ⊆ dom progₛ'
    ) ∧ (
      map_img ξ ## dom progₛ
    ) ∧ (
      ∀ func1 func2 func_dps,
      ξ !! func1 = Some func_dps →
      ξ !! func2 = Some func_dps →
      func1 = func2
    )
  ).
  cut (P (tmc_compute_mapping' progₛ) progₛ).
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
      * simpl. intros func1 func2 func_dps [(<- & ?) | (? & Hξ_lookup_1)]%lookup_insert_Some [(<- & ?) | (? & Hξ_lookup_2)]%lookup_insert_Some.
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
Lemma tmc_compute_mapping_sound progₛ :
  tmc_mapping_wf progₛ (tmc_compute_mapping progₛ).
Proof.
  pose proof tmc_compute_mapping'_sound. naive_solver.
Qed.

Lemma tmc_compile'_sound progₛ ξ :
  tmc_mapping_wf progₛ ξ →
  tmc progₛ (tmc_compile' progₛ ξ).
Proof.
  intros (Hξ_dom, Hξ_img, Hξ_inj).
  pose (P progₜ progₛ :=
    ( dom progₜ = dom progₛ ∪ map_img (restrict (dom progₛ) ξ)
    ) ∧ (
      ∀ func defₛ,
      progₛ !! func = Some defₛ →
        ∃ eₜ,
        tmc_expr_dir ξ defₛ.(data_definition_body) eₜ ∧
        progₜ !! func =
          Some {|
            data_definition_annot :=
              defₛ.(data_definition_annot) ;
            data_definition_body :=
              eₜ ;
          |}
    ) ∧ (
      ∀ func defₛ func_dps,
      progₛ !! func = Some defₛ →
      ξ !! func = Some func_dps →
        ∃ eₜ,
        tmc_expr_dps ξ (DataVar 1) (DataVar 2) defₛ.(data_definition_body) eₜ ∧
        progₜ !! func_dps =
          Some {|
            data_definition_annot :=
              defₛ.(data_definition_annot) ;
            data_definition_body :=
              DataLet (DataLoad (DataVar 0) (DataVal $ DataIndex DataOne)) $
              DataLet (DataLoad (DataVar 0) (DataVal $ DataIndex DataTwo)) $
              DataLet (DataLoad (DataVar 1) (DataVal $ DataIndex DataOne)) $
              DataLet (DataLoad (DataVar 3) (DataVal $ DataIndex DataTwo)) $
              eₜ ;
          |}
    )
  ).
  cut (P (tmc_compile' progₛ ξ) progₛ).
  { intros (Hprogₜ_dom & Hdir & Hdps). exists ξ; try naive_solver.
    rewrite Hprogₜ_dom restrict_subseteq //.
  }
  eapply (map_fold_strong_ind P).
  - split_and!; [| done..].
    rewrite dom_empty_L restrict_empty //.
  - intros func defₛ progₛ' progₜ Hprogₛ' Hprogₛ_lookup Hprogₛ'_lookup (Hprogₜ_dom & Hdir & Hdps). split_and!.
    + destruct (ξ !! func) as [func_dps |] eqn:Hξ_lookup; simpl.
      * rewrite !dom_insert_L Hprogₜ_dom restrict_union map_img_union_disjoint_L.
        { apply restrict_disjoint, disjoint_singleton_l, not_elem_of_dom_2. done. }
        rewrite (restrict_singleton_Some func_dps) // map_img_singleton_L //.
        set_solver.
      * rewrite !dom_insert_L Hprogₜ_dom restrict_union map_img_union_disjoint_L.
        { apply restrict_disjoint, disjoint_singleton_l, not_elem_of_dom_2. done. }
        rewrite restrict_singleton_None //.
        set_solver.
    + intros func' defₛ' [(<- & <-) | (Hfunc' & Hprogₛ'_lookup')]%lookup_insert_Some.
      * eexists. split.
        { apply tmc_compile_expr_sound_dir. }
        { destruct (ξ !! func) as [func_dps |] eqn:Hξ_lookup; simpl.
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
        { destruct (ξ !! func) as [func_dps |] eqn:Hξ_lookup; simpl.
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
    + intros func' defₛ' func_dps' [(<- & <-) | (Hfunc' & Hprogₛ'_lookup')]%lookup_insert_Some Hξ_lookup'.
      * eexists. split.
        { apply tmc_compile_expr_sound_dps. }
        { destruct (ξ !! func) as [func_dps |] eqn:Hξ_lookup; simplify.
          rewrite lookup_insert //.
        }
      * efeed destruct Hdps as (eₜ & ? & Hprogₜ_lookup'); [done.. |].
        eexists. split.
        { done. }
        { destruct (ξ !! func) as [func_dps |] eqn:Hξ_lookup; simpl.
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
Lemma tmc_compile_sound progₛ :
  tmc progₛ (tmc_compile progₛ).
Proof.
  apply tmc_compile'_sound, tmc_compute_mapping_sound.
Qed.
