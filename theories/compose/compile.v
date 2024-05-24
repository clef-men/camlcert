From stdpp Require Import
  stringmap.

From camlcert Require Import
  prelude.
From camlcert.data_lang Require Import
  subexpr.
From camlcert.compose Require Export
  metatheory.

Implicit Types prog progₛ progₜ : data_program.

Section compose_compile_expr.
  Context (func1 func2 func : data_function).

  Fixpoint compose_compile_expr_dir e :=
    match e with
    | DataVal _
    | DataVar _ =>
        e
    | DataLet e1 e2 =>
        DataLet
          (compose_compile_expr_dir e1)
          (compose_compile_expr_dir e2)
    | DataCall e1 e2 =>
        match e1, e2 with
        | DataVal (DataFunc func2' annot2), DataCall (DataVal (DataFunc func1' annot1)) e2' =>
            if bool_decide (func1 = func1') && bool_decide (func2 = func2') then (
              DataCall
                (DataVal (DataFunc func annot1))
                (compose_compile_expr_dir e2')
            ) else (
              DataCall
                (compose_compile_expr_dir e1)
                (compose_compile_expr_dir e2)
            )
        | _, _ =>
            DataCall
              (compose_compile_expr_dir e1)
              (compose_compile_expr_dir e2)
        end
    | DataUnop op e =>
        DataUnop op
          (compose_compile_expr_dir e)
    | DataBinop op e1 e2 =>
        DataBinop op
          (compose_compile_expr_dir e1)
          (compose_compile_expr_dir e2)
    | DataBinopDet op e1 e2 =>
        DataBinopDet op
          (compose_compile_expr_dir e1)
          (compose_compile_expr_dir e2)
    | DataIf e0 e1 e2 =>
        DataIf
          (compose_compile_expr_dir e0)
          (compose_compile_expr_dir e1)
          (compose_compile_expr_dir e2)
    | DataBlock tag e1 e2 =>
        DataBlock tag
          (compose_compile_expr_dir e1)
          (compose_compile_expr_dir e2)
    | DataBlockDet tag e1 e2 =>
        DataBlockDet tag
          (compose_compile_expr_dir e1)
          (compose_compile_expr_dir e2)
    | DataLoad e1 e2 =>
        DataLoad
          (compose_compile_expr_dir e1)
          (compose_compile_expr_dir e2)
    | DataStore e1 e2 e3 =>
        DataStore
          (compose_compile_expr_dir e1)
          (compose_compile_expr_dir e2)
          (compose_compile_expr_dir e3)
    end.
  #[global] Arguments compose_compile_expr_dir !_ / : assert.

  Fixpoint compose_compile_expr_comp e :=
    match e with
    | DataLet e1 e2 =>
        DataLet
          (compose_compile_expr_dir e1)
          (compose_compile_expr_comp e2)
    | DataCall (DataVal (DataFunc func1' annot)) e =>
        if bool_decide (func1 = func1') then (
          DataCall
            (DataVal (DataFunc func annot))
            (compose_compile_expr_dir e)
        ) else (
          DataCall
            (DataVal (DataFunc func2 []))
            (DataCall
              (DataVal (DataFunc func1' annot))
              (compose_compile_expr_dir e))
        )
    | DataIf e0 e1 e2 =>
        DataIf
          (compose_compile_expr_dir e0)
          (compose_compile_expr_comp e1)
          (compose_compile_expr_comp e2)
    | _ =>
      DataCall
        (DataVal (DataFunc func2 []))
        (compose_compile_expr_dir e)
    end.
  #[global] Arguments compose_compile_expr_comp !_ / : assert.

  Lemma compose_compile_expr_dir_sound e :
    compose_expr_dir func1 func2 func e (compose_compile_expr_dir e).
  Proof.
    induction e as [e IHe] using (well_founded_ind data_subexpr_wf);
      destruct e;
      try (constructor; auto with data_lang).
    simpl.
    do 5 (case_match; subst; try (constructor; auto with data_lang)).
    do 2 (case_bool_decide; subst; last (repeat constructor; auto with data_lang)).
    apply compose_expr_dir_call_compose. auto with data_lang.
  Qed.
  Lemma compose_compile_expr_comp_sound e :
    compose_expr_comp func1 func2 func e (compose_compile_expr_comp e).
  Proof.
    induction e;
      eauto using compose_compile_expr_dir_sound with compose.
    simpl.
    do 2 (case_match; subst; eauto using compose_compile_expr_dir_sound with compose).
    case_bool_decide; subst; last eauto using compose_compile_expr_dir_sound with compose.
    apply compose_expr_comp_call_compose, compose_compile_expr_dir_sound.
  Qed.
End compose_compile_expr.

Definition compose_compile_fresh func1 func2 progₛ :=
  fresh_string (func2 +:+ "_" +:+ func1) progₛ.
Definition compose_compile func1 func2 (progₛ : data_program) :=
  let func := compose_compile_fresh func1 func2 progₛ in
  let progₜ :=
    (λ def,
      {|data_definition_annot :=
          def.(data_definition_annot) ;
        data_definition_body :=
          compose_compile_expr_dir func1 func2 func def.(data_definition_body)
      |}
    ) <$> progₛ
  in
  match progₛ !! func1 with
  | None =>
      progₜ
  | Some def1ₛ =>
    <[func :=
      {|data_definition_annot :=
          def1ₛ.(data_definition_annot) ;
        data_definition_body :=
          compose_compile_expr_comp func1 func2 func def1ₛ.(data_definition_body) ;
      |}
    ]> progₜ
  end.

Lemma compose_compile_fresh_sound func1 func2 progₛ :
  progₛ !! compose_compile_fresh func1 func2 progₛ = None.
Proof.
  apply fresh_string_fresh.
Qed.
Lemma compose_compile_sound func1 func2 progₛ :
  func1 ∈ dom progₛ →
  func2 ∈ dom progₛ →
  compose func1 func2 progₛ (compose_compile func1 func2 progₛ).
Proof.
  intros Hfunc1ₛ Hfunc2ₛ.
  pose proof Hfunc1ₛ as Hfunc1ₛ'%lookup_lookup_total_dom.
  rewrite /compose_compile Hfunc1ₛ'.
  esplit; try done.
  - rewrite dom_insert_L dom_fmap_L //.
  - intros func defₛ Hfuncₛ. eexists. split.
    + apply compose_compile_expr_dir_sound.
    + rewrite lookup_insert_ne; last first.
      { pose proof (compose_compile_fresh_sound func1 func2 progₛ). naive_solver. }
      rewrite lookup_fmap Hfuncₛ //.
  - repeat eexists; first done.
    + apply compose_compile_expr_comp_sound.
    + rewrite lookup_insert //.
Qed.
