From simuliris Require Import
  prelude.
From simuliris.inline Require Export
  metatheory.

Implicit Types prog : data_program.

Definition inline_annotation :=
  "inline".

Definition inline_max_depth :=
  10.

Fixpoint inline_compile_expr prog depth := fix inline_compile_expr' e :=
  match e with
  | DataVal _
  | DataVar _ =>
      e
  | DataLet e1 e2 =>
      DataLet
        (inline_compile_expr' e1)
        (inline_compile_expr' e2)
  | DataCall e1 e2 =>
      match e1 with
      | DataVal (DataFunc func annot) =>
          match bool_decide (inline_annotation ∈ annot), prog !! func with
          | true, Some e_func =>
              let e_func :=
                match depth with
                | 0 =>
                    e_func
                | S depth =>
                    inline_compile_expr prog depth e_func
                end
              in
              DataLet
                (inline_compile_expr' e2)
                e_func
          | _, _ =>
              DataCall
                (inline_compile_expr' e1)
                (inline_compile_expr' e2)
          end
      | _ =>
          DataCall
            (inline_compile_expr' e1)
            (inline_compile_expr' e2)
      end
  | DataUnop op e =>
      DataUnop op
        (inline_compile_expr' e)
  | DataBinop op e1 e2 =>
      DataBinop op
        (inline_compile_expr' e1)
        (inline_compile_expr' e2)
  | DataBinopDet op e1 e2 =>
      DataBinopDet op
        (inline_compile_expr' e1)
        (inline_compile_expr' e2)
  | DataIf e0 e1 e2 =>
      DataIf
        (inline_compile_expr' e0)
        (inline_compile_expr' e1)
        (inline_compile_expr' e2)
  | DataConstr tag e1 e2 =>
      DataConstr tag
        (inline_compile_expr' e1)
        (inline_compile_expr' e2)
  | DataConstrDet tag e1 e2 =>
      DataConstrDet tag
        (inline_compile_expr' e1)
        (inline_compile_expr' e2)
  | DataLoad e1 e2 =>
      DataLoad
        (inline_compile_expr' e1)
        (inline_compile_expr' e2)
  | DataStore e1 e2 e3 =>
      DataStore
        (inline_compile_expr' e1)
        (inline_compile_expr' e2)
        (inline_compile_expr' e3)
  end.
#[global] Arguments inline_compile_expr _ _ !_ / : assert.

Definition inline_compile prog :=
  (inline_compile_expr prog inline_max_depth) <$> prog.

Lemma inline_compile_expr_sound prog depth e :
  inline_expr prog e (inline_compile_expr prog depth e).
Proof.
  revert e. induction depth; induction e.
  all: eauto with inline.
  all: do 4 (simpl; case_match; eauto with inline).
Qed.
Lemma inline_compile_sound prog :
  inline prog (inline_compile prog).
Proof.
  split.
  - rewrite dom_fmap_L //.
  - intros func e Hfunc. eexists. split.
    + apply inline_compile_expr_sound.
    + rewrite lookup_fmap Hfunc //.
Qed.
