From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  syntax.
From simuliris.data_lang Require Import
  notations.

Implicit Types func : data_function.
Implicit Types annot : data_annotation.
Implicit Types v vₛ vₜ : data_val.
Implicit Types e eₛ eₜ : data_expr.
Implicit Types prog progₛ progₜ : data_program.

Inductive compose_expr_dir func1 func2 func : data_expr → data_expr → Prop :=
  | compose_expr_dir_val v :
      compose_expr_dir func1 func2 func
        v
        v
  | compose_expr_dir_var x :
      compose_expr_dir func1 func2 func
        $x
        $x
  | compose_expr_dir_let eₛ1 eₛ2 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_dir func1 func2 func eₛ2 eₜ2 →
      compose_expr_dir func1 func2 func
        (let: eₛ1 in eₛ2)
        (let: eₜ1 in eₜ2)
  | compose_expr_dir_call eₛ1 eₛ2 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_dir func1 func2 func eₛ2 eₜ2 →
      compose_expr_dir func1 func2 func
        (eₛ1 eₛ2)
        (eₜ1 eₜ2)
  | compose_expr_dir_call_compose annot1 annot2 eₛ eₜ :
      compose_expr_dir func1 func2 func eₛ eₜ →
      compose_expr_dir func1 func2 func
        ((DataFunc func2 annot1) ((DataFunc func1 annot2) eₛ))
        ((DataFunc func annot1) eₜ)
  | compose_expr_dir_unop op eₛ eₜ :
      compose_expr_dir func1 func2 func eₛ eₜ →
      compose_expr_dir func1 func2 func
        (DataUnop op eₛ)
        (DataUnop op eₜ)
  | compose_expr_dir_binop op eₛ1 eₛ2 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_dir func1 func2 func eₛ2 eₜ2 →
      compose_expr_dir func1 func2 func
        (DataBinop op eₛ1 eₛ2)
        (DataBinop op eₜ1 eₜ2)
  | compose_expr_dir_binop_det op eₛ1 eₛ2 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_dir func1 func2 func eₛ2 eₜ2 →
      compose_expr_dir func1 func2 func
        (DataBinopDet op eₛ1 eₛ2)
        (DataBinopDet op eₜ1 eₜ2)
  | compose_expr_dir_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ0 eₜ0 →
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_dir func1 func2 func eₛ2 eₜ2 →
      compose_expr_dir func1 func2 func
        (if: eₛ0 then eₛ1 else eₛ2)
        (if: eₜ0 then eₜ1 else eₜ2)
  | compose_expr_dir_constr tag eₛ1 eₛ2 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_dir func1 func2 func eₛ2 eₜ2 →
      compose_expr_dir func1 func2 func
        (&tag eₛ1 eₛ2)
        (&tag eₜ1 eₜ2)
  | compose_expr_dir_constr_det tag eₛ1 eₛ2 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_dir func1 func2 func eₛ2 eₜ2 →
      compose_expr_dir func1 func2 func
        (&&tag eₛ1 eₛ2)
        (&&tag eₜ1 eₜ2)
  | compose_expr_dir_load eₛ1 eₛ2 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_dir func1 func2 func eₛ2 eₜ2 →
      compose_expr_dir func1 func2 func
        (![eₛ2] eₛ1)
        (![eₜ2] eₜ1)
  | compose_expr_dir_store eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_dir func1 func2 func eₛ2 eₜ2 →
      compose_expr_dir func1 func2 func eₛ3 eₜ3 →
      compose_expr_dir func1 func2 func
        (eₛ1 <-[eₛ2]- eₛ3)
        (eₜ1 <-[eₜ2]- eₜ3).

Inductive compose_expr_comp func1 func2 func : data_expr → data_expr → Prop :=
  | compose_expr_comp_base eₛ eₜ :
      compose_expr_dir func1 func2 func eₛ eₜ →
      compose_expr_comp func1 func2 func
        eₛ
        (func2 eₜ)
  | compose_expr_comp_let eₛ1 eₛ2 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ1 eₜ1 →
      compose_expr_comp func1 func2 func eₛ2 eₜ2 →
      compose_expr_comp func1 func2 func
        (let: eₛ1 in eₛ2)
        (let: eₜ1 in eₜ2)
  | compose_expr_comp_call_compose annot eₛ eₜ :
      compose_expr_dir func1 func2 func eₛ eₜ →
      compose_expr_comp func1 func2 func
        ((DataFunc func1 annot) eₛ)
        ((DataFunc func annot) eₜ)
  | compose_expr_comp_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      compose_expr_dir func1 func2 func eₛ0 eₜ0 →
      compose_expr_comp func1 func2 func eₛ1 eₜ1 →
      compose_expr_comp func1 func2 func eₛ2 eₜ2 →
      compose_expr_comp func1 func2 func
        (if: eₛ0 then eₛ1 else eₛ2)
        (if: eₜ0 then eₜ1 else eₜ2).

Create HintDb compose.

#[global] Hint Constructors compose_expr_dir : compose.
#[global] Hint Constructors compose_expr_comp : compose.

Record compose {progₛ progₜ func1 func2} := {
  compose_func : data_function ;

  compose_dom :
    dom progₜ = dom progₛ ∪ {[compose_func]} ;

  compose_dir func defₛ :
    progₛ !! func = Some defₛ →
      ∃ eₜ,
      compose_expr_dir func1 func2 compose_func defₛ.(data_definition_body) eₜ ∧
      progₜ !! func =
        Some {|
          data_definition_annot :=
            defₛ.(data_definition_annot) ;
          data_definition_body :=
            eₜ ;
        |} ;

  compose_comp :
    ∃ defₛ eₜ,
    progₛ !! func1 = Some defₛ ∧
    compose_expr_comp func1 func2 compose_func defₛ.(data_definition_body) eₜ ∧
    progₜ !! compose_func =
      Some {|
        data_definition_annot :=
          defₛ.(data_definition_annot) ;
        data_definition_body :=
          eₜ ;
      |} ;
}.
#[global] Arguments compose : clear implicits.
