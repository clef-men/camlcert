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

Inductive inline_expr prog : data_expr → data_expr → Prop :=
  | inline_expr_val v :
      inline_expr prog
        #v
        #v
  | inline_expr_var x :
      inline_expr prog
        $x
        $x
  | inline_expr_let eₛ1 eₛ2 eₜ1 eₜ2 :
      inline_expr prog eₛ1 eₜ1 →
      inline_expr prog eₛ2 eₜ2 →
      inline_expr prog
        (let: eₛ1 in eₛ2)
        (let: eₜ1 in eₜ2)
  | inline_expr_call eₛ1 eₛ2 eₜ1 eₜ2 :
      inline_expr prog eₛ1 eₜ1 →
      inline_expr prog eₛ2 eₜ2 →
      inline_expr prog
        (eₛ1 eₛ2)
        (eₜ1 eₜ2)
  | inline_expr_call_inline func annot defₛ e_funcₛ eₛ e_funcₜ eₜ :
      prog !! func = Some defₛ →
      e_funcₛ = defₛ.(data_definition_body) →
      inline_expr prog e_funcₛ e_funcₜ →
      inline_expr prog eₛ eₜ →
      inline_expr prog
        ((DataFunc func annot) eₛ)
        (let: eₜ in e_funcₜ)
  | inline_expr_unop op eₛ eₜ :
      inline_expr prog eₛ eₜ →
      inline_expr prog
        (DataUnop op eₛ)
        (DataUnop op eₜ)
  | inline_expr_binop op eₛ1 eₛ2 eₜ1 eₜ2 :
      inline_expr prog eₛ1 eₜ1 →
      inline_expr prog eₛ2 eₜ2 →
      inline_expr prog
        (DataBinop op eₛ1 eₛ2)
        (DataBinop op eₜ1 eₜ2)
  | inline_expr_binop_det op eₛ1 eₛ2 eₜ1 eₜ2 :
      inline_expr prog eₛ1 eₜ1 →
      inline_expr prog eₛ2 eₜ2 →
      inline_expr prog
        (DataBinopDet op eₛ1 eₛ2)
        (DataBinopDet op eₜ1 eₜ2)
  | inline_expr_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      inline_expr prog eₛ0 eₜ0 →
      inline_expr prog eₛ1 eₜ1 →
      inline_expr prog eₛ2 eₜ2 →
      inline_expr prog
        (if: eₛ0 then eₛ1 else eₛ2)
        (if: eₜ0 then eₜ1 else eₜ2)
  | inline_expr_constr tag eₛ1 eₛ2 eₜ1 eₜ2 :
      inline_expr prog eₛ1 eₜ1 →
      inline_expr prog eₛ2 eₜ2 →
      inline_expr prog
        (&tag eₛ1 eₛ2)
        (&tag eₜ1 eₜ2)
  | inline_expr_constr_det tag eₛ1 eₛ2 eₜ1 eₜ2 :
      inline_expr prog eₛ1 eₜ1 →
      inline_expr prog eₛ2 eₜ2 →
      inline_expr prog
        (&&tag eₛ1 eₛ2)
        (&&tag eₜ1 eₜ2)
  | inline_expr_load eₛ1 eₛ2 eₜ1 eₜ2 :
      inline_expr prog eₛ1 eₜ1 →
      inline_expr prog eₛ2 eₜ2 →
      inline_expr prog
        (![eₛ2] eₛ1)
        (![eₜ2] eₜ1)
  | inline_expr_store eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      inline_expr prog eₛ1 eₜ1 →
      inline_expr prog eₛ2 eₜ2 →
      inline_expr prog eₛ3 eₜ3 →
      inline_expr prog
        (eₛ1 <-[eₛ2]- eₛ3)
        (eₜ1 <-[eₜ2]- eₜ3).

Create HintDb inline.

#[global] Hint Constructors inline_expr : inline.

Record inline {progₛ progₜ} := {
  inline_dom :
    dom progₜ = dom progₛ ;

  inline_transform func defₛ eₛ :
    progₛ !! func = Some defₛ →
    eₛ = defₛ.(data_definition_body) →
      ∃ eₜ,
      inline_expr progₛ eₛ eₜ ∧
      progₜ !! func =
        Some {|
          data_definition_annot :=
            defₛ.(data_definition_annot) ;
          data_definition_body :=
            eₜ ;
        |} ;
}.
#[global] Arguments inline : clear implicits.
