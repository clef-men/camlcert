From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  syntax.
From camlcert.data_lang Require Import
  notations.
From camlcert Require Import
  options.

Implicit Types func : data_function.
Implicit Types annot : data_annotation.
Implicit Types v vₛ vₜ : data_val.
Implicit Types e eₛ eₜ : data_expr.
Implicit Types prog progₛ progₜ : data_program.

Section inline_expr.
  Context prog.

  Inductive inline_expr : data_expr → data_expr → Prop :=
    | inline_expr_val v :
        inline_expr
          v
          v
    | inline_expr_var x :
        inline_expr
          $x
          $x
    | inline_expr_let eₛ1 eₛ2 eₜ1 eₜ2 :
        inline_expr eₛ1 eₜ1 →
        inline_expr eₛ2 eₜ2 →
        inline_expr
          (let: eₛ1 in eₛ2)
          (let: eₜ1 in eₜ2)
    | inline_expr_call eₛ1 eₛ2 eₜ1 eₜ2 :
        inline_expr eₛ1 eₜ1 →
        inline_expr eₛ2 eₜ2 →
        inline_expr
          (eₛ1 eₛ2)
          (eₜ1 eₜ2)
    | inline_expr_call_inline func annot defₛ e_funcₛ eₛ e_funcₜ eₜ :
        prog !! func = Some defₛ →
        e_funcₛ = defₛ.(data_definition_body) →
        inline_expr e_funcₛ e_funcₜ →
        inline_expr eₛ eₜ →
        inline_expr
          ((DataFunc func annot) eₛ)
          (let: eₜ in e_funcₜ)
    | inline_expr_unop op eₛ eₜ :
        inline_expr eₛ eₜ →
        inline_expr
          (DataUnop op eₛ)
          (DataUnop op eₜ)
    | inline_expr_binop op eₛ1 eₛ2 eₜ1 eₜ2 :
        inline_expr eₛ1 eₜ1 →
        inline_expr eₛ2 eₜ2 →
        inline_expr
          (DataBinop op eₛ1 eₛ2)
          (DataBinop op eₜ1 eₜ2)
    | inline_expr_binop_det op eₛ1 eₛ2 eₜ1 eₜ2 :
        inline_expr eₛ1 eₜ1 →
        inline_expr eₛ2 eₜ2 →
        inline_expr
          (DataBinopDet op eₛ1 eₛ2)
          (DataBinopDet op eₜ1 eₜ2)
    | inline_expr_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
        inline_expr eₛ0 eₜ0 →
        inline_expr eₛ1 eₜ1 →
        inline_expr eₛ2 eₜ2 →
        inline_expr
          (if: eₛ0 then eₛ1 else eₛ2)
          (if: eₜ0 then eₜ1 else eₜ2)
    | inline_expr_block tag eₛ1 eₛ2 eₜ1 eₜ2 :
        inline_expr eₛ1 eₜ1 →
        inline_expr eₛ2 eₜ2 →
        inline_expr
          (&tag eₛ1 eₛ2)
          (&tag eₜ1 eₜ2)
    | inline_expr_block_det tag eₛ1 eₛ2 eₜ1 eₜ2 :
        inline_expr eₛ1 eₜ1 →
        inline_expr eₛ2 eₜ2 →
        inline_expr
          (&&tag eₛ1 eₛ2)
          (&&tag eₜ1 eₜ2)
    | inline_expr_load eₛ1 eₛ2 eₜ1 eₜ2 :
        inline_expr eₛ1 eₜ1 →
        inline_expr eₛ2 eₜ2 →
        inline_expr
          (![eₛ2] eₛ1)
          (![eₜ2] eₜ1)
    | inline_expr_store eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
        inline_expr eₛ1 eₜ1 →
        inline_expr eₛ2 eₜ2 →
        inline_expr eₛ3 eₜ3 →
        inline_expr
          (eₛ1 <-[eₛ2] eₛ3)
          (eₜ1 <-[eₜ2] eₜ3).
End inline_expr.

Create HintDb inline.

#[global] Hint Constructors inline_expr : inline.

Record inline {progₛ progₜ} := {
  inline_dom :
    dom progₜ = dom progₛ ;

  inline_transform func defₛ :
    progₛ !! func = Some defₛ →
      ∃ eₜ,
      inline_expr progₛ defₛ.(data_definition_body) eₜ ∧
      progₜ !! func =
        Some (
          rec: defₛ.(data_definition_annot) :=
            eₜ
        )%data_def ;
}.
#[global] Arguments inline : clear implicits.
