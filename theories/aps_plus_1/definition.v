From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  syntax.
From camlcert.data_lang Require Import
  notations.
From camlcert Require Import
  options.

Implicit Types n : Z.
Implicit Types func func_aps : data_function.
Implicit Types annot : data_annotation.
Implicit Types v vₛ vₜ : data_val.
Implicit Types e eₛ eₜ : data_expr.
Implicit Types prog progₛ progₜ : data_program.

Definition aps_plus_mapping :=
  gmap data_function data_function.

Section aps_plus_expr.
  Context (ξ : aps_plus_mapping).

  Inductive aps_plus_expr_dir : data_expr → data_expr → Prop :=
    | aps_plus_expr_dir_val v :
        aps_plus_expr_dir
          v
          v
    | aps_plus_expr_dir_var x :
        aps_plus_expr_dir
          $x
          $x
    | aps_plus_expr_dir_let eₛ1 eₛ2 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_dir eₛ2 eₜ2 →
        aps_plus_expr_dir
          (let: eₛ1 in eₛ2)
          (let: eₜ1 in eₜ2)
    | aps_plus_expr_dir_call eₛ1 eₛ2 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_dir eₛ2 eₜ2 →
        aps_plus_expr_dir
          (eₛ1 eₛ2)
          (eₜ1 eₜ2)
    | aps_plus_expr_dir_unop op eₛ eₜ :
        aps_plus_expr_dir eₛ eₜ →
        aps_plus_expr_dir
          (DataUnop op eₛ)
          (DataUnop op eₜ)
    | aps_plus_expr_dir_binop op eₛ1 eₛ2 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_dir eₛ2 eₜ2 →
        aps_plus_expr_dir
          (DataBinop op eₛ1 eₛ2)
          (DataBinop op eₜ1 eₜ2)
    | aps_plus_expr_dir_plus_1 n eₛ eₜ :
        aps_plus_expr_aps n eₛ eₜ →
        aps_plus_expr_dir
          (n + eₛ)
          eₜ
    | aps_plus_expr_dir_plus_2 n eₛ eₜ :
        aps_plus_expr_aps n eₛ eₜ →
        aps_plus_expr_dir
          (eₛ + n)
          eₜ
    | aps_plus_expr_dir_binop_det op eₛ1 eₛ2 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_dir eₛ2 eₜ2 →
        aps_plus_expr_dir
          (DataBinopDet op eₛ1 eₛ2)
          (DataBinopDet op eₜ1 eₜ2)
    | aps_plus_expr_dir_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ0 eₜ0 →
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_dir eₛ2 eₜ2 →
        aps_plus_expr_dir
          (if: eₛ0 then eₛ1 else eₛ2)
          (if: eₜ0 then eₜ1 else eₜ2)
    | aps_plus_expr_dir_block tag eₛ1 eₛ2 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_dir eₛ2 eₜ2 →
        aps_plus_expr_dir
          (&tag eₛ1 eₛ2)
          (&tag eₜ1 eₜ2)
    | aps_plus_expr_dir_block_det tag eₛ1 eₛ2 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_dir eₛ2 eₜ2 →
        aps_plus_expr_dir
          (&&tag eₛ1 eₛ2)
          (&&tag eₜ1 eₜ2)
    | aps_plus_expr_dir_load eₛ1 eₛ2 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_dir eₛ2 eₜ2 →
        aps_plus_expr_dir
          (![eₛ2] eₛ1)
          (![eₜ2] eₜ1)
    | aps_plus_expr_dir_store eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_dir eₛ2 eₜ2 →
        aps_plus_expr_dir eₛ3 eₜ3 →
        aps_plus_expr_dir
          (eₛ1 <-[eₛ2]- eₛ3)
          (eₜ1 <-[eₜ2]- eₜ3)
  with aps_plus_expr_aps : data_expr → data_expr → data_expr → Prop :=
    | aps_plus_expr_aps_base acc eₛ eₜ :
        aps_plus_expr_dir eₛ eₜ →
        aps_plus_expr_aps acc
          eₛ
          (acc + eₜ)
    | aps_plus_expr_aps_let acc eₛ1 eₛ2 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ1 eₜ1 →
        aps_plus_expr_aps acc.[ren (+1)] eₛ2 eₜ2 →
        aps_plus_expr_aps acc
          (let: eₛ1 in eₛ2)
          (let: eₜ1 in eₜ2)
    | aps_plus_expr_aps_call acc annot func eₛ func_aps eₜ eₜ' :
        ξ !! func = Some func_aps →
        aps_plus_expr_dir eₛ eₜ →
        eₜ' = (let: eₜ in (DataFunc func_aps annot) (acc.[ren (+1)], $0))%data_expr →
        aps_plus_expr_aps acc
          ((DataFunc func annot) eₛ)
          eₜ'
    | aps_plus_expr_aps_plus_1 acc n eₛ eₜ :
        aps_plus_expr_aps $0 eₛ.[ren (+1)] eₜ →
        aps_plus_expr_aps acc
          (n + eₛ)
          (let: acc + n in eₜ)
    | aps_plus_expr_aps_plus_2 acc n eₛ eₜ :
        aps_plus_expr_aps $0 eₛ.[ren (+1)] eₜ →
        aps_plus_expr_aps acc
          (eₛ + n)
          (let: acc + n in eₜ)
    | aps_plus_expr_aps_if acc eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
        aps_plus_expr_dir eₛ0 eₜ0 →
        aps_plus_expr_aps acc eₛ1 eₜ1 →
        aps_plus_expr_aps acc eₛ2 eₜ2 →
        aps_plus_expr_aps acc
          (if: eₛ0 then eₛ1 else eₛ2)
          (if: eₜ0 then eₜ1 else eₜ2).
End aps_plus_expr.

Scheme aps_plus_expr_dir_aps_ind :=
  Minimality for aps_plus_expr_dir Sort Prop
with aps_plus_expr_aps_dir_ind :=
  Minimality for aps_plus_expr_aps Sort Prop.
Combined Scheme aps_plus_expr_ind from
  aps_plus_expr_dir_aps_ind,
  aps_plus_expr_aps_dir_ind.

Create HintDb aps_plus.

#[global] Hint Constructors aps_plus_expr_dir : aps_plus.
#[global] Hint Constructors aps_plus_expr_aps : aps_plus.

Record aps_plus {progₛ progₜ} := {
  aps_plus_ξ : gmap data_function data_function ;

  aps_plus_ξ_dom :
    dom aps_plus_ξ ⊆ dom progₛ ;
  aps_plus_dom :
    dom progₜ = dom progₛ ∪ map_img aps_plus_ξ ;

  aps_plus_dir func defₛ :
    progₛ !! func = Some defₛ →
      ∃ eₜ,
      aps_plus_expr_dir aps_plus_ξ defₛ.(data_definition_body) eₜ ∧
      progₜ !! func =
        Some (
          rec: defₛ.(data_definition_annot) :=
            eₜ
        )%data_def ;

  aps_plus_aps func defₛ func_aps :
    progₛ !! func = Some defₛ →
    aps_plus_ξ !! func = Some func_aps →
      ∃ eₜ,
      aps_plus_expr_aps aps_plus_ξ $1 defₛ.(data_definition_body) eₜ ∧
      progₜ !! func_aps =
        Some (
          rec: defₛ.(data_definition_annot) :=
            let: ![𝟙] $0 in
            let: ![𝟚] $1 in
            eₜ
        )%data_def ;
}.
#[global] Arguments aps_plus : clear implicits.
