From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  syntax.
From simuliris.data_lang Require Import
  notations.

Implicit Types func func_dps : data_function.
Implicit Types annot : data_annotation.
Implicit Types v vₛ vₜ : data_val.
Implicit Types e eₛ eₜ : data_expr.
Implicit Types prog progₛ progₜ : data_program.

Definition tmc_mapping :=
  gmap data_function data_function.

Section tmc_expr.
  Context (ξ : tmc_mapping).

  Inductive tmc_expr_dir : data_expr → data_expr → Prop :=
    | tmc_expr_dir_val v :
        tmc_expr_dir
          v
          v
    | tmc_expr_dir_var x :
        tmc_expr_dir
          $x
          $x
    | tmc_expr_dir_let eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dir
          (let: eₛ1 in eₛ2)
          (let: eₜ1 in eₜ2)
    | tmc_expr_dir_call eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dir
          (eₛ1 eₛ2)
          (eₜ1 eₜ2)
    | tmc_expr_dir_unop op eₛ eₜ :
        tmc_expr_dir eₛ eₜ →
        tmc_expr_dir
          (DataUnop op eₛ)
          (DataUnop op eₜ)
    | tmc_expr_dir_binop op eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dir
          (DataBinop op eₛ1 eₛ2)
          (DataBinop op eₜ1 eₜ2)
    | tmc_expr_dir_binop_det op eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dir
          (DataBinopDet op eₛ1 eₛ2)
          (DataBinopDet op eₜ1 eₜ2)
    | tmc_expr_dir_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
        tmc_expr_dir eₛ0 eₜ0 →
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dir
          (if: eₛ0 then eₛ1 else eₛ2)
          (if: eₜ0 then eₜ1 else eₜ2)
    | tmc_expr_dir_block tag eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dir
          (&tag eₛ1 eₛ2)
          (&tag eₜ1 eₜ2)
    | tmc_expr_dir_block_dps_1 tag eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dps $0 𝟚 eₛ2.[ren (+1)] eₜ2 →
        tmc_expr_dir
          (&tag eₛ1 eₛ2)
          (let: &tag eₜ1 #() in eₜ2 ;; $0)
    | tmc_expr_dir_block_dps_2 tag eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dps $0 𝟙 eₛ1.[ren (+1)] eₜ1 →
        tmc_expr_dir
          (&tag eₛ1 eₛ2)
          (let: &tag #() eₜ2 in eₜ1 ;; $0)
    | tmc_expr_dir_block_det tag eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dir
          (&&tag eₛ1 eₛ2)
          (&&tag eₜ1 eₜ2)
    | tmc_expr_dir_load eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dir
          (![eₛ2] eₛ1)
          (![eₜ2] eₜ1)
    | tmc_expr_dir_store eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dir eₛ3 eₜ3 →
        tmc_expr_dir
          (eₛ1 <-[eₛ2]- eₛ3)
          (eₜ1 <-[eₜ2]- eₜ3)
  with tmc_expr_dps : data_expr → data_expr → data_expr → data_expr → Prop :=
    | tmc_expr_dps_base dst idx eₛ eₜ :
        tmc_expr_dir eₛ eₜ →
        tmc_expr_dps dst idx
          eₛ
          (dst <-[idx]- eₜ)
    | tmc_expr_dps_let dst idx eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dps dst.[ren (+1)] idx.[ren (+1)] eₛ2 eₜ2 →
        tmc_expr_dps dst idx
          (let: eₛ1 in eₛ2)
          (let: eₜ1 in eₜ2)
    | tmc_expr_dps_call dst idx func annot eₛ func_dps eₜ eₜ' :
        ξ !! func = Some func_dps →
        tmc_expr_dir eₛ eₜ →
        eₜ' = (let: eₜ in (DataFunc func_dps annot) (dst.[ren (+1)], idx.[ren (+1)], $0))%data_expr →
        tmc_expr_dps dst idx
          ((DataFunc func annot) eₛ)
          eₜ'
    | tmc_expr_dps_if dst idx eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
        tmc_expr_dir eₛ0 eₜ0 →
        tmc_expr_dps dst idx eₛ1 eₜ1 →
        tmc_expr_dps dst idx eₛ2 eₜ2 →
        tmc_expr_dps dst idx
          (if: eₛ0 then eₛ1 else eₛ2)
          (if: eₜ0 then eₜ1 else eₜ2)
    | tmc_expr_dps_block_1 dst idx tag eₛ1 eₛ2 eₜ1 eₜ2 eₜ :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dps $0 𝟚 eₛ2.[ren (+1)] eₜ2 →
        eₜ = (let: &tag eₜ1 #() in dst.[ren (+1)] <-[idx.[ren (+1)]]- $0 ;; eₜ2)%data_expr →
        tmc_expr_dps dst idx
          (&tag eₛ1 eₛ2)
          eₜ
    | tmc_expr_dps_block_2 dst idx tag eₛ1 eₛ2 eₜ1 eₜ2 eₜ :
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dps $0 𝟙 eₛ1.[ren (+1)] eₜ1 →
        eₜ = (let: &tag #() eₜ2 in dst.[ren (+1)] <-[idx.[ren (+1)]]- $0 ;; eₜ1)%data_expr →
        tmc_expr_dps dst idx
          (&tag eₛ1 eₛ2)
          eₜ.
End tmc_expr.

Scheme tmc_expr_dir_dps_ind := Minimality for tmc_expr_dir Sort Prop
with tmc_expr_dps_dir_ind := Minimality for tmc_expr_dps Sort Prop.
Combined Scheme tmc_expr_ind from tmc_expr_dir_dps_ind, tmc_expr_dps_dir_ind.

Create HintDb tmc.

#[global] Hint Constructors tmc_expr_dir : tmc.
#[global] Hint Constructors tmc_expr_dps : tmc.

Record tmc {progₛ progₜ} := {
  tmc_ξ : gmap data_function data_function ;

  tmc_ξ_dom :
    dom tmc_ξ ⊆ dom progₛ ;
  tmc_dom :
    dom progₜ = dom progₛ ∪ map_img tmc_ξ ;

  tmc_dir func defₛ :
    progₛ !! func = Some defₛ →
      ∃ eₜ,
      tmc_expr_dir tmc_ξ defₛ.(data_definition_body) eₜ ∧
      progₜ !! func =
        Some (
          rec: defₛ.(data_definition_annot) :=
            eₜ
        )%data_def ;

  tmc_dps func defₛ func_dps :
    progₛ !! func = Some defₛ →
    tmc_ξ !! func = Some func_dps →
      ∃ eₜ,
      tmc_expr_dps tmc_ξ $1 $2 defₛ.(data_definition_body) eₜ ∧
      progₜ !! func_dps =
        Some (
          rec: defₛ.(data_definition_annot) :=
            let: ![𝟙] $0 in
            let: ![𝟚] $0 in
            let: ![𝟙] $1 in
            let: ![𝟚] $3 in
            eₜ
        )%data_def ;
}.
#[global] Arguments tmc : clear implicits.
