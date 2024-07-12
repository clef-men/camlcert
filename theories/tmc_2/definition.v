From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  syntax.
From camlcert.data_lang Require Import
  notations.
From camlcert Require Import
  options.

Implicit Types func func_dps : data_function.
Implicit Types annot : data_annotation.
Implicit Types v vₛ vₜ : data_val.
Implicit Types e eₛ eₜ : data_expr.
Implicit Types prog progₛ progₜ : data_program.

Definition tmc_mapping :=
  gmap data_function data_function.

Inductive tmc_side :=
  | TmcLeft
  | TmcRight.

Coercion tmc_side_to_index side :=
  match side with
  | TmcLeft =>
      𝟙
  | TmcRight =>
      𝟚
  end.
Definition tmc_side_invert side :=
  match side with
  | TmcLeft =>
      TmcRight
  | TmcRight =>
      TmcLeft
  end.

Record tmc_ctxi := TmcCtxi {
  tmc_ctxi_tag : data_tag ;
  tmc_ctxi_side : tmc_side ;
  tmc_ctxi_expr : data_expr ;
}.
Add Printing Constructor tmc_ctxi.
Implicit Types c : tmc_ctxi.

#[global] Instance tmc_ctxi_fill : Fill tmc_ctxi data_expr :=
  Build_Fill (λ c e,
    match c.(tmc_ctxi_side) with
    | TmcLeft =>
        &c.(tmc_ctxi_tag) e c.(tmc_ctxi_expr)
    | TmcRight =>
        &c.(tmc_ctxi_tag) c.(tmc_ctxi_expr) e
    end
  )%data_expr.
#[global] Instance tmc_ctxi_hsubst : HSubst data_expr tmc_ctxi :=
  λ ς c,
    TmcCtxi c.(tmc_ctxi_tag) c.(tmc_ctxi_side) c.(tmc_ctxi_expr).[ς].

Definition tmc_ctx :=
  list tmc_ctxi.
Implicit Types C : tmc_ctx.

#[global] Instance tmc_ctx_fill : Fill tmc_ctx data_expr :=
  Build_Fill (λ C e,
    foldl (λ e c, c @@ e) e C
  ).
#[global] Instance tmc_ctx_hsubst : HSubst data_expr tmc_ctx :=
  λ ς C,
    (hsubst ς) <$> C.

Record tmc_rctxi := TmcRctxi {
  tmc_rctxi_tag : data_tag ;
  tmc_rctxi_side : tmc_side ;
  tmc_rctxi_val : data_val ;
}.
Add Printing Constructor tmc_rctxi.

Coercion tmc_rctxi_to_ctxi (c : tmc_rctxi) :=
  TmcCtxi c.(tmc_rctxi_tag) c.(tmc_rctxi_side) c.(tmc_rctxi_val).

Definition tmc_rctx :=
  list tmc_rctxi.

Definition tmc_rctx_to_ctx : tmc_rctx → tmc_ctx :=
  fmap tmc_rctxi_to_ctxi.
Coercion tmc_rctx_to_ctx : tmc_rctx >-> tmc_ctx.

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
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dps $0 𝟙 [] eₛ1.[ren (+1)] eₜ1 →
        tmc_expr_dir
          (&tag eₛ1 eₛ2)
          (let: &tag #() eₜ2 in eₜ1 ;; $0)
    | tmc_expr_dir_block_dps_2 tag eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dps $0 𝟚 [] eₛ2.[ren (+1)] eₜ2 →
        tmc_expr_dir
          (&tag eₛ1 eₛ2)
          (let: &tag eₜ1 #() in eₜ2 ;; $0)
    | tmc_expr_dir_block_dps_12 tag eₛ1 eₛ2 eₜ1 eₜ2 eₜ :
        tmc_expr_dps $0 𝟙 [] eₛ1.[ren (+1)] eₜ1 →
        tmc_expr_dps $0 𝟚 [] eₛ2.[ren (+1)] eₜ2 →
        eₜ = (let: &tag #() #() in eₜ1 ;; eₜ2 ;; $0)%data_expr →
        tmc_expr_dir
          (&tag eₛ1 eₛ2)
          eₜ
    | tmc_expr_dir_block_dps_21 tag eₛ1 eₛ2 eₜ1 eₜ2 eₜ :
        tmc_expr_dps $0 𝟙 [] eₛ1.[ren (+1)] eₜ1 →
        tmc_expr_dps $0 𝟚 [] eₛ2.[ren (+1)] eₜ2 →
        eₜ = (let: &tag #() #() in eₜ2 ;; eₜ1 ;; $0)%data_expr →
        tmc_expr_dir
          (&tag eₛ1 eₛ2)
          eₜ
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
          (eₛ1 <-[eₛ2] eₛ3)
          (eₜ1 <-[eₜ2] eₜ3)
  with tmc_expr_dps : data_expr → data_expr → tmc_ctx → data_expr → data_expr → Prop :=
    | tmc_expr_dps_base dst idx C eₛ eₜ eₜ' :
        tmc_expr_dir eₛ eₜ →
        eₜ' = C @@ eₜ →
        tmc_expr_dps dst idx C
          eₛ
          (dst <-[idx] eₜ')
    | tmc_expr_dps_let dst idx C eₛ1 eₛ2 eₜ1 eₜ2 :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dps dst.[ren (+1)] idx.[ren (+1)] C.|[ren (+1)] eₛ2 eₜ2 →
        tmc_expr_dps dst idx C
          (let: eₛ1 in eₛ2)
          (let: eₜ1 in eₜ2)
    | tmc_expr_dps_call dst idx func annot eₛ func_dps eₜ eₜ' :
        ξ !! func = Some func_dps →
        tmc_expr_dir eₛ eₜ →
        eₜ' = (let: eₜ in (DataFunc func_dps annot) (dst.[ren (+1)], idx.[ren (+1)], $0))%data_expr →
        tmc_expr_dps dst idx []
          ((DataFunc func annot) eₛ)
          eₜ'
    | tmc_expr_dps_if dst idx C eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
        tmc_expr_dir eₛ0 eₜ0 →
        tmc_expr_dps dst idx C eₛ1 eₜ1 →
        tmc_expr_dps dst idx C eₛ2 eₜ2 →
        tmc_expr_dps dst idx C
          (if: eₛ0 then eₛ1 else eₛ2)
          (if: eₜ0 then eₜ1 else eₜ2)
    | tmc_expr_dps_block_1 dst idx C tag eₛ1 eₛ2 eₜ1 eₜ2 eₜ :
        tmc_expr_dir eₛ2 eₜ2 →
        tmc_expr_dps dst.[ren (+1)] idx.[ren (+1)] (TmcCtxi tag TmcLeft $0 :: C.|[ren (+1)]) eₛ1.[ren (+1)] eₜ1 →
        eₜ = (let: eₜ2 in eₜ1)%data_expr →
        tmc_expr_dps dst idx C
          (&tag eₛ1 eₛ2)
          eₜ
    | tmc_expr_dps_block_2 dst idx C tag eₛ1 eₛ2 eₜ1 eₜ2 eₜ :
        tmc_expr_dir eₛ1 eₜ1 →
        tmc_expr_dps dst.[ren (+1)] idx.[ren (+1)] (TmcCtxi tag TmcRight $0 :: C.|[ren (+1)]) eₛ2.[ren (+1)] eₜ2 →
        eₜ = (let: eₜ1 in eₜ2)%data_expr →
        tmc_expr_dps dst idx C
          (&tag eₛ1 eₛ2)
          eₜ
    | tmc_expr_dps_reify dst idx c C eₛ eₜ eₜ' :
        tmc_expr_dps $0 c.(tmc_ctxi_side) [] eₛ.[ren (+1)] eₜ →
        eₜ' = (let: c @@ #() in dst.[ren (+1)] <-[idx.[ren (+1)]] (C.|[ren (+1)] @@ $0) ;; eₜ)%data_expr →
        tmc_expr_dps dst idx (c :: C)
          eₛ
          eₜ'.
End tmc_expr.

Scheme tmc_expr_dir_dps_ind :=
  Minimality for tmc_expr_dir Sort Prop
with tmc_expr_dps_dir_ind :=
  Minimality for tmc_expr_dps Sort Prop.
Combined Scheme tmc_expr_ind from
  tmc_expr_dir_dps_ind,
  tmc_expr_dps_dir_ind.

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
      tmc_expr_dps tmc_ξ $1 $2 [] defₛ.(data_definition_body) eₜ ∧
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
