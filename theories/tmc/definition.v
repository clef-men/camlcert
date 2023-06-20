From simuliris Require Import
  prelude.
From simuliris.language Require Export
  syntax.
From simuliris.language Require Import
  notations.

Implicit Types func func_dps : function.
Implicit Types v vₛ vₜ : val.
Implicit Types e eₛ eₜ : expr.
Implicit Types prog progₛ progₜ : program.
Implicit Types ξ : gmap function function.

Inductive tmc_dir ξ : expr → expr → Prop :=
  | tmc_dir_val v :
      tmc_dir ξ
        #v
        #v
  | tmc_dir_var x :
      tmc_dir ξ
        $x
        $x
  | tmc_dir_let eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ
        (let: eₛ1 in eₛ2)
        (let: eₜ1 in eₜ2)
  | tmc_dir_call eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ
        (eₛ1 eₛ2)
        (eₜ1 eₜ2)
  | tmc_dir_unop op eₛ eₜ :
      tmc_dir ξ eₛ eₜ →
      tmc_dir ξ
        (Unop op eₛ)
        (Unop op eₜ)
  | tmc_dir_binop op eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ
        (Binop op eₛ1 eₛ2)
        (Binop op eₜ1 eₜ2)
  | tmc_dir_if eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      tmc_dir ξ eₛ0 eₜ0 →
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ
        (if: eₛ0 then eₛ1 else eₛ2)
        (if: eₜ0 then eₜ1 else eₜ2)
  | tmc_dir_constr constr eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ
        (&constr eₛ1 eₛ2)
        (&constr eₜ1 eₜ2)
  | tmc_dir_constr_dps_1 constr eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dps ξ $0 𝟚 eₛ2.[ren (+1)] eₜ2 →
      tmc_dir ξ
        (&constr eₛ1 eₛ2)
        (let: &constr eₜ1 #() in eₜ2 ;; $0)
  | tmc_dir_constr_dps_2 constr eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dps ξ $0 𝟙 eₛ1.[ren (+1)] eₜ1 →
      tmc_dir ξ
        (&constr eₛ1 eₛ2)
        (let: &constr #() eₜ2 in eₜ1 ;; $0)
  | tmc_dir_constr_det constr eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ
        (&&constr eₛ1 eₛ2)
        (&&constr eₜ1 eₜ2)
  | tmc_dir_load eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ
        (![eₛ2] eₛ1)
        (![eₜ2] eₜ1)
  | tmc_dir_store eₛ1 eₛ2 eₛ3 eₜ1 eₜ2 eₜ3 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ eₛ3 eₜ3 →
      tmc_dir ξ
        (eₛ1 <-[eₛ2]- eₛ3)
        (eₜ1 <-[eₜ2]- eₜ3)
with tmc_dps ξ : expr → expr → expr → expr → Prop :=
  | tmc_dps_base dst idx eₛ eₜ :
      tmc_dir ξ eₛ eₜ →
      tmc_dps ξ dst idx
        eₛ
        (dst <-[idx]- eₜ)
  | tmc_dps_let dst idx eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dps ξ dst.[ren (+1)] idx.[ren (+1)] eₛ2 eₜ2 →
      tmc_dps ξ dst idx
        (let: eₛ1 in eₛ2)
        (let: eₜ1 in eₜ2)
  | tmc_dps_call dst idx func func_dps eₛ eₜ eₜ' :
      ξ !! func = Some func_dps →
      tmc_dir ξ eₛ eₜ →
      eₜ' = (let: eₜ in func_dps (dst.[ren (+1)], idx.[ren (+1)], $0))%E →
      tmc_dps ξ dst idx
        (func eₛ)
        eₜ'
  | tmc_dps_if dst idx eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      tmc_dir ξ eₛ0 eₜ0 →
      tmc_dps ξ dst idx eₛ1 eₜ1 →
      tmc_dps ξ dst idx eₛ2 eₜ2 →
      tmc_dps ξ dst idx
        (if: eₛ0 then eₛ1 else eₛ2)
        (if: eₜ0 then eₜ1 else eₜ2)
  | tmc_dps_constr_1 dst idx constr eₛ1 eₛ2 eₜ1 eₜ2 eₜ :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dps ξ $0 𝟚 eₛ2.[ren (+1)] eₜ2 →
      eₜ = (let: &constr eₜ1 #() in dst.[ren (+1)] <-[idx.[ren (+1)]]- $0 ;; eₜ2)%E →
      tmc_dps ξ dst idx
        (&constr eₛ1 eₛ2)
        eₜ
  | tmc_dps_constr_2 dst idx constr eₛ1 eₛ2 eₜ1 eₜ2 eₜ :
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dps ξ $0 𝟙 eₛ1.[ren (+1)] eₜ1 →
      eₜ = (let: &constr #() eₜ2 in dst.[ren (+1)] <-[idx.[ren (+1)]]- $0 ;; eₜ1)%E →
      tmc_dps ξ dst idx
        (&constr eₛ1 eₛ2)
        eₜ.

Scheme tmc_dir_dps_ind := Minimality for tmc_dir Sort Prop
with tmc_dps_dir_ind := Minimality for tmc_dps Sort Prop.
Combined Scheme tmc_ind from tmc_dir_dps_ind, tmc_dps_dir_ind.

Create HintDb tmc.

#[export] Hint Constructors tmc_dir : tmc.
#[export] Hint Constructors tmc_dps : tmc.

Record tmc {progₛ progₜ} := {
  tmc_ξ : gmap function function ;

  tmc_ξ_fresh :
    map_Forall (λ _ func_dps, func_dps ∉ dom progₛ) tmc_ξ ;
  tmc_ξ_inj func1 func2 func_dps :
    tmc_ξ !! func1 = Some func_dps →
    tmc_ξ !! func2 = Some func_dps →
    func1 = func2 ;

  tmc_dirs func eₛ :
    progₛ !! func = Some eₛ →
      ∃ eₜ,
      progₜ !! func = Some eₜ ∧
      tmc_dir tmc_ξ eₛ eₜ ;

  tmc_dpss func func_dps eₛ :
    progₛ !! func = Some eₛ →
    tmc_ξ !! func = Some func_dps →
      ∃ eₜ,
      progₜ !! func_dps = Some (let: ![𝟙] $0 in let: ![𝟚] $0 in let: ![𝟙] $1 in let: ![𝟚] $3 in eₜ)%E ∧
      tmc_dps tmc_ξ $1 $2 eₛ eₜ ;
}.
#[global] Arguments tmc : clear implicits.
