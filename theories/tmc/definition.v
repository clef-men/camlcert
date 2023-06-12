From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
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
      tmc_dps ξ $0.(2) eₛ2.[ren (+1)] eₜ2 →
      tmc_dir ξ
        (&constr eₛ1 eₛ2)
        (let: &constr eₜ1 #() in eₜ2 ;; $0)
  | tmc_dir_constr_dps_2 constr eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dps ξ $0.(1) eₛ1.[ren (+1)] eₜ1 →
      tmc_dir ξ
        (&constr eₛ1 eₛ2)
        (let: &constr #() eₜ2 in eₜ1 ;; $0)
  | tmc_dir_constr_det constr eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ
        (&&constr eₛ1 eₛ2)
        (&&constr eₜ1 eₜ2)
  | tmc_dir_load eₛ eₜ :
      tmc_dir ξ eₛ eₜ →
      tmc_dir ξ
        !eₛ
        !eₜ
  | tmc_dir_store eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dir ξ
        (eₛ1 <- eₛ2)
        (eₜ1 <- eₜ2)
with tmc_dps ξ : expr → expr → expr → Prop :=
  | tmc_dps_base dst eₛ eₜ :
      tmc_dir ξ eₛ eₜ →
      tmc_dps ξ dst
        eₛ
        (dst <- eₜ)
  | tmc_dps_let dst eₛ1 eₛ2 eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dps ξ dst.[ren (+1)] eₛ2 eₜ2 →
      tmc_dps ξ dst
        (let: eₛ1 in eₛ2)
        (let: eₜ1 in eₜ2)
  | tmc_dps_call dst func func_dps eₛ eₜ :
      ξ !! func = Some func_dps →
      tmc_dir ξ eₛ eₜ →
      tmc_dps ξ dst
        (func eₛ)
        (func_dps (dst, eₜ))%E
  | tmc_dps_if dst eₛ0 eₛ1 eₛ2 eₜ0 eₜ1 eₜ2 :
      tmc_dir ξ eₛ0 eₜ0 →
      tmc_dps ξ dst eₛ1 eₜ1 →
      tmc_dps ξ dst eₛ2 eₜ2 →
      tmc_dps ξ dst
        (if: eₛ0 then eₛ1 else eₛ2)
        (if: eₜ0 then eₜ1 else eₜ2)
  | tmc_dps_constr_1 dst constr eₛ1 eₛ2 eₜ eₜ1 eₜ2 :
      tmc_dir ξ eₛ1 eₜ1 →
      tmc_dps ξ $0.(2) eₛ2.[ren (+1)] eₜ2 →
      eₜ = (let: &constr eₜ1 #() in dst.[ren (+1)] <- $0 ;; eₜ2)%E →
      tmc_dps ξ dst
        (&constr eₛ1 eₛ2)
        eₜ
  | tmc_dps_constr_2 dst constr eₛ1 eₛ2 eₜ eₜ1 eₜ2 :
      tmc_dir ξ eₛ2 eₜ2 →
      tmc_dps ξ $0.(1) eₛ1.[ren (+1)] eₜ1 →
      eₜ = (let: &constr #() eₜ2 in dst.[ren (+1)] <- $0 ;; eₜ1)%E →
      tmc_dps ξ dst
        (&constr eₛ1 eₛ2)
        eₜ.

Scheme tmc_dir_dps_ind := Minimality for tmc_dir Sort Prop
with tmc_dps_dir_ind := Minimality for tmc_dps Sort Prop.
Combined Scheme tmc_ind from tmc_dir_dps_ind, tmc_dps_dir_ind.

Create HintDb tmc.

#[export] Hint Constructors tmc_dir : tmc.
#[export] Hint Constructors tmc_dps : tmc.

Lemma tmc_dir_refl ξ e :
  tmc_dir ξ e e.
Proof.
  induction e; eauto with tmc.
Qed.
#[export] Hint Resolve tmc_dir_refl : tmc.

Lemma tmc_subst ξ :
  ( ∀ eₛ eₜ,
    tmc_dir ξ eₛ eₜ →
    ∀ eₛ' eₜ' ς,
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    tmc_dir ξ eₛ' eₜ'
  ) ∧ (
    ∀ dst eₛ eₜ,
    tmc_dps ξ dst eₛ eₜ →
    ∀ dst' eₛ' eₜ' ς,
    dst' = dst.[ς] →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    tmc_dps ξ dst' eₛ' eₜ'
  ).
Proof.
  apply tmc_ind; solve
  [ intros; simplify; eauto with tmc
  | intros * ? ? ? IHdps **; simplify;
    econstructor; try naive_solver; first eapply IHdps with (up ς); autosubst
  ].
Qed.
Lemma tmc_dir_subst ξ ς eₛ eₛ' eₜ eₜ' :
  tmc_dir ξ eₛ eₜ →
  eₛ' = eₛ.[ς] →
  eₜ' = eₜ.[ς] →
  tmc_dir ξ eₛ' eₜ'.
Proof.
  eauto using (proj1 (tmc_subst ξ)).
Qed.
#[export] Hint Resolve tmc_dir_subst : tmc.
Lemma tmc_dps_subst ξ ς dst dst' eₛ eₛ' eₜ eₜ' :
  tmc_dps ξ dst eₛ eₜ →
  dst' = dst.[ς] →
  eₛ' = eₛ.[ς] →
  eₜ' = eₜ.[ς] →
  tmc_dps ξ dst' eₛ' eₜ'.
Proof.
  eauto using (proj2 (tmc_subst ξ)).
Qed.
#[export] Hint Resolve tmc_dps_subst : tmc.

Record tmc progₛ progₜ := {
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
      progₜ !! func_dps = Some (let: FST $0 in let: SND $1 in eₜ)%E ∧
      tmc_dps tmc_ξ $1 eₛ eₜ ;
}.
