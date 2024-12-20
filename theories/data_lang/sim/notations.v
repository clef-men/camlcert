From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  notations
  sim.definition.
From camlcert Require Import
  options.

Notation "l ↦ₛ{ dq } v" := (
  mapstoₛ (locₛ := loc) (valₛ := data_val) l dq v%data_val
)(at level 20,
  format "l  ↦ₛ{ dq }  v"
) : bi_scope.
Notation "l ↦ₛ□ v" :=
  (l ↦ₛ{DfracDiscarded} v)%I
( at level 20,
  format "l  ↦ₛ□  v"
) : bi_scope.
Notation "l ↦ₛ{# q } v" :=
  (l ↦ₛ{DfracOwn q} v)%I
( at level 20,
  format "l  ↦ₛ{# q }  v"
) : bi_scope.
Notation "l ↦ₛ v" :=
  (l ↦ₛ{#1} v)%I
( at level 20,
  format "l  ↦ₛ  v"
) : bi_scope.

Notation "l ↦ₜ{ dq } v" := (
  mapstoₜ (locₜ := loc) (valₜ := data_val) l dq v%data_val
)(at level 20,
  format "l  ↦ₜ{ dq }  v"
) : bi_scope.
Notation "l ↦ₜ□ v" :=
  (l ↦ₜ{DfracDiscarded} v)%I
( at level 20,
  format "l  ↦ₜ□  v"
) : bi_scope.
Notation "l ↦ₜ{# q } v" :=
  (l ↦ₜ{DfracOwn q} v)%I
( at level 20,
  format "l  ↦ₜ{# q }  v"
) : bi_scope.
Notation "l ↦ₜ v" :=
  (l ↦ₜ{#1} v)%I
( at level 20,
  format "l  ↦ₜ  v"
) : bi_scope.

Notation "'SIM' eₛ ≳ eₜ [[ Χ ] ] {{ Φ } }" := (
  sim Χ Φ%I eₛ%data_expr eₜ%data_expr
)(at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ {{ Φ } }" :=
  (sim ⊥ Φ%I eₛ%data_expr eₜ%data_expr)%I
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ [[ Χ ] ] {{# Φ } }" := (
  simv Χ Φ%I eₛ%data_expr eₜ%data_expr
)(at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ {{# Φ } }" :=
  (simv ⊥ Φ%I eₛ%data_expr eₜ%data_expr)%I
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.

Notation "'SIM' eₛ ≳ eₜ [[ Χ ] ] {{ Φ } }" := (
  ⊢ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}
) : stdpp_scope.
Notation "'SIM' eₛ ≳ eₜ {{ Φ } }" := (
  ⊢ SIM eₛ ≳ eₜ {{ Φ }}
) : stdpp_scope.
Notation "'SIM' eₛ ≳ eₜ [[ Χ ] ] {{# Φ } }" := (
  ⊢ SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}
) : stdpp_scope.
Notation "'SIM' eₛ ≳ eₜ {{# Φ } }" := (
  ⊢ SIM eₛ ≳ eₜ {{# Φ }}
) : stdpp_scope.

Notation "{{{ P } } } eₛ ≳ eₜ [[ Χ ] ] {{{ Φ } } }" :=
  ( □ (
      ∀ Ψ,
      P%I -∗
      (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{ Ψ }}
    )
  )%I
( at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{{  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ≳ eₜ {{{ Φ } } }" :=
  ( □ (
      ∀ Ψ,
      P%I -∗
      (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
      SIM eₛ ≳ eₜ {{ Ψ }}
    )
  )%I
( at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' {{{  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ≳ eₜ [[ Χ ] ] {{{# Φ } } }" :=
  ( □ (
      ∀ Ψ,
      P%I -∗
      (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
      SIM eₛ ≳ eₜ [[ Χ ]] {{# Ψ }}
    )
  )%I
( at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{{#  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ≳ eₜ {{{# Φ } } }" :=
  ( □ (
      ∀ Ψ,
      P%I -∗
      (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
      SIM eₛ ≳ eₜ {{# Ψ }}
    )
  )%I
( at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' {{{#  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.

Notation "{{{ P } } } eₛ ≳ eₜ [[ Χ ] ] {{{ Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ [[ Χ ]] {{ Ψ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ≳ eₜ {{{ Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ {{ Ψ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ≳ eₜ [[ Χ ] ] {{{# Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    SIM eₛ ≳ eₜ [[ Χ ]] {{# Ψ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ≳ eₜ {{{# Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    SIM eₛ ≳ eₜ {{# Ψ }}
) : stdpp_scope.
