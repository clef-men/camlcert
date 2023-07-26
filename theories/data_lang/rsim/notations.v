From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  sim.notations
  rsim.definition.

Notation "'SIM' eₛ ⩾ eₜ [[ Χ ] ] {{ Φ } }" := (rsim Χ Φ%I eₛ%data_expr eₜ%data_expr)
( at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ⩾ eₜ {{ Φ } }" := (rsim ⊥ Φ%I eₛ%data_expr eₜ%data_expr)%I
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ⩾ eₜ [[ Χ ] ] {{# Φ } }" := (rsimv Χ Φ%I eₛ%data_expr eₜ%data_expr)
( at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ⩾ eₜ {{# Φ } }" := (rsimv ⊥ Φ%I eₛ%data_expr eₜ%data_expr)%I
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.

Notation "'SIM' eₛ ⩾ eₜ [[ Χ ] ] {{ Φ } }" := (⊢ SIM eₛ ⩾ eₜ [[ Χ ]] {{ Φ }})
: stdpp_scope.
Notation "'SIM' eₛ ⩾ eₜ {{ Φ } }" := (⊢ SIM eₛ ⩾ eₜ {{ Φ }})
: stdpp_scope.
Notation "'SIM' eₛ ⩾ eₜ [[ Χ ] ] {{# Φ } }" := (⊢ SIM eₛ ⩾ eₜ [[ Χ ]] {{# Φ }})
: stdpp_scope.
Notation "'SIM' eₛ ⩾ eₜ {{# Φ } }" := (⊢ SIM eₛ ⩾ eₜ {{# Φ }})
: stdpp_scope.

Notation "{{{ P } } } eₛ ⩾ eₜ [[ Χ ] ] {{{ Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ⩾ eₜ [[ Χ ]] {{ Ψ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{{  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ⩾ eₜ {{{ Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ⩾ eₜ {{ Ψ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' {{{  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ⩾ eₜ [[ Χ ] ] {{{# Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    SIM eₛ ⩾ eₜ [[ Χ ]] {{# Ψ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{{#  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ⩾ eₜ {{{# Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    SIM eₛ ⩾ eₜ {{# Ψ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' {{{#  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.

Notation "{{{ P } } } eₛ ⩾ eₜ [[ Χ ] ] {{{ Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ⩾ eₜ [[ Χ ]] {{ Ψ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ⩾ eₜ {{{ Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ⩾ eₜ {{ Ψ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ⩾ eₜ [[ Χ ] ] {{{# Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    SIM eₛ ⩾ eₜ [[ Χ ]] {{# Ψ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ⩾ eₜ {{{# Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    SIM eₛ ⩾ eₜ {{# Ψ }}
) : stdpp_scope.
