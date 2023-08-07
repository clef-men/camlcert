From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  bisim.notations
  rbisim.definition.

Notation "'BISIM' eₛ ≅ eₜ [[ Χ ] ] {{ Φ } }" := (rbisim Χ Φ%I eₛ%data_expr eₜ%data_expr)
( at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' BISIM  '/  ' '[' eₛ ']'  '/' ≅  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'BISIM' eₛ ≅ eₜ {{ Φ } }" := (rbisim ⊥ Φ%I eₛ%data_expr eₜ%data_expr)%I
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' BISIM  '/  ' '[' eₛ ']'  '/' ≅  '[' eₜ ']'  '/' {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'BISIM' eₛ ≅ eₜ [[ Χ ] ] {{# Φ } }" := (rbisimv Χ Φ%I eₛ%data_expr eₜ%data_expr)
( at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' BISIM  '/  ' '[' eₛ ']'  '/' ≅  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'BISIM' eₛ ≅ eₜ {{# Φ } }" := (rbisimv ⊥ Φ%I eₛ%data_expr eₜ%data_expr)%I
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' BISIM  '/  ' '[' eₛ ']'  '/' ≅  '[' eₜ ']'  '/' {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.

Notation "'BISIM' eₛ ≅ eₜ [[ Χ ] ] {{ Φ } }" := (⊢ BISIM eₛ ≅ eₜ [[ Χ ]] {{ Φ }})
: stdpp_scope.
Notation "'BISIM' eₛ ≅ eₜ {{ Φ } }" := (⊢ BISIM eₛ ≅ eₜ {{ Φ }})
: stdpp_scope.
Notation "'BISIM' eₛ ≅ eₜ [[ Χ ] ] {{# Φ } }" := (⊢ BISIM eₛ ≅ eₜ [[ Χ ]] {{# Φ }})
: stdpp_scope.
Notation "'BISIM' eₛ ≅ eₜ {{# Φ } }" := (⊢ BISIM eₛ ≅ eₜ {{# Φ }})
: stdpp_scope.

Notation "{{{ P } } } eₛ ≅ eₜ [[ Χ ] ] {{{ Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    BISIM eₛ ≅ eₜ [[ Χ ]] {{ Ψ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≅  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{{  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ≅ eₜ {{{ Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    BISIM eₛ ≅ eₜ {{ Ψ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≅  '[' eₜ ']'  '/' {{{  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ≅ eₜ [[ Χ ] ] {{{# Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    BISIM eₛ ≅ eₜ [[ Χ ]] {{# Ψ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≅  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{{#  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ≅ eₜ {{{# Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    BISIM eₛ ≅ eₜ {{# Ψ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≅  '[' eₜ ']'  '/' {{{#  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.

Notation "{{{ P } } } eₛ ≅ eₜ [[ Χ ] ] {{{ Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    BISIM eₛ ≅ eₜ [[ Χ ]] {{ Ψ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ≅ eₜ {{{ Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    BISIM eₛ ≅ eₜ {{ Ψ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ≅ eₜ [[ Χ ] ] {{{# Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    BISIM eₛ ≅ eₜ [[ Χ ]] {{# Ψ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ≅ eₜ {{{# Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ vₛ vₜ, Φ vₛ vₜ -∗ Ψ vₛ vₜ) -∗
    BISIM eₛ ≅ eₜ {{# Ψ }}
) : stdpp_scope.
