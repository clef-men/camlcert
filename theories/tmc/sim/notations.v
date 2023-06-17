From simuliris Require Import
  prelude.
From simuliris.language Require Export
  notations.
From simuliris.tmc Require Export
  sim.definition.

Notation "l ↦ₛ{ dq } v" := (mapstoₛ (locₛ := loc) (valₛ := val) l dq v%V)
( at level 20,
  format "l  ↦ₛ{ dq }  v"
) : bi_scope.
Notation "l ↦ₛ□ v" := (l ↦ₛ{DfracDiscarded} v)%I
( at level 20,
  format "l  ↦ₛ□  v"
) : bi_scope.
Notation "l ↦ₛ{# q } v" := (l ↦ₛ{DfracOwn q} v)%I
( at level 20,
  format "l  ↦ₛ{# q }  v"
) : bi_scope.
Notation "l ↦ₛ v" := (l ↦ₛ{#1} v)%I
( at level 20,
  format "l  ↦ₛ  v"
) : bi_scope.

Notation "l ↦ₜ{ dq } v" := (mapstoₜ (locₜ := loc) (valₜ := val) l dq v%V)
( at level 20,
  format "l  ↦ₜ{ dq }  v"
) : bi_scope.
Notation "l ↦ₜ□ v" := (l ↦ₜ{DfracDiscarded} v)%I
( at level 20,
  format "l  ↦ₜ□  v"
) : bi_scope.
Notation "l ↦ₜ{# q } v" := (l ↦ₜ{DfracOwn q} v)%I
( at level 20,
  format "l  ↦ₜ{# q }  v"
) : bi_scope.
Notation "l ↦ₜ v" := (l ↦ₜ{#1} v)%I
( at level 20,
  format "l  ↦ₜ  v"
) : bi_scope.

Notation "'SIM' eₛ ≳ eₜ [[ X ] ] {{ Φ } }" := (sim X Φ%I eₛ%E eₜ%E)
( at level 20,
  eₛ, eₜ, X, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' X ']'  '/' ] ]  {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ {{ Φ } }" := (SIM eₛ ≳ eₜ [[ ⊥ ]] {{ Φ }})%I
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ [[ X ] ] [[ Φ ] ]" := (simv X Φ%I eₛ%E eₜ%E)
( at level 20,
  eₛ, eₜ, X, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' X ']'  '/' ] ]  [[  '/  ' '[' Φ ']'  '/' ] ] ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ [[ Φ ] ]" := (SIM eₛ ≳ eₜ [[ ⊥ ]] [[ Φ ]])%I
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' Φ ']'  '/' ] ] ']'"
) : bi_scope.

Notation "'SIM' eₛ ≳ eₜ [[ X ] ] {{ Φ } }" := (⊢ SIM eₛ ≳ eₜ [[ X ]] {{ Φ }})
: stdpp_scope.
Notation "'SIM' eₛ ≳ eₜ {{ Φ } }" := (⊢ SIM eₛ ≳ eₜ {{ Φ }})
: stdpp_scope.
Notation "'SIM' eₛ ≳ eₜ [[ X ] ] [[ Φ ] ]" := (⊢ SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]])
: stdpp_scope.
Notation "'SIM' eₛ ≳ eₜ [[ Φ ] ]" := (⊢ SIM eₛ ≳ eₜ [[ Φ ]])
: stdpp_scope.

Notation "{{{ P } } } eₛ ≳ eₜ [[ X ] ] {{{ Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Ψ eₛ eₜ -∗ Φ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' X ']'  '/' ] ]  {{{  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "{{{ P } } } eₛ ≳ eₜ {{{ Φ } } }" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Ψ eₛ eₜ -∗ Φ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ {{ Φ }}
  )
)%I (
  at level 20,
  format "'[hv' {{{  '/  ' '[' P ']'  '/' } } }  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' {{{  '/  ' '[' Φ ']'  '/' } } } ']'"
) : bi_scope.
Notation "[[[ P ] ] ] eₛ ≳ eₜ [[ X ] ] [[[ Φ ] ] ]" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Ψ eₛ eₜ -∗ Φ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]
  )
)%I (
  at level 20,
  format "'[hv' [[[  '/  ' '[' P ']'  '/' ] ] ]  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' X ']'  '/' ] ]  [[[  '/  ' '[' Φ ']'  '/' ] ] ] ']'"
) : bi_scope.
Notation "[[[ P ] ] ] eₛ ≳ eₜ [[[ Φ ] ] ]" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Ψ eₛ eₜ -∗ Φ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ [[ Φ ]]
  )
)%I (
  at level 20,
  format "'[hv' [[[  '/  ' '[' P ']'  '/' ] ] ]  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[[  '/  ' '[' Φ ']'  '/' ] ] ] ']'"
) : bi_scope.

Notation "{{{ P } } } eₛ ≳ eₜ [[ X ] ] {{{ Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Ψ eₛ eₜ -∗ Φ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}
) : stdpp_scope.
Notation "{{{ P } } } eₛ ≳ eₜ {{{ Φ } } }" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Ψ eₛ eₜ -∗ Φ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ {{ Φ }}
) : stdpp_scope.
Notation "[[[ P ] ] ] eₛ ≳ eₜ [[ X ] ] [[[ Φ ] ] ]" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Ψ eₛ eₜ -∗ Φ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]
) : stdpp_scope.
Notation "[[[ P ] ] ] eₛ ≳ eₜ [[[ Φ ] ] ]" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Ψ eₛ eₜ -∗ Φ eₛ eₜ) -∗
    SIM eₛ ≳ eₜ [[ Φ ]]
) : stdpp_scope.
