From simuliris Require Import
  prelude.
From simuliris.tmc Require Export
  sim.notations.
From simuliris.tmc Require Export
  csim.definition.

Notation "'SIM' eₛ ⩾ eₜ [[ X ] ] [[ Φ ] ]" := (csimv X Φ%I eₛ%lambda_expr eₜ%lambda_expr)
( at level 20,
  eₛ, eₜ, X, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' [[  '/  ' '[' X ']'  '/' ] ]  [[  '/  ' '[' Φ ']'  '/' ] ] ']'"
) : bi_scope.
Notation "'SIM' eₛ ⩾ eₜ [[ Φ ] ]" := (csimv ⊥ Φ%I eₛ%lambda_expr eₜ%lambda_expr)%I
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' [[  '/  ' '[' Φ ']'  '/' ] ] ']'"
) : bi_scope.

Notation "'SIM' eₛ ⩾ eₜ [[ X ] ] [[ Φ ] ]" := (⊢ SIM eₛ ⩾ eₜ [[ X ]] [[ Φ ]])
: stdpp_scope.
Notation "'SIM' eₛ ⩾ eₜ [[ Φ ] ]" := (⊢ SIM eₛ ⩾ eₜ [[ Φ ]])
: stdpp_scope.

Notation "[[[ P ] ] ] eₛ ⩾ eₜ [[ X ] ] [[[ Φ ] ] ]" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ⩾ eₜ [[ X ]] [[ Ψ ]]
  )
)%I (
  at level 20,
  format "'[hv' [[[  '/  ' '[' P ']'  '/' ] ] ]  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' [[  '/  ' '[' X ']'  '/' ] ]  [[[  '/  ' '[' Φ ']'  '/' ] ] ] ']'"
) : bi_scope.
Notation "[[[ P ] ] ] eₛ ⩾ eₜ [[[ Φ ] ] ]" := (
  □ (
    ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ⩾ eₜ [[ Ψ ]]
  )
)%I (
  at level 20,
  format "'[hv' [[[  '/  ' '[' P ']'  '/' ] ] ]  '/  ' '[' eₛ ']'  '/' ⩾  '[' eₜ ']'  '/' [[[  '/  ' '[' Φ ']'  '/' ] ] ] ']'"
) : bi_scope.

Notation "[[[ P ] ] ] eₛ ⩾ eₜ [[ X ] ] [[[ Φ ] ] ]" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ⩾ eₜ [[ X ]] [[ Ψ ]]
) : stdpp_scope.
Notation "[[[ P ] ] ] eₛ ⩾ eₜ [[[ Φ ] ] ]" := (
  ⊢ ∀ Ψ,
    P%I -∗
    (∀ eₛ eₜ, Φ eₛ eₜ -∗ Ψ eₛ eₜ) -∗
    SIM eₛ ⩾ eₜ [[ Ψ ]]
) : stdpp_scope.
