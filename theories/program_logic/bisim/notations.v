From simuliris Require Import
  prelude.
From simuliris.program_logic Require Export
  bisim.definition.

Notation "'BISIM' eₛ ≃ eₜ [[ Χ ] ] {{ Φ } }" := (bisim Χ Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' BISIM  '/  ' '[' eₛ ']'  '/' ≃  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'BISIM' eₛ ≃ eₜ {{ Φ } }" := (bisim ⊥ Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' BISIM  '/  ' '[' eₛ ']'  '/' ≃  '[' eₜ ']'  '/' {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'BISIM' eₛ ≃ eₜ [[ Χ ] ] {{# Φ } }" := (bisimv Χ Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' BISIM  '/  ' '[' eₛ ']'  '/' ≃  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'BISIM' eₛ ≃ eₜ {{# Φ } }" := (bisimv ⊥ Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' BISIM  '/  ' '[' eₛ ']'  '/' ≃  '[' eₜ ']'  '/' {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.

Notation "'BISIM' eₛ ≃ eₜ [[ Χ ] ] {{ Φ } }" := (⊢ BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }})
: stdpp_scope.
Notation "'BISIM' eₛ ≃ eₜ {{ Φ } }" := (⊢ BISIM eₛ ≃ eₜ {{ Φ }})
: stdpp_scope.
Notation "'BISIM' eₛ ≃ eₜ [[ Χ ] ] {{# Φ } }" := (⊢ BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ }})
: stdpp_scope.
Notation "'BISIM' eₛ ≃ eₜ {{# Φ } }" := (⊢ BISIM eₛ ≃ eₜ {{# Φ }})
: stdpp_scope.
