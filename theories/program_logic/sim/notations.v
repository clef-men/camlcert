From simuliris Require Import
  prelude.
From simuliris.program_logic Require Export
  sim.definition.

Notation "'SIM' eₛ ≳ eₜ [[ Χ ] ] {{ Φ } }" := (sim Χ Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ {{ Φ } }" := (sim ⊥ Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ [[ Χ ] ] {{# Φ } }" := (simv Χ Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, Χ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' Χ ']'  '/' ] ]  {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ {{# Φ } }" := (simv ⊥ Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' {{#  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.

Notation "'SIM' eₛ ≳ eₜ [[ Χ ] ] {{ Φ } }" := (⊢ SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }})
: stdpp_scope.
Notation "'SIM' eₛ ≳ eₜ {{ Φ } }" := (⊢ SIM eₛ ≳ eₜ {{ Φ }})
: stdpp_scope.
Notation "'SIM' eₛ ≳ eₜ [[ Χ ] ] {{# Φ } }" := (⊢ SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }})
: stdpp_scope.
Notation "'SIM' eₛ ≳ eₜ {{# Φ } }" := (⊢ SIM eₛ ≳ eₜ {{# Φ }})
: stdpp_scope.
