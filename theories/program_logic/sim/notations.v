From simuliris Require Import
  prelude.
From simuliris.program_logic Require Export
  sim.definition.

Notation "'SIM' eₛ ≳ eₜ [[ X ] ] {{ Φ } }" := (sim X Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, X, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' X ']'  '/' ] ]  {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ {{ Φ } }" := (sim ⊥ Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ [[ X ] ] [[ Φ ] ]" := (simv X Φ%I eₛ eₜ)
( at level 20,
  eₛ, eₜ, X, Φ at level 200,
  format "'[hv' SIM  '/  ' '[' eₛ ']'  '/' ≳  '[' eₜ ']'  '/' [[  '/  ' '[' X ']'  '/' ] ]  [[  '/  ' '[' Φ ']'  '/' ] ] ']'"
) : bi_scope.
Notation "'SIM' eₛ ≳ eₜ [[ Φ ] ]" := (simv ⊥ Φ%I eₛ eₜ)
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
