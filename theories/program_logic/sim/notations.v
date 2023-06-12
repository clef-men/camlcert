From simuliris Require Import
  prelude.
From simuliris.program_logic Require Export
  sim.definition.

Notation "'SIM' progₛ ; eₛ ≳ progₜ ; eₜ [[ X ] ] {{ Φ } }" := (
  sim progₛ progₜ X Φ%I eₛ eₜ
) (
  at level 20,
  progₛ, eₛ, progₜ, eₜ, X, Φ at level 200,
  format "'[hv' SIM  progₛ ;  eₛ  ≳  progₜ ;  eₜ  [[  X  ] ]  {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' progₛ ; eₛ ≳ progₜ ; eₜ {{ Φ } }" := (
  SIM progₛ; eₛ ≳ progₜ; eₜ [[ ⊥ ]] {{ Φ }}
)%I (
  at level 20,
  progₛ, eₛ, progₜ, eₜ, Φ at level 200,
  format "'[hv' SIM  progₛ ;  eₛ  ≳  progₜ ;  eₜ  {{  '/  ' '[' Φ ']'  '/' } } ']'"
) : bi_scope.
Notation "'SIM' progₛ ; eₛ ≳ progₜ ; eₜ [[ X ] ] [[ Φ ] ]" := (
  simv progₛ progₜ X Φ%I eₛ eₜ
) (
  at level 20,
  progₛ, eₛ, progₜ, eₜ, X, Φ at level 200,
  format "'[hv' SIM  progₛ ;  eₛ  ≳  progₜ ;  eₜ  [[  X  ] ]  [[  '/  ' '[' Φ ']'  '/' ] ] ']'"
) : bi_scope.
Notation "'SIM' progₛ ; eₛ ≳ progₜ ; eₜ [[ Φ ] ]" := (
  SIM progₛ; eₛ ≳ progₜ; eₜ [[ ⊥ ]] [[ Φ ]]
)%I (
  at level 20,
  progₛ, eₛ, progₜ, eₜ, Φ at level 200,
  format "'[hv' SIM  progₛ ;  eₛ  ≳  progₜ ;  eₜ  [[  '/  ' '[' Φ ']'  '/' ] ] ']'"
) : bi_scope.

Notation "'SIM' progₛ ; eₛ ≳ progₜ ; eₜ [[ X ] ] {{ Φ } }" := (
  ⊢ SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}
) : stdpp_scope.
Notation "'SIM' progₛ ; eₛ ≳ progₜ ; eₜ {{ Φ } }" := (
  ⊢ SIM progₛ; eₛ ≳ progₜ; eₜ {{ Φ }}
) : stdpp_scope.
Notation "'SIM' progₛ ; eₛ ≳ progₜ ; eₜ [[ X ] ] [[ Φ ] ]" := (
  ⊢ SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]
) : stdpp_scope.
Notation "'SIM' progₛ ; eₛ ≳ progₜ ; eₜ [[ Φ ] ]" := (
  ⊢ SIM progₛ; eₛ ≳ progₜ; eₜ [[ Φ ]]
) : stdpp_scope.
