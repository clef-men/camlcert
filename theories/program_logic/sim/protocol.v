From iris.bi Require Import
  bi.

From simuliris Require Import
  prelude.
From simuliris.program_logic Require Export
  ectx_language.

Section bi.
  Context (PROP : bi).
  Context (Λₛ Λₜ : ectx_language).

  Notation expr_relation :=
    (expr Λₛ → expr Λₜ → PROP).
  Notation expr_relation_O :=
    (expr_O Λₛ -d> expr_O Λₜ -d> PROP).

  Definition sim_protocol :=
    expr_relation → expr_relation.
  Definition sim_protocol_O :=
    (expr_relation_O → expr_relation_O).

  #[global] Instance sim_protocol_ne (X : sim_protocol_O) n :
    NonExpansive X →
    Proper ((≡{n}≡) ==> (=) ==> (=) ==> (≡{n}≡)) X.
  Proof.
    intros HX Φ1 Φ2 HΦ eₛ1 eₛ2 -> eₜ1 eₜ2 ->.
    apply HX. done.
  Qed.

  #[global] Instance sim_protocol_bottom : Bottom sim_protocol := (
    λ _ _ _,
      False
  )%I.
  #[global] Instance sim_protocol_meet : Meet sim_protocol := (
    λ X1 X2 Φ eₛ eₜ,
      X1 Φ eₛ eₜ ∨ X2 Φ eₛ eₜ
  )%I.
  #[global] Instance sim_protocol_join : Join sim_protocol := (
    λ X1 X2 Φ eₛ eₜ,
      X1 Φ eₛ eₜ ∧ X2 Φ eₛ eₜ
  )%I.
End bi.
