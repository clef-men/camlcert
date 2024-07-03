From iris.bi Require Import
  bi.

From camlcert Require Import
  prelude.
From camlcert.iris.program_logic Require Export
  ectx_language.
From camlcert Require Import
  options.

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

  #[global] Instance sim_protocol_ne (Χ : sim_protocol_O) n :
    NonExpansive Χ →
    Proper ((≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡) ==> (≡{n}≡)) Χ.
  Proof.
    intros HΧ Φ1 Φ2 HΦ eₛ1 eₛ2 ->%leibniz_equiv eₜ1 eₜ2 ->%leibniz_equiv.
    apply HΧ. done.
  Qed.

  #[global] Instance sim_protocol_bottom : Bottom sim_protocol := (
    λ _ _ _,
      False
  )%I.
  #[global] Instance sim_protocol_meet : Meet sim_protocol := (
    λ Χ1 Χ2 Φ eₛ eₜ,
      Χ1 Φ eₛ eₜ ∨ Χ2 Φ eₛ eₜ
  )%I.
  #[global] Instance sim_protocol_join : Join sim_protocol := (
    λ Χ1 Χ2 Φ eₛ eₜ,
      Χ1 Φ eₛ eₜ ∧ Χ2 Φ eₛ eₜ
  )%I.
End bi.
