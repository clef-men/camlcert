From iris.proofmode Require Import
  class_instances_updates.
From iris.proofmode Require Export
  proofmode.

From simuliris Require Import
  prelude.
From simuliris.base_logic Require Export
  lib.cupd.rules.

Section bi_cupd.
  Context `{BiCUpd PROP}.
  Implicit Types P Q R : PROP.

  #[local] Tactic Notation "solve" "with" constr(H) :=
    apply (H _ cupd_bi_bupd).

  #[global] Instance from_assumption_cupd p P Q :
    FromAssumption p P Q →
    KnownRFromAssumption p P (|++> Q).
  Proof.
    solve with @from_assumption_bupd.
  Qed.

  #[global] Instance from_pure_cupd a P ϕ :
    FromPure a P ϕ →
    FromPure a (|++> P) ϕ.
  Proof.
    solve with @from_pure_bupd.
  Qed.

  #[global] Instance into_wand_cupd p q R P Q :
    IntoWand false false R P Q →
    IntoWand p q (|++> R) (|++> P) (|++> Q).
  Proof.
    solve with @into_wand_bupd.
  Qed.

  #[global] Instance into_wand_cupd_persistent p q R P Q :
    IntoWand false q R P Q →
    IntoWand p q (|++> R) P (|++> Q).
  Proof.
    solve with @into_wand_bupd_persistent.
  Qed.

  #[global] Instance into_wand_cupd_args p q R P Q :
    IntoWand p false R P Q →
    IntoWand' p q R (|++> P) (|++> Q).
  Proof.
    solve with @into_wand_bupd_args.
  Qed.

  #[global] Instance from_sep_cupd P Q1 Q2 :
    FromSep P Q1 Q2 →
    FromSep (|++> P) (|++> Q1) (|++> Q2).
  Proof.
    solve with @from_sep_bupd.
  Qed.

  #[global] Instance from_or_cupd P Q1 Q2 :
    FromOr P Q1 Q2 →
    FromOr (|++> P) (|++> Q1) (|++> Q2).
  Proof.
    solve with @from_or_bupd.
  Qed.

  #[global] Instance into_and_cupd P Q1 Q2 :
    IntoAnd false P Q1 Q2 →
    IntoAnd false (|++> P) (|++> Q1) (|++> Q2).
  Proof.
    solve with @into_and_bupd.
  Qed.

  #[global] Instance from_exist_cupd {X} P (Φ : X → PROP) :
    FromExist P Φ →
    FromExist (|++> P) (λ x, |++> Φ x)%I.
  Proof.
    solve with @from_exist_bupd.
  Qed.

  #[global] Instance into_forall_cupd {X} P (Φ : X → PROP) :
    IntoForall P Φ →
    IntoForall (|++> P) (λ x, |++> Φ x)%I.
  Proof.
    solve with @into_forall_bupd.
  Qed.

  #[global] Instance is_except_0_cupd P :
    IsExcept0 P →
    IsExcept0 (|++> P).
  Proof.
    solve with @is_except_0_bupd.
  Qed.

  #[global] Instance from_modal_cupd P :
    FromModal True modality_id (|++> P) (|++> P) P.
  Proof.
    solve with @from_modal_bupd.
  Qed.

  #[global] Instance elim_modal_cupd p P Q :
    ElimModal True p false (|++> P) P (|++> Q) (|++> Q).
  Proof.
    solve with @elim_modal_bupd.
  Qed.

  #[global] Instance elim_modal_bupd_cupd p P Q :
    ElimModal True p false (|==> P) P (|++> Q) (|++> Q) | 10.
  Proof.
    rewrite
      /ElimModal bi.intuitionistically_if_elim
      bupd_cupd cupd_frame_r bi.wand_elim_r.
    by setoid_rewrite cupd_trans.
  Qed.

  #[global] Instance add_modal_cupd P Q :
    AddModal (|++> P) P (|++> Q).
  Proof.
    solve with @add_modal_bupd.
  Qed.

  #[global] Instance frame_cupd p R P Q :
    Frame p R P Q →
    Frame p R (|++> P) (|++> Q)
  | 2.
  Proof.
    rewrite /Frame => <-. rewrite cupd_frame_l //.
  Qed.
End bi_cupd.
