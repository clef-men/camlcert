From iris.proofmode Require Import
  coq_tactics
  reduction.

From simuliris Require Import
  prelude.
From simuliris.base_logic Require Export
  lib.cupd.proofmode.
From simuliris.program_logic Require Export
  sim.rules.
From simuliris.program_logic Require Import
  sim.notations.

Section sim_state.
  Context `{!BiBUpd PROP, !BiAffine PROP}.
  Context `{sim_state : !SimState PROP Λₛ Λₜ}.
  Context (progₛ : program Λₛ) (progₜ : program Λₜ).
  Context (X : sim_protocol PROP Λₛ Λₜ).

  Section sim.
    #[global] Instance frame_sim p R eₛ eₜ Φ1 Φ2 :
      (∀ eₛ eₜ, Frame p R (Φ1 eₛ eₜ) (Φ2 eₛ eₜ)) →
      Frame p R
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ1 }})
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ2 }}).
    Proof.
      rewrite /Frame sim_frame_l.
      iIntros "%HR Hsim".
      iApply (sim_mono with "[] Hsim"). iIntros "%eₛ' %eₜ'". iApply HR.
    Qed.

    #[global] Instance elim_modal_cupd_sim p P eₛ eₜ Φ :
      ElimModal True p false (|++> P) P
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }})
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "_ (HP & Hsim)".
      iApply cupd_sim. iMod "HP". iModIntro. iApply ("Hsim" with "HP").
    Qed.
    #[global] Instance elim_modal_bupd_sim p P eₛ eₜ Φ :
      ElimModal True p false (|==> P) P
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }})
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "_ (HP & Hsim)".
      iApply bupd_sim. iMod "HP". iModIntro. iApply ("Hsim" with "HP").
    Qed.

    #[global] Instance add_modal_cupd_sim P eₛ eₜ Φ :
      AddModal (|++> P) P (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite /AddModal.
      iIntros "(HP & Hsim)".
      iApply cupd_sim. iMod "HP". iApply ("Hsim" with "HP").
    Qed.
    #[global] Instance add_modal_bupd_sim P eₛ eₜ Φ :
      AddModal (|==> P) P (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite /AddModal.
      iIntros "(HP & Hsim)".
      iApply bupd_sim. iMod "HP". iApply ("Hsim" with "HP").
    Qed.

    Lemma tac_sim_eval eₛ eₛ' eₜ eₜ' Φ Δ :
      (∀ (eₛ'' := eₛ'), eₛ = eₛ'') →
      (∀ (eₜ'' := eₜ'), eₜ = eₜ'') →
      envs_entails Δ (SIM progₛ; eₛ' ≳ progₜ; eₜ' [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      intros -> ->. done.
    Qed.

    Lemma tac_cupd_sim eₛ eₜ Φ Δ :
      envs_entails Δ (|++> SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply cupd_sim.
    Qed.
    Lemma tac_bupd_sim eₛ eₜ Φ Δ :
      envs_entails Δ (|==> SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply bupd_sim.
    Qed.

    Lemma tac_sim_cupd eₛ eₜ Φ Δ :
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }}) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply sim_cupd.
    Qed.
    Lemma tac_sim_bupd eₛ eₜ Φ Δ :
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }}) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply sim_bupd.
    Qed.

    Lemma tac_sim_post eₛ eₜ Φ Δ :
      envs_entails Δ (Φ eₛ eₜ) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iIntros. iApply sim_post. done.
    Qed.

    Lemma tac_sim_bind Kₛ fₛ eₛ Kₜ fₜ eₜ Φ Δ :
      fₛ = (λ eₛ, Kₛ @@ eₛ) →
      fₜ = (λ eₜ, Kₜ @@ eₜ) →
      envs_entails Δ (
        SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ λ eₛ' eₜ',
          SIM progₛ; fₛ eₛ' ≳ progₜ; fₜ eₜ' [[ X ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM progₛ; Kₛ @@ eₛ ≳ progₜ; Kₜ @@ eₜ [[ X ]] {{ Φ }}
      ).
    Proof.
      rewrite envs_entails_unseal -sim_bind => -> -> -> //.
    Qed.
    Lemma tac_sim_bindₛ K f eₛ eₜ Φ Δ :
      f = (λ eₛ, K @@ eₛ) →
      envs_entails Δ (
        SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ λ eₛ' eₜ',
          SIM progₛ; f eₛ' ≳ progₜ; eₜ' [[ X ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM progₛ; K @@ eₛ ≳ progₜ; eₜ [[ X ]] {{ Φ }}
      ).
    Proof.
      rewrite envs_entails_unseal -sim_bindₛ => -> -> //.
    Qed.
    Lemma tac_sim_bindₜ eₛ K f eₜ Φ Δ :
      f = (λ eₜ, K @@ eₜ) →
      envs_entails Δ (
        SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] {{ λ eₛ' eₜ',
          SIM progₛ; eₛ' ≳ progₜ; f eₜ' [[ X ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM progₛ; eₛ ≳ progₜ; K @@ eₜ [[ X ]] {{ Φ }}
      ).
    Proof.
      rewrite envs_entails_unseal -sim_bindₜ => -> -> //.
    Qed.

    Lemma tac_sim_pure_execₛ ϕ n K eₛ1 eₛ2 eₜ Φ Δ :
      PureExec progₛ ϕ n eₛ1 eₛ2 →
      ϕ →
      envs_entails Δ (SIM progₛ; K @@ eₛ2 ≳ progₜ; eₜ [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM progₛ; K @@ eₛ1 ≳ progₜ; eₜ [[ X ]] {{ Φ }}).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      rewrite envs_entails_unseal => ? ? ->.
      eapply sim_pure_stepsₛ, rtc_nsteps_2, pure_exec; done.
    Qed.
    Lemma tac_sim_pure_execₜ ϕ n eₛ K eₜ1 eₜ2 Φ Δ :
      PureExec progₜ ϕ n eₜ1 eₜ2 →
      ϕ →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; K @@ eₜ2 [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; K @@ eₜ1 [[ X ]] {{ Φ }}).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      rewrite envs_entails_unseal => ? ? ->.
      eapply sim_pure_stepsₜ, rtc_nsteps_2, pure_exec; done.
    Qed.
  End sim.

  Section simv.
    #[global] Instance frame_simv p R eₛ eₜ Φ1 Φ2 :
      (∀ eₛ eₜ, Frame p R (Φ1 eₛ eₜ) (Φ2 eₛ eₜ)) →
      Frame p R
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ1 ]])
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ2 ]]).
    Proof.
      rewrite /Frame simv_frame_l.
      iIntros "%HR Hsim".
      iApply (simv_mono with "[] Hsim"). iIntros "%eₛ' %eₜ'". iApply HR.
    Qed.

    #[global] Instance elim_modal_cupd_simv p P eₛ eₜ Φ :
      ElimModal True p false (|++> P) P
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]])
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "_ (HP & Hsim)".
      iApply cupd_simv. iMod "HP". iModIntro. iApply ("Hsim" with "HP").
    Qed.
    #[global] Instance elim_modal_bupd_simv p P eₛ eₜ Φ :
      ElimModal True p false (|==> P) P
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]])
        (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "_ (HP & Hsim)".
      iApply bupd_simv. iMod "HP". iModIntro. iApply ("Hsim" with "HP").
    Qed.

    #[global] Instance add_modal_cupd_simv P eₛ eₜ Φ :
      AddModal (|++> P) P (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite /AddModal.
      iIntros "(HP & Hsim)".
      iApply cupd_simv. iMod "HP". iApply ("Hsim" with "HP").
    Qed.
    #[global] Instance add_modal_bupd_simv P eₛ eₜ Φ :
      AddModal (|==> P) P (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite /AddModal.
      iIntros "(HP & Hsim)".
      iApply bupd_simv. iMod "HP". iApply ("Hsim" with "HP").
    Qed.

    Lemma tac_simv_eval eₛ eₛ' eₜ eₜ' Φ Δ :
      (∀ (eₛ'' := eₛ'), eₛ = eₛ'') →
      (∀ (eₜ'' := eₜ'), eₜ = eₜ'') →
      envs_entails Δ (SIM progₛ; eₛ' ≳ progₜ; eₜ' [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      intros -> ->. done.
    Qed.

    Lemma tac_cupd_simv eₛ eₜ Φ Δ :
      envs_entails Δ (|++> SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply cupd_simv.
    Qed.
    Lemma tac_bupd_simv eₛ eₜ Φ Δ :
      envs_entails Δ (|==> SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply bupd_simv.
    Qed.

    Lemma tac_simv_cupd eₛ eₜ Φ Δ :
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ λ eₛ eₜ, |++> Φ eₛ eₜ ]]) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply simv_cupd.
    Qed.
    Lemma tac_simv_bupd eₛ eₜ Φ Δ :
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ λ eₛ eₜ, |==> Φ eₛ eₜ ]]) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply simv_bupd.
    Qed.

    Lemma tac_simv_strongly_stuck eₛ eₜ Φ Δ :
      IsStronglyStuck progₛ eₛ →
      IsStronglyStuck progₜ eₜ →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal.
      iIntros. iApply simv_strongly_stuck; done.
    Qed.

    Lemma tac_simv_post eₛ vₛ eₜ vₜ Φ Δ :
      eₛ = of_val vₛ →
      eₜ = of_val vₜ →
      envs_entails Δ (Φ vₛ vₜ) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => -> -> ->.
      iIntros. iApply simv_post; done.
    Qed.

    Lemma tac_simv_bind Kₛ fₛ eₛ Kₜ fₜ eₜ Φ Δ :
      fₛ = (λ vₛ, Kₛ @@ vₛ) →
      fₜ = (λ vₜ, Kₜ @@ vₜ) →
      envs_entails Δ (
        SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ λ vₛ vₜ,
          SIM progₛ; fₛ (of_val vₛ) ≳ progₜ; fₜ (of_val vₜ) [[ X ]] [[ Φ ]]
        ]]
      ) →
      envs_entails Δ (
        SIM progₛ; Kₛ @@ eₛ ≳ progₜ; Kₜ @@ eₜ [[ X ]] [[ Φ ]]
      ).
    Proof.
      rewrite envs_entails_unseal -simv_bind => -> -> -> //.
    Qed.
    Lemma tac_simv_bindₛ K f eₛ eₜ Φ Δ :
      f = (λ vₛ, K @@ vₛ) →
      envs_entails Δ (
        SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ λ vₛ vₜ,
          SIM progₛ; f (of_val vₛ) ≳ progₜ; of_val vₜ [[ X ]] [[ Φ ]]
        ]]
      ) →
      envs_entails Δ (
        SIM progₛ; K @@ eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]
      ).
    Proof.
      rewrite envs_entails_unseal -simv_bindₛ => -> -> //.
    Qed.
    Lemma tac_simv_bindₜ eₛ K f eₜ Φ Δ :
      f = (λ eₜ, K @@ eₜ) →
      envs_entails Δ (
        SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ λ vₛ vₜ,
          SIM progₛ; of_val vₛ ≳ progₜ; f (of_val vₜ) [[ X ]] [[ Φ ]]
        ]]
      ) →
      envs_entails Δ (
        SIM progₛ; eₛ ≳ progₜ; K @@ eₜ [[ X ]] [[ Φ ]]
      ).
    Proof.
      rewrite envs_entails_unseal -simv_bindₜ => -> -> //.
    Qed.

    Lemma tac_simv_pure_execₛ ϕ n K eₛ1 eₛ2 eₜ Φ Δ :
      PureExec progₛ ϕ n eₛ1 eₛ2 →
      ϕ →
      envs_entails Δ (SIM progₛ; K @@ eₛ2 ≳ progₜ; eₜ [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM progₛ; K @@ eₛ1 ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      rewrite envs_entails_unseal => ? ? ->.
      eapply simv_pure_stepsₛ, rtc_nsteps_2, pure_exec; done.
    Qed.
    Lemma tac_simv_pure_execₜ ϕ n eₛ K eₜ1 eₜ2 Φ Δ :
      PureExec progₜ ϕ n eₜ1 eₜ2 →
      ϕ →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; K @@ eₜ2 [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; K @@ eₜ1 [[ X ]] [[ Φ ]]).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      rewrite envs_entails_unseal => ? ? ->.
      eapply simv_pure_stepsₜ, rtc_nsteps_2, pure_exec; done.
    Qed.
  End simv.
End sim_state.

Tactic Notation "expr_is_val" open_constr(e) :=
  eunify (of_val _) e.

Tactic Notation "ectx_is_empty" open_constr(K) :=
  let ectx := type of K in
  unshelve unify (empty : ectx) K; [].

Tactic Notation "match_sim" tactic3(tac_fail) tactic3(tac_succ) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (sim ?Φ ?eₛ ?eₜ) =>
      tac_succ Φ eₛ eₜ
  | _ =>
      tac_fail
  end.
Tactic Notation "match_simv" tactic3(tac_fail) tactic3(tac_succ) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (simv ?Φ ?eₛ ?eₜ) =>
      tac_succ Φ eₛ eₜ
  | _ =>
      tac_fail
  end.

Tactic Notation "on_sim" tactic3(tac) :=
  match_sim ltac:(fun _ => fail "not a 'sim'") tac.
Tactic Notation "on_simv" tactic3(tac) :=
  match_simv ltac:(fun _ => fail "not a 'simv'") tac.

Tactic Notation "sim_eval" tactic3(tacₛ) tactic3(tacₜ) :=
  on_sim ltac:(fun _ _ _ =>
    notypeclasses refine (tac_sim_eval _ _ _ _ _ _ _ _ _ _ _ _);
    [ iSolveTC
    | let x := fresh in intros x; tacₛ; unfold x; notypeclasses refine eq_refl
    | let x := fresh in intros x; tacₜ; unfold x; notypeclasses refine eq_refl
    | idtac
    ]
  ).
Tactic Notation "sim_eval" tactic3(tac) :=
  sim_eval ltac:(tac) ltac:(tac).
Tactic Notation "sim_evalₛ" tactic3(tac) :=
  sim_eval ltac:(tac) ltac:(idtac).
Tactic Notation "sim_evalₜ" tactic3(tac) :=
  sim_eval ltac:(idtac) ltac:(tac).

Ltac sim_simpl :=
  sim_eval simpl.
Ltac sim_simplₛ :=
  sim_evalₛ simpl.
Ltac sim_simplₜ :=
  sim_evalₜ simpl.

Ltac sim_cupd_simple :=
  on_sim ltac:(fun _ _ _ =>
    notypeclasses refine (tac_sim_cupd _ _ _ _ _ _ _ _); first iSolveTC
  ).
Ltac sim_cupd :=
  on_sim ltac:(fun Φ _ _ =>
    first
    [ assert (∀ P eₛ eₜ, AddModal (|++> P) P (Φ eₛ eₜ)) as _ by iSolveTC
    | sim_cupd_simple
    ]
  ).
Ltac cupd_sim :=
  on_sim ltac:(fun _ _ _ =>
    notypeclasses refine (tac_cupd_sim _ _ _ _ _ _ _ _); first iSolveTC
  ).

Ltac sim_bupd_simple :=
  on_sim ltac:(fun _ _ _ =>
    notypeclasses refine (tac_sim_bupd _ _ _ _ _ _ _ _); first iSolveTC
  ).
Ltac sim_bupd :=
  on_sim ltac:(fun Φ _ _ =>
    first
    [ assert (∀ P eₛ eₜ, AddModal (|==> P) P (Φ eₛ eₜ)) as _ by iSolveTC
    | sim_bupd_simple
    ]
  ).
Ltac bupd_sim :=
  on_sim ltac:(fun _ _ _ =>
    notypeclasses refine (tac_bupd_sim _ _ _ _ _ _ _ _); first iSolveTC
  ).

Ltac simv_strongly_stuck :=
  on_simv ltac:(fun _ _ _ =>
    notypeclasses refine (tac_simv_strongly_stuck _ _ _ _ _ _ _ _ _);
    iSolveTC
  ).

Ltac sim_post_simple :=
  on_sim ltac:(fun _ _ _ =>
    notypeclasses refine (tac_sim_post _ _ _ _ _ _ _ _); first iSolveTC
  ).
Ltac sim_post :=
  sim_simpl;
  sim_cupd;
  sim_post_simple;
  lazymatch goal with |- envs_entails _ (?Φ ?eₛ ?eₜ) =>
    tryif
      eunify (cupd (sim_post_val _)) Φ;
      expr_is_val eₛ; expr_is_val eₜ
    then (
      iExists _, _; iSplitR; [done | iSplitR; [done |]]
    ) else (
      idtac
    )
  end;
  try done.

Tactic Notation "sim_finish" "with" tactic3(tac) :=
  sim_eval (simpl; rewrite ?fill_empty; tac);
  on_sim ltac:(fun _ eₛ eₜ =>
    tryif expr_is_val eₛ; expr_is_val eₜ then (
      sim_post
    ) else (
      try solve [sim_post]
    )
  );
  pm_prettify.
Tactic Notation "sim_finish" :=
  sim_finish with idtac.

Tactic Notation "sim_bind_coreₛ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    notypeclasses refine (tac_sim_bindₛ _ _ _ K _ _ _ _ _ _ _);
    [ iSolveTC
    | simpl; reflexivity
    | pm_prettify
    ]
  ).
Tactic Notation "sim_bind_coreₜ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    notypeclasses refine (tac_sim_bindₜ _ _ _ _ K _ _ _ _ _ _);
    [ iSolveTC
    | simpl; reflexivity
    | pm_prettify
    ]
  ).
Tactic Notation "sim_bind_core" open_constr(Kₛ) open_constr(Kₜ) :=
  tryif ectx_is_empty Kₛ then (
    sim_bind_coreₜ Kₜ
  ) else (
    tryif ectx_is_empty Kₜ then (
      sim_bind_coreₛ Kₛ
    ) else (
      notypeclasses refine (tac_sim_bind _ _ _ Kₛ _ _ Kₜ _ _ _ _ _ _ _);
      [ iSolveTC
      | simpl; reflexivity
      | simpl; reflexivity
      | pm_prettify
      ]
    )
  ).

Tactic Notation "sim_pure_coreₛ" open_constr(K) "with" tactic3(tac) :=
  notypeclasses refine (tac_sim_pure_execₛ _ _ _ _ _ K _ _ _ _ _ _ _ _);
  [ iSolveTC
  | iSolveTC
  | try done
  | sim_finish with tac
  ].
Tactic Notation "sim_pure_coreₛ" open_constr(K) :=
  sim_pure_coreₛ K with idtac.
Tactic Notation "sim_pure_coreₜ" open_constr(K) "with" tactic3(tac) :=
  notypeclasses refine (tac_sim_pure_execₜ _ _ _ _ _ _ K _ _ _ _ _ _ _);
  [ iSolveTC
  | iSolveTC
  | try done
  | sim_finish with tac
  ].
Tactic Notation "sim_pure_coreₜ" open_constr(K) :=
  sim_pure_coreₜ K with idtac.
