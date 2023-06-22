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
  Context `{sim_programs : !SimPrograms Λₛ Λₜ}.
  Context `{!BiBUpd PROP, !BiAffine PROP}.
  Context `{sim_state : !SimState PROP Λₛ Λₜ}.
  Context (X : sim_protocol PROP Λₛ Λₜ).

  Section sim.
    #[global] Instance frame_sim p R eₛ eₜ Φ1 Φ2 :
      (∀ eₛ eₜ, Frame p R (Φ1 eₛ eₜ) (Φ2 eₛ eₜ)) →
      Frame p R
        (SIM eₛ ≳ eₜ [[ X ]] {{ Φ1 }})
        (SIM eₛ ≳ eₜ [[ X ]] {{ Φ2 }}).
    Proof.
      rewrite /Frame sim_frame_l.
      iIntros "%HR Hsim".
      iApply (sim_mono with "[] Hsim"). iIntros "%eₛ' %eₜ'". iApply HR.
    Qed.

    #[global] Instance elim_modal_cupd_sim p P eₛ eₜ Φ :
      ElimModal True p false (|++> P) P
        (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }})
        (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "_ (HP & Hsim)".
      iApply cupd_sim. iMod "HP". iModIntro. iApply ("Hsim" with "HP").
    Qed.
    #[global] Instance elim_modal_bupd_sim p P eₛ eₜ Φ :
      ElimModal True p false (|==> P) P
        (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }})
        (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "_ (HP & Hsim)".
      iApply bupd_sim. iMod "HP". iModIntro. iApply ("Hsim" with "HP").
    Qed.

    #[global] Instance add_modal_cupd_sim P eₛ eₜ Φ :
      AddModal (|++> P) P (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite /AddModal.
      iIntros "(HP & Hsim)".
      iApply cupd_sim. iMod "HP". iApply ("Hsim" with "HP").
    Qed.
    #[global] Instance add_modal_bupd_sim P eₛ eₜ Φ :
      AddModal (|==> P) P (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite /AddModal.
      iIntros "(HP & Hsim)".
      iApply bupd_sim. iMod "HP". iApply ("Hsim" with "HP").
    Qed.

    Lemma tac_sim_eval eₛ eₛ' eₜ eₜ' Φ Δ :
      (∀ (eₛ'' := eₛ'), eₛ = eₛ'') →
      (∀ (eₜ'' := eₜ'), eₜ = eₜ'') →
      envs_entails Δ (SIM eₛ' ≳ eₜ' [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      intros -> ->. done.
    Qed.

    Lemma tac_sim_strongly_stuck eₛ eₜ Φ Δ :
      IsStronglyStuck sim_progₛ eₛ →
      IsStronglyStuck sim_progₜ eₜ →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal.
      iIntros. iApply sim_strongly_stuck; done.
    Qed.

    Lemma tac_sim_post eₛ eₜ Φ Δ :
      envs_entails Δ (Φ eₛ eₜ) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iIntros. iApply sim_post. done.
    Qed.

    Lemma tac_cupd_sim eₛ eₜ Φ Δ :
      envs_entails Δ (|++> SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply cupd_sim.
    Qed.
    Lemma tac_bupd_sim eₛ eₜ Φ Δ :
      envs_entails Δ (|==> SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply bupd_sim.
    Qed.

    Lemma tac_sim_cupd eₛ eₜ Φ Δ :
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply sim_cupd.
    Qed.
    Lemma tac_sim_bupd eₛ eₜ Φ Δ :
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply sim_bupd.
    Qed.

    Lemma tac_sim_bind Kₛ fₛ eₛ Kₜ fₜ eₜ Φ Δ :
      fₛ = (λ eₛ, Kₛ @@ eₛ) →
      fₜ = (λ eₜ, Kₜ @@ eₜ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ X ]] {{ λ eₛ' eₜ',
          SIM fₛ eₛ' ≳ fₜ eₜ' [[ X ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ X ]] {{ Φ }}
      ).
    Proof.
      rewrite envs_entails_unseal -sim_bind => -> -> -> //.
    Qed.
    Lemma tac_sim_bindₛ K f eₛ eₜ Φ Δ :
      f = (λ eₛ, K @@ eₛ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ X ]] {{ λ eₛ' eₜ',
          SIM f eₛ' ≳ eₜ' [[ X ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM K @@ eₛ ≳ eₜ [[ X ]] {{ Φ }}
      ).
    Proof.
      rewrite envs_entails_unseal -sim_bindₛ => -> -> //.
    Qed.
    Lemma tac_sim_bindₜ eₛ K f eₜ Φ Δ :
      f = (λ eₜ, K @@ eₜ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ X ]] {{ λ eₛ' eₜ',
          SIM eₛ' ≳ f eₜ' [[ X ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM eₛ ≳ K @@ eₜ [[ X ]] {{ Φ }}
      ).
    Proof.
      rewrite envs_entails_unseal -sim_bindₜ => -> -> //.
    Qed.

    Lemma tac_sim_pure_execₛ ϕ n K eₛ1 eₛ2 eₜ Φ Δ :
      PureExec sim_progₛ ϕ n eₛ1 eₛ2 →
      ϕ →
      envs_entails Δ (SIM K @@ eₛ2 ≳ eₜ [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM K @@ eₛ1 ≳ eₜ [[ X ]] {{ Φ }}).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      rewrite envs_entails_unseal => ? ? ->.
      eapply sim_pure_stepsₛ, rtc_nsteps_2, pure_exec_pure_steps; done.
    Qed.
    Lemma tac_sim_pure_execₜ ϕ n eₛ K eₜ1 eₜ2 Φ Δ :
      PureExec sim_progₜ ϕ n eₜ1 eₜ2 →
      ϕ →
      envs_entails Δ (SIM eₛ ≳ K @@ eₜ2 [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM eₛ ≳ K @@ eₜ1 [[ X ]] {{ Φ }}).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      rewrite envs_entails_unseal => ? ? ->.
      eapply sim_pure_stepsₜ, rtc_nsteps_2, pure_exec_pure_steps; done.
    Qed.
  End sim.

  Section simv.
    #[global] Instance frame_simv p R eₛ eₜ Φ1 Φ2 :
      (∀ eₛ eₜ, Frame p R (Φ1 eₛ eₜ) (Φ2 eₛ eₜ)) →
      Frame p R
        (SIM eₛ ≳ eₜ [[ X ]] [[ Φ1 ]])
        (SIM eₛ ≳ eₜ [[ X ]] [[ Φ2 ]]).
    Proof.
      rewrite /Frame simv_frame_l.
      iIntros "%HR Hsim".
      iApply (simv_mono with "[] Hsim"). iIntros "%eₛ' %eₜ'". iApply HR.
    Qed.

    #[global] Instance elim_modal_cupd_simv p P eₛ eₜ Φ :
      ElimModal True p false (|++> P) P
        (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]])
        (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "_ (HP & Hsim)".
      iApply cupd_simv. iMod "HP". iModIntro. iApply ("Hsim" with "HP").
    Qed.
    #[global] Instance elim_modal_bupd_simv p P eₛ eₜ Φ :
      ElimModal True p false (|==> P) P
        (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]])
        (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      iIntros "_ (HP & Hsim)".
      iApply bupd_simv. iMod "HP". iModIntro. iApply ("Hsim" with "HP").
    Qed.

    #[global] Instance add_modal_cupd_simv P eₛ eₜ Φ :
      AddModal (|++> P) P (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite /AddModal.
      iIntros "(HP & Hsim)".
      iApply cupd_simv. iMod "HP". iApply ("Hsim" with "HP").
    Qed.
    #[global] Instance add_modal_bupd_simv P eₛ eₜ Φ :
      AddModal (|==> P) P (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite /AddModal.
      iIntros "(HP & Hsim)".
      iApply bupd_simv. iMod "HP". iApply ("Hsim" with "HP").
    Qed.

    Lemma tac_simv_eval eₛ eₛ' eₜ eₜ' Φ Δ :
      (∀ (eₛ'' := eₛ'), eₛ = eₛ'') →
      (∀ (eₜ'' := eₜ'), eₜ = eₜ'') →
      envs_entails Δ (SIM eₛ' ≳ eₜ' [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      intros -> ->. done.
    Qed.

    Lemma tac_simv_strongly_stuck eₛ eₜ Φ Δ :
      IsStronglyStuck sim_progₛ eₛ →
      IsStronglyStuck sim_progₜ eₜ →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal.
      iIntros. iApply simv_strongly_stuck; done.
    Qed.

    Lemma tac_simv_post eₛ vₛ eₜ vₜ Φ Δ :
      eₛ = of_val vₛ →
      eₜ = of_val vₜ →
      envs_entails Δ (Φ vₛ vₜ) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => -> -> ->.
      iIntros. iApply simv_post; done.
    Qed.

    Lemma tac_cupd_simv eₛ eₜ Φ Δ :
      envs_entails Δ (|++> SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply cupd_simv.
    Qed.
    Lemma tac_bupd_simv eₛ eₜ Φ Δ :
      envs_entails Δ (|==> SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply bupd_simv.
    Qed.

    Lemma tac_simv_cupd eₛ eₜ Φ Δ :
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] [[ λ eₛ eₜ, |++> Φ eₛ eₜ ]]) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply simv_cupd.
    Qed.
    Lemma tac_simv_bupd eₛ eₜ Φ Δ :
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] [[ λ eₛ eₜ, |==> Φ eₛ eₜ ]]) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      rewrite envs_entails_unseal => ->.
      iApply simv_bupd.
    Qed.

    Lemma tac_simv_bind Kₛ fₛ eₛ Kₜ fₜ eₜ Φ Δ :
      fₛ = (λ eₛ, Kₛ @@ eₛ) →
      fₜ = (λ eₜ, Kₜ @@ eₜ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ X ]] [[ λ vₛ vₜ,
          SIM fₛ (of_val vₛ) ≳ fₜ (of_val vₜ) [[ X ]] [[ Φ ]]
        ]]
      ) →
      envs_entails Δ (
        SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ X ]] [[ Φ ]]
      ).
    Proof.
      rewrite envs_entails_unseal -simv_bind => -> -> -> //.
    Qed.
    Lemma tac_simv_bindₛ K f eₛ eₜ Φ Δ :
      f = (λ eₛ, K @@ eₛ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ X ]] [[ λ vₛ vₜ,
          SIM f (of_val vₛ) ≳ of_val vₜ [[ X ]] [[ Φ ]]
        ]]
      ) →
      envs_entails Δ (
        SIM K @@ eₛ ≳ eₜ [[ X ]] [[ Φ ]]
      ).
    Proof.
      rewrite envs_entails_unseal -simv_bindₛ => -> -> //.
    Qed.
    Lemma tac_simv_bindₜ eₛ K f eₜ Φ Δ :
      f = (λ eₜ, K @@ eₜ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ X ]] [[ λ vₛ vₜ,
          SIM of_val vₛ ≳ f (of_val vₜ) [[ X ]] [[ Φ ]]
        ]]
      ) →
      envs_entails Δ (
        SIM eₛ ≳ K @@ eₜ [[ X ]] [[ Φ ]]
      ).
    Proof.
      rewrite envs_entails_unseal -simv_bindₜ => -> -> //.
    Qed.

    Lemma tac_simv_pure_execₛ ϕ n K eₛ1 eₛ2 eₜ Φ Δ :
      PureExec sim_progₛ ϕ n eₛ1 eₛ2 →
      ϕ →
      envs_entails Δ (SIM K @@ eₛ2 ≳ eₜ [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM K @@ eₛ1 ≳ eₜ [[ X ]] [[ Φ ]]).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      rewrite envs_entails_unseal => ? ? ->.
      eapply simv_pure_stepsₛ, rtc_nsteps_2, pure_exec_pure_steps; done.
    Qed.
    Lemma tac_simv_pure_execₜ ϕ n eₛ K eₜ1 eₜ2 Φ Δ :
      PureExec sim_progₜ ϕ n eₜ1 eₜ2 →
      ϕ →
      envs_entails Δ (SIM eₛ ≳ K @@ eₜ2 [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM eₛ ≳ K @@ eₜ1 [[ X ]] [[ Φ ]]).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      rewrite envs_entails_unseal => ? ? ->.
      eapply simv_pure_stepsₜ, rtc_nsteps_2, pure_exec_pure_steps; done.
    Qed.
  End simv.
End sim_state.

#[local] Tactic Notation "expr_is_val" open_constr(e) :=
  eunify (of_val _) e.

#[local] Tactic Notation "ectx_is_empty" open_constr(K) :=
  let ectx := type of K in
  unshelve unify (empty : ectx) K; [].

Tactic Notation "match_sim_or_simv" tactic3(tac_sim) tactic3(tac_simv) tactic3(tac_fail) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ (sim ?X ?Φ ?eₛ ?eₜ) =>
      tac_sim Δ X Φ eₛ eₜ
  | |- envs_entails ?Δ (simv ?X ?Φ ?eₛ ?eₜ) =>
      tac_simv Δ X Φ eₛ eₜ
  | _ =>
      tac_fail ()
  end.
Tactic Notation "match_sim_or_simv'" tactic3(tac_succ) tactic3(tac_fail) :=
  match_sim_or_simv
    ltac:(tac_succ)
    ltac:(tac_succ)
    ltac:(tac_fail).
Tactic Notation "match_sim" tactic3(tac_succ) tactic3(tac_fail) :=
  match_sim_or_simv
    ltac:(tac_succ)
    ltac:(fun _ _ _ _ _ => tac_fail ())
    ltac:(tac_fail).
Tactic Notation "match_simv" tactic3(tac_succ) tactic3(tac_fail) :=
  match_sim_or_simv
    ltac:(fun _ _ _ _ _ => tac_fail ())
    ltac:(tac_succ)
    ltac:(tac_fail).

Tactic Notation "on_sim_or_simv" tactic3(tac_sim) tactic3(tac_simv) :=
  match_sim_or_simv
    ltac:(tac_sim)
    ltac:(tac_simv)
    ltac:(fun _ => fail "not a 'sim' or a 'simv'").
Tactic Notation "on_sim_or_simv'" tactic3(tac) :=
  on_sim_or_simv
    ltac:(tac)
    ltac:(tac).
Tactic Notation "on_sim" tactic3(tac) :=
  match_sim
    ltac:(tac)
    ltac:(fun _ => fail "not a 'sim'").
Tactic Notation "on_simv" tactic3(tac) :=
  match_simv
    ltac:(tac)
    ltac:(fun _ => fail "not a 'simv'").

Tactic Notation "sim_eval" tactic3(tacₛ) tactic3(tacₜ) :=
  on_sim_or_simv
    ltac:(fun _ _ _ _ _ => notypeclasses refine (tac_sim_eval _ _ _ _ _ _ _ _ _ _))
    ltac:(fun _ _ _ _ _ => notypeclasses refine (tac_simv_eval _ _ _ _ _ _ _ _ _ _));
  [ let x := fresh in intros x; tacₛ; unfold x; notypeclasses refine eq_refl
  | let x := fresh in intros x; tacₜ; unfold x; notypeclasses refine eq_refl
  | idtac
  ].
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

Ltac sim_simpl_post :=
  on_sim_or_simv
    ltac:(fun Δ X Φ eₛ eₜ =>
      let Φ := eval simpl in Φ in
      change (envs_entails Δ (sim X Φ eₛ eₜ))
    )
    ltac:(fun Δ X Φ eₛ eₜ =>
      let Φ := eval simpl in Φ in
      change (envs_entails Δ (simv X Φ eₛ eₜ))
    ).

Ltac sim_strongly_stuck :=
  on_sim_or_simv
    ltac:(fun _ _ _ _ _ => eapply tac_sim_strongly_stuck)
    ltac:(fun _ _ _ _ _ => eapply tac_simv_strongly_stuck);
  [ iSolveTC
  | iSolveTC
  ].

Ltac cupd_sim :=
  on_sim_or_simv
    ltac:(fun _ _ _ _ _ => eapply tac_cupd_sim)
    ltac:(fun _ _ _ _ _ => eapply tac_cupd_simv).

Ltac sim_cupd_simple :=
  on_sim_or_simv
    ltac:(fun _ _ _ _ _ => eapply tac_sim_cupd)
    ltac:(fun _ _ _ _ _ => eapply tac_simv_cupd).
Ltac sim_cupd :=
  on_sim_or_simv'
    ltac:(fun _ _ Φ _ _ =>
      first
      [ assert (∀ P eₛ eₜ, AddModal (|++> P) P (Φ eₛ eₜ)) as _ by iSolveTC
      | sim_cupd_simple
      ]
    ).

Ltac bupd_sim :=
  on_sim_or_simv
    ltac:(fun _ _ _ _ _ => eapply tac_bupd_sim)
    ltac:(fun _ _ _ _ _ => eapply tac_bupd_simv).

Ltac sim_bupd_simple :=
  on_sim_or_simv
    ltac:(fun _ _ _ _ _ => eapply tac_sim_bupd)
    ltac:(fun _ _ _ _ _ => eapply tac_simv_bupd).
Ltac sim_bupd :=
  on_sim_or_simv' ltac:(fun _ _ Φ _ _ =>
    first
    [ assert (∀ P eₛ eₜ, AddModal (|==> P) P (Φ eₛ eₜ)) as _ by iSolveTC
    | sim_bupd_simple
    ]
  ).

Ltac sim_post_simple :=
  on_sim_or_simv
    ltac:(fun _ _ _ _ _ =>
      eapply tac_sim_post
    )
    ltac:(fun _ _ _ _ _ =>
      eapply tac_simv_post;
      [ reflexivity
      | reflexivity
      | idtac
      ]
    ).
Ltac sim_post :=
  sim_simpl;
  sim_cupd;
  sim_post_simple;
  try done.

Tactic Notation "sim_finish" "with" tactic3(tac) :=
  sim_eval (simpl; rewrite ?fill_empty; tac);
  on_sim_or_simv
    ltac:(fun _ _ _ eₛ eₜ =>
      tryif expr_is_val eₛ; expr_is_val eₜ then (
        sim_post
      ) else (
        try solve [sim_post]
      )
    )
    ltac:(fun _ _ _ _ _ =>
      try sim_post
    );
  pm_prettify.
Tactic Notation "sim_finish" :=
  sim_finish with idtac.

Tactic Notation "sim_bind_coreₛ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    on_sim_or_simv
      ltac:(fun _ _ _ _ _ => eapply (tac_sim_bindₛ _ K))
      ltac:(fun _ _ _ _ _ => eapply (tac_simv_bindₛ _ K));
    [ simpl; reflexivity
    | pm_prettify; sim_simpl_post
    ]
  ).
Tactic Notation "sim_bind_coreₜ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    on_sim_or_simv
      ltac:(fun _ _ _ _ _ => eapply (tac_sim_bindₜ _ _ K))
      ltac:(fun _ _ _ _ _ => eapply (tac_simv_bindₜ _ _ K));
    [ simpl; reflexivity
    | pm_prettify; sim_simpl_post
    ]
  ).
Tactic Notation "sim_bind_core" open_constr(Kₛ) open_constr(Kₜ) :=
  tryif ectx_is_empty Kₛ then (
    sim_bind_coreₜ Kₜ
  ) else (
    tryif ectx_is_empty Kₜ then (
      sim_bind_coreₛ Kₛ
    ) else (
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_bind _ Kₛ _ _ Kₜ))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_bind _ Kₛ _ _ Kₜ));
      [ simpl; reflexivity
      | simpl; reflexivity
      | pm_prettify; sim_simpl_post
      ]
    )
  ).

Tactic Notation "sim_pure_coreₛ" open_constr(K) "with" tactic3(tac) :=
  on_sim_or_simv
    ltac:(fun _ _ _ _ _ => eapply (tac_sim_pure_execₛ _ _ _ K))
    ltac:(fun _ _ _ _ _ => eapply (tac_simv_pure_execₛ _ _ _ K));
  [ iSolveTC
  | try done
  | sim_finish with tac
  ].
Tactic Notation "sim_pure_coreₛ" open_constr(K) :=
  sim_pure_coreₛ K with idtac.
Tactic Notation "sim_pure_coreₜ" open_constr(K) "with" tactic3(tac) :=
  on_sim_or_simv
    ltac:(fun _ _ _ _ _ => eapply (tac_sim_pure_execₜ _ _ _ _ K))
    ltac:(fun _ _ _ _ _ => eapply (tac_simv_pure_execₜ _ _ _ _ K));
  [ iSolveTC
  | try done
  | sim_finish with tac
  ].
Tactic Notation "sim_pure_coreₜ" open_constr(K) :=
  sim_pure_coreₜ K with idtac.
