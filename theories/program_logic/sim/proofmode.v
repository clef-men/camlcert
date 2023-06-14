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

  Lemma tac_simv_strongly_stuck eₛ eₜ Φ Δ :
    IsStronglyStuck progₛ eₛ →
    IsStronglyStuck progₜ eₜ →
    envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
  Proof.
    rewrite envs_entails_unseal.
    iIntros. iApply simv_strongly_stuck; done.
  Qed.

  Lemma tac_simv_post eₛ vₛ eₜ vₜ Φ Δ :
    eₛ = of_val vₛ →
    eₜ = of_val vₜ →
    envs_entails Δ (Φ vₛ vₜ) →
    envs_entails Δ (SIM progₛ; eₛ ≳ progₜ; eₜ [[ X ]] [[ Φ ]]).
  Proof.
    rewrite envs_entails_unseal => -> -> ->.
    iIntros. iApply simv_post; done.
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
End sim_state.

Tactic Notation "expr_is_val" open_constr(e) :=
  eunify (of_val _) e.

Tactic Notation "ectx_is_empty" open_constr(K) :=
  let ectx := type of K in
  unshelve unify (empty : ectx) K; [].

Tactic Notation "match_simv" tactic3(tac_succ) tactic3(tac_fail) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ (simv ?progₛ ?progₜ ?X ?Φ ?eₛ ?eₜ) =>
      tac_succ Δ progₛ progₜ X Φ eₛ eₜ
  | _ =>
      tac_fail ()
  end.

Tactic Notation "on_simv" tactic3(tac) :=
  match_simv ltac:(tac) ltac:(fun _ => fail "not a 'simv'").

Tactic Notation "simv_eval" tactic3(tacₛ) tactic3(tacₜ) :=
  on_simv ltac:(fun _ _ _ _ _ _ _ =>
    notypeclasses refine (tac_simv_eval _ _ _ _ _ _ _ _ _ _ _ _);
    [ let x := fresh in intros x; tacₛ; unfold x; notypeclasses refine eq_refl
    | let x := fresh in intros x; tacₜ; unfold x; notypeclasses refine eq_refl
    | idtac
    ]
  ).
Tactic Notation "simv_eval" tactic3(tac) :=
  simv_eval ltac:(tac) ltac:(tac).
Tactic Notation "simv_evalₛ" tactic3(tac) :=
  simv_eval ltac:(tac) ltac:(idtac).
Tactic Notation "simv_evalₜ" tactic3(tac) :=
  simv_eval ltac:(idtac) ltac:(tac).

Ltac simv_simpl :=
  simv_eval simpl.
Ltac simv_simplₛ :=
  simv_evalₛ simpl.
Ltac simv_simplₜ :=
  simv_evalₜ simpl.

Ltac simv_simpl_post :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ (simv ?progₛ ?progₜ ?X ?Φ ?eₛ ?eₜ) =>
      let Φ := eval simpl in Φ in
      change (envs_entails Δ (simv progₛ progₜ X Φ eₛ eₜ))
  | _ =>
     fail "simv_simpl_post: not a 'simv'"
  end.

Ltac simv_strongly_stuck :=
  on_simv ltac:(fun _ _ _ _ _ _ _ =>
    eapply tac_simv_strongly_stuck;
    [ iSolveTC
    | iSolveTC
    ]
  ).

Ltac cupd_sim :=
  on_simv ltac:(fun _ _ _ _ _ _ _ =>
    eapply tac_cupd_simv
  ).

Ltac simv_cupd_simple :=
  on_simv ltac:(fun _ _ _ _ _ _ _ =>
    eapply tac_simv_cupd
  ).
Ltac simv_cupd :=
  on_simv ltac:(fun _ _ _ _ Φ _ _ =>
    first
    [ assert (∀ P eₛ eₜ, AddModal (|++> P) P (Φ eₛ eₜ)) as _ by iSolveTC
    | simv_cupd_simple
    ]
  ).

Ltac bupd_sim :=
  on_simv ltac:(fun _ _ _ _ _ _ _ =>
    eapply tac_bupd_simv
  ).

Ltac simv_bupd_simple :=
  on_simv ltac:(fun _ _ _ _ _ _ _ =>
    eapply tac_simv_bupd
  ).
Ltac simv_bupd :=
  on_simv ltac:(fun _ _ _ _ Φ _ _ =>
    first
    [ assert (∀ P eₛ eₜ, AddModal (|==> P) P (Φ eₛ eₜ)) as _ by iSolveTC
    | simv_bupd_simple
    ]
  ).

Ltac simv_post_simple :=
  on_simv ltac:(fun _ _ _ _ _ _ _ =>
    eapply tac_simv_post;
    [ reflexivity
    | reflexivity
    | idtac
    ]
  ).
Ltac simv_post :=
  simv_simpl;
  simv_cupd;
  simv_post_simple;
  try done.

Tactic Notation "simv_finish" "with" tactic3(tac) :=
  simv_eval (simpl; rewrite ?fill_empty; tac);
  try simv_post;
  pm_prettify.
Tactic Notation "simv_finish" :=
  simv_finish with idtac.

Tactic Notation "simv_bind_coreₛ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    eapply (tac_simv_bindₛ _ _ _ K);
    [ simpl; reflexivity
    | pm_prettify; simv_simpl_post
    ]
  ).
Tactic Notation "simv_bind_coreₜ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    eapply (tac_simv_bindₜ _ _ _ _ K);
    [ simpl; reflexivity
    | pm_prettify; simv_simpl_post
    ]
  ).
Tactic Notation "simv_bind_core" open_constr(Kₛ) open_constr(Kₜ) :=
  tryif ectx_is_empty Kₛ then (
    simv_bind_coreₜ Kₜ
  ) else (
    tryif ectx_is_empty Kₜ then (
      simv_bind_coreₛ Kₛ
    ) else (
      eapply (tac_simv_bind _ _ _ Kₛ _ _ Kₜ);
      [ simpl; reflexivity
      | simpl; reflexivity
      | pm_prettify; simv_simpl_post
      ]
    )
  ).

Tactic Notation "simv_pure_coreₛ" open_constr(K) "with" tactic3(tac) :=
  eapply (tac_simv_pure_execₛ _ _ _ _ _ K);
  [ iSolveTC
  | try done
  | simv_finish with tac
  ].
Tactic Notation "simv_pure_coreₛ" open_constr(K) :=
  simv_pure_coreₛ K with idtac.
Tactic Notation "simv_pure_coreₜ" open_constr(K) "with" tactic3(tac) :=
  eapply (tac_simv_pure_execₜ _ _ _ _ _ _ K);
  [ iSolveTC
  | try done
  | simv_finish with tac
  ].
Tactic Notation "simv_pure_coreₜ" open_constr(K) :=
  simv_pure_coreₜ K with idtac.
