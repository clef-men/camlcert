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
  Context (Χ : sim_protocol PROP Λₛ Λₜ).

  Section sim.
    #[global] Instance frame_sim p R Φ1 Φ2 eₛ eₜ :
      (∀ eₛ eₜ, Frame p R (Φ1 eₛ eₜ) (Φ2 eₛ eₜ)) →
      Frame p R
        (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ1 }})
        (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ2 }}).
    Proof.
      rewrite /Frame sim_frame_l sim_mono'.
      iIntros "%HΦ HΦ2".
      iDestruct ("HΦ2" with "[]") as "HΦ2"; last iSmash.
      clear eₛ eₜ. iIntros "%eₛ %eₜ". iDestruct HΦ as "HΦ". iSmash.
    Qed.

    #[global] Instance elim_modal_cupd_sim p P Φ eₛ eₜ :
      ElimModal True p false (|++> P) P
        (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }})
        (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      setoid_rewrite <- cupd_sim at 2. iSmash.
    Qed.
    #[global] Instance elim_modal_bupd_sim p P Φ eₛ eₜ :
      ElimModal True p false (|==> P) P
        (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }})
        (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      setoid_rewrite <- bupd_sim at 2. iSmash.
    Qed.

    #[global] Instance add_modal_cupd_sim P Φ eₛ eₜ :
      AddModal (|++> P) P (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite /AddModal.
      setoid_rewrite <- cupd_sim at 2. iSmash.
    Qed.
    #[global] Instance add_modal_bupd_sim P Φ eₛ eₜ :
      AddModal (|==> P) P (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite /AddModal.
      setoid_rewrite <- bupd_sim at 2. iSmash.
    Qed.

    Lemma tac_sim_eval Δ Φ eₛ eₛ' eₜ eₜ' :
      (∀ (eₛ'' := eₛ'), eₛ = eₛ'') →
      (∀ (eₜ'' := eₜ'), eₜ = eₜ'') →
      envs_entails Δ (SIM eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      move=> -> -> //.
    Qed.

    Lemma tac_sim_strongly_stuck Δ Φ ϕₛ eₛ ϕₜ eₜ :
      IsStronglyStuck sim_progₛ ϕₛ eₛ →
      ϕₛ →
      IsStronglyStuck sim_progₜ ϕₜ eₜ →
      ϕₜ →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      intros. rewrite -sim_strongly_stuck //; apply is_strongly_stuck; done.
    Qed.

    Lemma tac_sim_post Δ Φ eₛ eₜ :
      envs_entails Δ (Φ eₛ eₜ) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite -sim_post //.
    Qed.

    Lemma tac_cupd_sim Δ Φ eₛ eₜ :
      envs_entails Δ (|++> SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite cupd_sim //.
    Qed.
    Lemma tac_bupd_sim Δ Φ eₛ eₜ :
      envs_entails Δ (|==> SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite bupd_sim //.
    Qed.

    Lemma tac_sim_cupd Δ Φ eₛ eₜ :
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite sim_cupd //.
    Qed.
    Lemma tac_sim_bupd Δ Φ eₛ eₜ :
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite sim_bupd //.
    Qed.

    Lemma tac_sim_bind Δ Φ Kₛ fₛ eₛ Kₜ fₜ eₜ :
      fₛ = (λ eₛ, Kₛ @@ eₛ) →
      fₜ = (λ eₜ, Kₜ @@ eₜ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          SIM fₛ eₛ' ≳ fₜ eₜ' [[ Χ ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ Χ ]] {{ Φ }}
      ).
    Proof.
      rewrite -sim_bind => -> -> //.
    Qed.
    Lemma tac_sim_bindₛ Δ Φ K f eₛ eₜ :
      f = (λ eₛ, K @@ eₛ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          SIM f eₛ' ≳ eₜ' [[ Χ ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM K @@ eₛ ≳ eₜ [[ Χ ]] {{ Φ }}
      ).
    Proof.
      rewrite -sim_bindₛ => -> //.
    Qed.
    Lemma tac_sim_bindₜ Δ Φ eₛ K f eₜ :
      f = (λ eₜ, K @@ eₜ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          SIM eₛ' ≳ f eₜ' [[ Χ ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM eₛ ≳ K @@ eₜ [[ Χ ]] {{ Φ }}
      ).
    Proof.
      rewrite -sim_bindₜ => -> //.
    Qed.

    Lemma tac_sim_pure_execₛ Δ Φ n ϕ K eₛ1 eₛ2 eₜ :
      PureExec sim_progₛ n ϕ eₛ1 eₛ2 →
      ϕ →
      envs_entails Δ (SIM K @@ eₛ2 ≳ eₜ [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (SIM K @@ eₛ1 ≳ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      intros. rewrite -sim_pure_stepsₛ //.
      eapply rtc_nsteps_2, pure_exec_pure_steps. done.
    Qed.
    Lemma tac_sim_pure_execₜ Δ Φ n ϕ eₛ K eₜ1 eₜ2 :
      PureExec sim_progₜ n ϕ eₜ1 eₜ2 →
      ϕ →
      envs_entails Δ (SIM eₛ ≳ K @@ eₜ2 [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (SIM eₛ ≳ K @@ eₜ1 [[ Χ ]] {{ Φ }}).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      intros. rewrite -sim_pure_stepsₜ //.
      eapply rtc_nsteps_2, pure_exec_pure_steps. done.
    Qed.
  End sim.

  Section simv.
    #[global] Instance frame_simv p R Φ1 Φ2 eₛ eₜ :
      (∀ eₛ eₜ, Frame p R (Φ1 eₛ eₜ) (Φ2 eₛ eₜ)) →
      Frame p R
        (SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ1 }})
        (SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ2 }}).
    Proof.
      rewrite /Frame simv_frame_l simv_mono'.
      iIntros "%HΦ HΦ2".
      iDestruct ("HΦ2" with "[]") as "HΦ2"; last iSmash.
      clear eₛ eₜ. iIntros "%eₛ %eₜ". iDestruct HΦ as "HΦ". iSmash.
    Qed.

    Lemma tac_simv_post Δ Φ eₛ vₛ eₜ vₜ :
      eₛ = of_val vₛ →
      eₜ = of_val vₜ →
      envs_entails Δ (Φ vₛ vₜ) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}).
    Proof.
      intros. rewrite -simv_post //.
    Qed.

    Lemma tac_simv_cupd Δ Φ eₛ eₜ :
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, |++> Φ eₛ eₜ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}).
    Proof.
      rewrite simv_cupd //.
    Qed.
    Lemma tac_simv_bupd Δ Φ eₛ eₜ :
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{# λ eₛ eₜ, |==> Φ eₛ eₜ }}) →
      envs_entails Δ (SIM eₛ ≳ eₜ [[ Χ ]] {{# Φ }}).
    Proof.
      rewrite simv_bupd //.
    Qed.

    Lemma tac_simv_bind Δ Φ Kₛ fₛ eₛ Kₜ fₜ eₜ :
      fₛ = (λ eₛ, Kₛ @@ eₛ) →
      fₜ = (λ eₜ, Kₜ @@ eₜ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ vₛ vₜ,
          SIM fₛ (of_val vₛ) ≳ fₜ (of_val vₜ) [[ Χ ]] {{# Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM Kₛ @@ eₛ ≳ Kₜ @@ eₜ [[ Χ ]] {{# Φ }}
      ).
    Proof.
      rewrite -simv_bind => -> -> //.
    Qed.
    Lemma tac_simv_bindₛ Δ Φ K f eₛ eₜ :
      f = (λ eₛ, K @@ eₛ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ vₛ vₜ,
          SIM f (of_val vₛ) ≳ of_val vₜ [[ Χ ]] {{# Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM K @@ eₛ ≳ eₜ [[ Χ ]] {{# Φ }}
      ).
    Proof.
      rewrite -simv_bindₛ => -> //.
    Qed.
    Lemma tac_simv_bindₜ Δ Φ eₛ K f eₜ :
      f = (λ eₜ, K @@ eₜ) →
      envs_entails Δ (
        SIM eₛ ≳ eₜ [[ Χ ]] {{# λ vₛ vₜ,
          SIM of_val vₛ ≳ f (of_val vₜ) [[ Χ ]] {{# Φ }}
        }}
      ) →
      envs_entails Δ (
        SIM eₛ ≳ K @@ eₜ [[ Χ ]] {{# Φ }}
      ).
    Proof.
      rewrite -simv_bindₜ => -> //.
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
  | |- envs_entails ?Δ ?Q =>
      let Χ := open_constr:(_) in
      let Φ := open_constr:(_) in
      let eₛ := open_constr:(_) in
      let eₜ := open_constr:(_) in
      tryif unify Q (simv Χ Φ eₛ eₜ) then (
        tac_simv Δ Χ Φ eₛ eₜ
      ) else tryif unify Q (sim Χ Φ eₛ eₜ) then (
        tac_sim Δ Χ Φ eₛ eₜ
      ) else (
        tac_fail ()
      )
  | _ =>
      tac_fail ()
  end.
Tactic Notation "match_sim" tactic3(tac_succ) tactic3(tac_fail) :=
  match_sim_or_simv
    ltac:(tac_succ)
    ltac:(tac_succ)
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
Tactic Notation "on_sim" tactic3(tac) :=
  match_sim
    ltac:(tac)
    ltac:(fun _ => fail "not a 'sim'").
Tactic Notation "on_simv" tactic3(tac) :=
  match_simv
    ltac:(tac)
    ltac:(fun _ => fail "not a 'simv'").

Tactic Notation "sim_eval" tactic3(tacₛ) tactic3(tacₜ) :=
  on_sim ltac:(fun _ _ _ _ _ =>
    notypeclasses refine (tac_sim_eval _ _ _ _ _ _ _ _ _ _)
  );
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
    ltac:(fun Δ Χ Φ eₛ eₜ =>
      let Φ := eval cbn in Φ in
      change (envs_entails Δ (sim Χ Φ eₛ eₜ))
    )
    ltac:(fun Δ Χ Φ eₛ eₜ =>
      let Φ := eval cbn in Φ in
      change (envs_entails Δ (simv Χ Φ eₛ eₜ))
    ).

Ltac sim_strongly_stuck :=
  on_sim ltac:(fun _ _ _ _ _ =>
    eapply tac_sim_strongly_stuck
  );
  [ tc_solve
  | done
  | tc_solve
  | done
  ].

Ltac cupd_sim :=
  on_sim ltac:(fun _ _ _ _ _ =>
    eapply tac_cupd_sim
  ).
Ltac bupd_sim :=
  on_sim ltac:(fun _ _ _ _ _ =>
    eapply tac_bupd_sim
  ).

Ltac sim_cupd :=
  on_sim_or_simv
    ltac:(fun _ _ Φ _ _ =>
      tryif assert (∀ P eₛ eₜ, AddModal (|++> P) P (Φ eₛ eₜ)) as _ by tc_solve then (
        idtac
      ) else (
        eapply tac_sim_cupd
      )
    )
    ltac:(fun _ _ Φ _ _ =>
      tryif assert (∀ P vₛ vₜ, AddModal (|++> P) P (Φ vₛ vₜ)) as _ by tc_solve then (
        idtac
      ) else (
        eapply tac_simv_cupd
      )
    ).

Ltac sim_bupd :=
  on_sim_or_simv
    ltac:(fun _ _ Φ _ _ =>
      tryif assert (∀ P eₛ eₜ, AddModal (|==> P) P (Φ eₛ eₜ)) as _ by tc_solve then (
        idtac
      ) else (
        eapply tac_sim_bupd
      )
    )
    ltac:(fun _ _ Φ _ _ =>
      tryif assert (∀ P vₛ vₜ, AddModal (|==> P) P (Φ vₛ vₜ)) as _ by tc_solve then (
        idtac
      ) else (
        eapply tac_simv_bupd
      )
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
  try iSmash+.

Tactic Notation "sim_finish" tactic3(helper) :=
  try done;
  sim_eval (simpl; rewrite ?fill_empty; helper);
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

#[global] Instance sim_finisher_option : TacticFlag "sim_finisher" | 100 :=
  {| tactic_flag := true |}.
Tactic Notation "sim_finisher" tactic3(helper) :=
  lazymatch tactic_flag_get "sim_finisher" with
  | true =>
      sim_finish helper
  | _ =>
      idtac
  end.

Tactic Notation "sim_bind_coreₛ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    on_sim_or_simv
      ltac:(fun _ _ _ _ _ => eapply (tac_sim_bindₛ _ _ _ K))
      ltac:(fun _ _ _ _ _ => eapply (tac_simv_bindₛ _ _ _ K));
    [ simpl; reflexivity
    | pm_prettify; sim_simpl_post
    ]
  ).
Tactic Notation "sim_bind_coreₜ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    on_sim_or_simv
      ltac:(fun _ _ _ _ _ => eapply (tac_sim_bindₜ _ _ _ _ K))
      ltac:(fun _ _ _ _ _ => eapply (tac_simv_bindₜ _ _ _ _ K));
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
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_bind _ _ _ Kₛ _ _ Kₜ))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_bind _ _ _ Kₛ _ _ Kₜ));
      [ simpl; reflexivity
      | simpl; reflexivity
      | pm_prettify; sim_simpl_post
      ]
    )
  ).

Tactic Notation "sim_pure_coreₛ" open_constr(K) :=
  on_sim ltac:(fun _ _ _ _ _ =>
    eapply (tac_sim_pure_execₛ _ _ _ _ _ K)
  );
  [ tc_solve
  | try done
  | idtac
  ].
Tactic Notation "sim_pure_coreₜ" open_constr(K) :=
  on_sim ltac:(fun _ _ _ _ _ =>
    eapply (tac_sim_pure_execₜ _ _ _ _ _ _ K)
  );
  [ tc_solve
  | try done
  | idtac
  ].
