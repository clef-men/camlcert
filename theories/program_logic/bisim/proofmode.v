From iris.proofmode Require Import
  coq_tactics
  reduction.

From simuliris Require Import
  prelude.
From simuliris.base_logic Require Export
  lib.cupd.proofmode.
From simuliris.program_logic Require Export
  bisim.rules.
From simuliris.program_logic Require Import
  bisim.notations.

Section sim_state.
  Context `{sim_programs : !SimPrograms Λₛ Λₜ}.
  Context `{!BiBUpd PROP, !BiAffine PROP}.
  Context `{sim_state : !SimState PROP Λₛ Λₜ}.
  Context (Χ : sim_protocol PROP Λₛ Λₜ).

  Section bisim.
    #[global] Instance frame_bisim p R Φ1 Φ2 eₛ eₜ :
      (∀ eₛ eₜ, Frame p R (Φ1 eₛ eₜ) (Φ2 eₛ eₜ)) →
      Frame p R
        (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ1 }})
        (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ2 }}).
    Proof.
      rewrite /Frame bisim_frame_l bisim_mono'.
      iIntros "%HΦ HΦ2".
      iDestruct ("HΦ2" with "[]") as "HΦ2"; last iSmash.
      clear eₛ eₜ. iIntros "%eₛ %eₜ". iDestruct HΦ as "HΦ". iSmash.
    Qed.

    #[global] Instance elim_modal_cupd_bisim p P Φ eₛ eₜ :
      ElimModal True p false (|++> P) P
        (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }})
        (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      setoid_rewrite <- cupd_bisim at 2. iSmash.
    Qed.
    #[global] Instance elim_modal_bupd_bisim p P Φ eₛ eₜ :
      ElimModal True p false (|==> P) P
        (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }})
        (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite /ElimModal bi.intuitionistically_if_elim.
      setoid_rewrite <- bupd_bisim at 2. iSmash.
    Qed.

    #[global] Instance add_modal_cupd_bisim P Φ eₛ eₜ :
      AddModal (|++> P) P (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite /AddModal.
      setoid_rewrite <- cupd_bisim at 2. iSmash.
    Qed.
    #[global] Instance add_modal_bupd_bisim P Φ eₛ eₜ :
      AddModal (|==> P) P (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite /AddModal.
      setoid_rewrite <- bupd_bisim at 2. iSmash.
    Qed.

    Lemma tac_bisim_eval Δ Φ eₛ eₛ' eₜ eₜ' :
      (∀ (eₛ'' := eₛ'), eₛ = eₛ'') →
      (∀ (eₜ'' := eₜ'), eₜ = eₜ'') →
      envs_entails Δ (BISIM eₛ' ≃ eₜ' [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      move=> -> -> //.
    Qed.

    Lemma tac_bisim_strongly_stuck Δ Φ ϕₛ eₛ ϕₜ eₜ :
      IsStronglyStuck sim_progₛ ϕₛ eₛ →
      ϕₛ →
      IsStronglyStuck sim_progₜ ϕₜ eₜ →
      ϕₜ →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      intros. rewrite -bisim_strongly_stuck //; apply is_strongly_stuck; done.
    Qed.

    Lemma tac_bisim_post Δ Φ eₛ eₜ :
      envs_entails Δ (Φ eₛ eₜ) →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite -bisim_post //.
    Qed.

    Lemma tac_cupd_bisim Δ Φ eₛ eₜ :
      envs_entails Δ (|++> BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite cupd_bisim //.
    Qed.
    Lemma tac_bupd_bisim Δ Φ eₛ eₜ :
      envs_entails Δ (|==> BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite bupd_bisim //.
    Qed.

    Lemma tac_bisim_cupd Δ Φ eₛ eₜ :
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ eₜ, |++> Φ eₛ eₜ }}) →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite bisim_cupd //.
    Qed.
    Lemma tac_bisim_bupd Δ Φ eₛ eₜ :
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ eₜ, |==> Φ eₛ eₜ }}) →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      rewrite bisim_bupd //.
    Qed.

    Lemma tac_bisim_bind Δ Φ Kₛ fₛ eₛ Kₜ fₜ eₜ :
      fₛ = (λ eₛ, Kₛ @@ eₛ) →
      fₜ = (λ eₜ, Kₜ @@ eₜ) →
      envs_entails Δ (
        BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          BISIM fₛ eₛ' ≃ fₜ eₜ' [[ Χ ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        BISIM Kₛ @@ eₛ ≃ Kₜ @@ eₜ [[ Χ ]] {{ Φ }}
      ).
    Proof.
      rewrite -bisim_bind => -> -> //.
    Qed.
    Lemma tac_bisim_bindₛ Δ Φ K f eₛ eₜ :
      f = (λ eₛ, K @@ eₛ) →
      envs_entails Δ (
        BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          BISIM f eₛ' ≃ eₜ' [[ Χ ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        BISIM K @@ eₛ ≃ eₜ [[ Χ ]] {{ Φ }}
      ).
    Proof.
      rewrite -bisim_bindₛ => -> //.
    Qed.
    Lemma tac_bisim_bindₜ Δ Φ eₛ K f eₜ :
      f = (λ eₜ, K @@ eₜ) →
      envs_entails Δ (
        BISIM eₛ ≃ eₜ [[ Χ ]] {{ λ eₛ' eₜ',
          BISIM eₛ' ≃ f eₜ' [[ Χ ]] {{ Φ }}
        }}
      ) →
      envs_entails Δ (
        BISIM eₛ ≃ K @@ eₜ [[ Χ ]] {{ Φ }}
      ).
    Proof.
      rewrite -bisim_bindₜ => -> //.
    Qed.

    Lemma tac_bisim_pure_execₛ Δ Φ n ϕ K eₛ1 eₛ2 eₜ :
      PureExec sim_progₛ n ϕ eₛ1 eₛ2 →
      ϕ →
      envs_entails Δ (BISIM K @@ eₛ2 ≃ eₜ [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (BISIM K @@ eₛ1 ≃ eₜ [[ Χ ]] {{ Φ }}).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      intros. rewrite -bisim_pure_stepsₛ //.
      eapply rtc_nsteps_2, pure_exec_pure_steps. done.
    Qed.
    Lemma tac_bisim_pure_execₜ Δ Φ n ϕ eₛ K eₜ1 eₜ2 :
      PureExec sim_progₜ n ϕ eₜ1 eₜ2 →
      ϕ →
      envs_entails Δ (BISIM eₛ ≃ K @@ eₜ2 [[ Χ ]] {{ Φ }}) →
      envs_entails Δ (BISIM eₛ ≃ K @@ eₜ1 [[ Χ ]] {{ Φ }}).
    Proof.
      pose proof @pure_exec_fill_pure_exec.
      intros. rewrite -bisim_pure_stepsₜ //.
      eapply rtc_nsteps_2, pure_exec_pure_steps. done.
    Qed.
  End bisim.

  Section bisimv.
    #[global] Instance frame_bisimv p R Φ1 Φ2 eₛ eₜ :
      (∀ eₛ eₜ, Frame p R (Φ1 eₛ eₜ) (Φ2 eₛ eₜ)) →
      Frame p R
        (BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ1 }})
        (BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ2 }}).
    Proof.
      rewrite /Frame bisimv_frame_l bisimv_mono'.
      iIntros "%HΦ HΦ2".
      iDestruct ("HΦ2" with "[]") as "HΦ2"; last iSmash.
      clear eₛ eₜ. iIntros "%eₛ %eₜ". iDestruct HΦ as "HΦ". iSmash.
    Qed.

    Lemma tac_bisimv_post Δ Φ eₛ vₛ eₜ vₜ :
      eₛ = of_val vₛ →
      eₜ = of_val vₜ →
      envs_entails Δ (Φ vₛ vₜ) →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ }}).
    Proof.
      intros. rewrite -bisimv_post //.
    Qed.

    Lemma tac_bisimv_cupd Δ Φ eₛ eₜ :
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ eₛ eₜ, |++> Φ eₛ eₜ }}) →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ }}).
    Proof.
      rewrite bisimv_cupd //.
    Qed.
    Lemma tac_bisimv_bupd Δ Φ eₛ eₜ :
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ eₛ eₜ, |==> Φ eₛ eₜ }}) →
      envs_entails Δ (BISIM eₛ ≃ eₜ [[ Χ ]] {{# Φ }}).
    Proof.
      rewrite bisimv_bupd //.
    Qed.

    Lemma tac_bisimv_bind Δ Φ Kₛ fₛ eₛ Kₜ fₜ eₜ :
      fₛ = (λ eₛ, Kₛ @@ eₛ) →
      fₜ = (λ eₜ, Kₜ @@ eₜ) →
      envs_entails Δ (
        BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ vₛ vₜ,
          BISIM fₛ (of_val vₛ) ≃ fₜ (of_val vₜ) [[ Χ ]] {{# Φ }}
        }}
      ) →
      envs_entails Δ (
        BISIM Kₛ @@ eₛ ≃ Kₜ @@ eₜ [[ Χ ]] {{# Φ }}
      ).
    Proof.
      rewrite -bisimv_bind => -> -> //.
    Qed.
    Lemma tac_bisimv_bindₛ Δ Φ K f eₛ eₜ :
      f = (λ eₛ, K @@ eₛ) →
      envs_entails Δ (
        BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ vₛ vₜ,
          BISIM f (of_val vₛ) ≃ of_val vₜ [[ Χ ]] {{# Φ }}
        }}
      ) →
      envs_entails Δ (
        BISIM K @@ eₛ ≃ eₜ [[ Χ ]] {{# Φ }}
      ).
    Proof.
      rewrite -bisimv_bindₛ => -> //.
    Qed.
    Lemma tac_bisimv_bindₜ Δ Φ eₛ K f eₜ :
      f = (λ eₜ, K @@ eₜ) →
      envs_entails Δ (
        BISIM eₛ ≃ eₜ [[ Χ ]] {{# λ vₛ vₜ,
          BISIM of_val vₛ ≃ f (of_val vₜ) [[ Χ ]] {{# Φ }}
        }}
      ) →
      envs_entails Δ (
        BISIM eₛ ≃ K @@ eₜ [[ Χ ]] {{# Φ }}
      ).
    Proof.
      rewrite -bisimv_bindₜ => -> //.
    Qed.
  End bisimv.
End sim_state.

#[local] Tactic Notation "expr_is_val" open_constr(e) :=
  eunify (of_val _) e.

#[local] Tactic Notation "ectx_is_empty" open_constr(K) :=
  let ectx := type of K in
  unshelve unify (empty : ectx) K; [].

Tactic Notation "match_bisim_or_bisimv" tactic3(tac_bisim) tactic3(tac_bisimv) tactic3(tac_fail) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails ?Δ ?Q =>
      let Χ := open_constr:(_) in
      let Φ := open_constr:(_) in
      let eₛ := open_constr:(_) in
      let eₜ := open_constr:(_) in
      tryif unify Q (bisimv Χ Φ eₛ eₜ) then (
        tac_bisimv Δ Χ Φ eₛ eₜ
      ) else tryif unify Q (bisim Χ Φ eₛ eₜ) then (
        tac_bisim Δ Χ Φ eₛ eₜ
      ) else (
        tac_fail ()
      )
  | _ =>
      tac_fail ()
  end.
Tactic Notation "match_bisim" tactic3(tac_succ) tactic3(tac_fail) :=
  match_bisim_or_bisimv
    ltac:(tac_succ)
    ltac:(tac_succ)
    ltac:(tac_fail).
Tactic Notation "match_bisimv" tactic3(tac_succ) tactic3(tac_fail) :=
  match_bisim_or_bisimv
    ltac:(fun _ _ _ _ _ => tac_fail ())
    ltac:(tac_succ)
    ltac:(tac_fail).

Tactic Notation "on_bisim_or_bisimv" tactic3(tac_bisim) tactic3(tac_bisimv) :=
  match_bisim_or_bisimv
    ltac:(tac_bisim)
    ltac:(tac_bisimv)
    ltac:(fun _ => fail "not a 'bisim' or a 'bisimv'").
Tactic Notation "on_bisim" tactic3(tac) :=
  match_bisim
    ltac:(tac)
    ltac:(fun _ => fail "not a 'bisim'").
Tactic Notation "on_bisimv" tactic3(tac) :=
  match_bisimv
    ltac:(tac)
    ltac:(fun _ => fail "not a 'bisimv'").

Tactic Notation "bisim_eval" tactic3(tacₛ) tactic3(tacₜ) :=
  on_bisim ltac:(fun _ _ _ _ _ =>
    notypeclasses refine (tac_bisim_eval _ _ _ _ _ _ _ _ _ _)
  );
  [ let x := fresh in intros x; tacₛ; unfold x; notypeclasses refine eq_refl
  | let x := fresh in intros x; tacₜ; unfold x; notypeclasses refine eq_refl
  | idtac
  ].
Tactic Notation "bisim_eval" tactic3(tac) :=
  bisim_eval ltac:(tac) ltac:(tac).
Tactic Notation "bisim_evalₛ" tactic3(tac) :=
  bisim_eval ltac:(tac) ltac:(idtac).
Tactic Notation "bisim_evalₜ" tactic3(tac) :=
  bisim_eval ltac:(idtac) ltac:(tac).

Ltac bisim_simpl :=
  bisim_eval simpl.
Ltac bisim_simplₛ :=
  bisim_evalₛ simpl.
Ltac bisim_simplₜ :=
  bisim_evalₜ simpl.

Ltac bisim_simpl_post :=
  on_bisim_or_bisimv
    ltac:(fun Δ Χ Φ eₛ eₜ =>
      let Φ := eval cbn in Φ in
      change (envs_entails Δ (bisim Χ Φ eₛ eₜ))
    )
    ltac:(fun Δ Χ Φ eₛ eₜ =>
      let Φ := eval cbn in Φ in
      change (envs_entails Δ (bisimv Χ Φ eₛ eₜ))
    ).

Ltac bisim_strongly_stuck :=
  on_bisim ltac:(fun _ _ _ _ _ =>
    eapply tac_bisim_strongly_stuck
  );
  [ tc_solve
  | done
  | tc_solve
  | done
  ].

Ltac cupd_bisim :=
  on_bisim ltac:(fun _ _ _ _ _ =>
    eapply tac_cupd_bisim
  ).
Ltac bupd_bisim :=
  on_bisim ltac:(fun _ _ _ _ _ =>
    eapply tac_bupd_bisim
  ).

Ltac bisim_cupd :=
  on_bisim_or_bisimv
    ltac:(fun _ _ Φ _ _ =>
      tryif assert (∀ P eₛ eₜ, AddModal (|++> P) P (Φ eₛ eₜ)) as _ by tc_solve then (
        idtac
      ) else (
        eapply tac_bisim_cupd
      )
    )
    ltac:(fun _ _ Φ _ _ =>
      tryif assert (∀ P vₛ vₜ, AddModal (|++> P) P (Φ vₛ vₜ)) as _ by tc_solve then (
        idtac
      ) else (
        eapply tac_bisimv_cupd
      )
    ).

Ltac bisim_bupd :=
  on_bisim_or_bisimv
    ltac:(fun _ _ Φ _ _ =>
      tryif assert (∀ P eₛ eₜ, AddModal (|==> P) P (Φ eₛ eₜ)) as _ by tc_solve then (
        idtac
      ) else (
        eapply tac_bisim_bupd
      )
    )
    ltac:(fun _ _ Φ _ _ =>
      tryif assert (∀ P vₛ vₜ, AddModal (|==> P) P (Φ vₛ vₜ)) as _ by tc_solve then (
        idtac
      ) else (
        eapply tac_bisimv_bupd
      )
    ).

Ltac bisim_post_simple :=
  on_bisim_or_bisimv
    ltac:(fun _ _ _ _ _ =>
      eapply tac_bisim_post
    )
    ltac:(fun _ _ _ _ _ =>
      eapply tac_bisimv_post;
      [ reflexivity
      | reflexivity
      | idtac
      ]
    ).
Ltac bisim_post :=
  bisim_simpl;
  bisim_cupd;
  bisim_post_simple;
  try iSmash+.

Tactic Notation "bisim_finish" tactic3(helper) :=
  try done;
  bisim_eval (simpl; rewrite ?fill_empty; helper);
  on_bisim_or_bisimv
    ltac:(fun _ _ _ eₛ eₜ =>
      tryif expr_is_val eₛ; expr_is_val eₜ then (
        bisim_post
      ) else (
        try solve [bisim_post]
      )
    )
    ltac:(fun _ _ _ _ _ =>
      try bisim_post
    );
  pm_prettify.

#[global] Instance bisim_finisher_option : TacticFlag "bisim_finisher" | 100 :=
  {| tactic_flag := true |}.
Tactic Notation "bisim_finisher" tactic3(helper) :=
  lazymatch tactic_flag_get "bisim_finisher" with
  | true =>
      bisim_finish helper
  | _ =>
      idtac
  end.

Tactic Notation "bisim_bind_coreₛ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    on_bisim_or_bisimv
      ltac:(fun _ _ _ _ _ => eapply (tac_bisim_bindₛ _ _ _ K))
      ltac:(fun _ _ _ _ _ => eapply (tac_bisimv_bindₛ _ _ _ K));
    [ simpl; reflexivity
    | pm_prettify; bisim_simpl_post
    ]
  ).
Tactic Notation "bisim_bind_coreₜ" open_constr(K) :=
  tryif ectx_is_empty K then (
    idtac
  ) else (
    on_bisim_or_bisimv
      ltac:(fun _ _ _ _ _ => eapply (tac_bisim_bindₜ _ _ _ _ K))
      ltac:(fun _ _ _ _ _ => eapply (tac_bisimv_bindₜ _ _ _ _ K));
    [ simpl; reflexivity
    | pm_prettify; bisim_simpl_post
    ]
  ).
Tactic Notation "bisim_bind_core" open_constr(Kₛ) open_constr(Kₜ) :=
  tryif ectx_is_empty Kₛ then (
    bisim_bind_coreₜ Kₜ
  ) else (
    tryif ectx_is_empty Kₜ then (
      bisim_bind_coreₛ Kₛ
    ) else (
      on_bisim_or_bisimv
        ltac:(fun _ _ _ _ _ => eapply (tac_bisim_bind _ _ _ Kₛ _ _ Kₜ))
        ltac:(fun _ _ _ _ _ => eapply (tac_bisimv_bind _ _ _ Kₛ _ _ Kₜ));
      [ simpl; reflexivity
      | simpl; reflexivity
      | pm_prettify; bisim_simpl_post
      ]
    )
  ).

Tactic Notation "bisim_pure_coreₛ" open_constr(K) :=
  on_bisim ltac:(fun _ _ _ _ _ =>
    eapply (tac_bisim_pure_execₛ _ _ _ _ _ K)
  );
  [ tc_solve
  | try done
  | idtac
  ].
Tactic Notation "bisim_pure_coreₜ" open_constr(K) :=
  on_bisim ltac:(fun _ _ _ _ _ =>
    eapply (tac_bisim_pure_execₜ _ _ _ _ _ _ K)
  );
  [ tc_solve
  | try done
  | idtac
  ].
