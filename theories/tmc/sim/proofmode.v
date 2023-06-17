From iris.proofmode Require Import
  coq_tactics
  reduction.

From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.program_logic Require Export
  sim.proofmode.
From simuliris.tmc Require Export
  sim.basic_rules.
From simuliris.tmc Require Import
  sim.notations.

Section sim.
  Context `{sim_programs : !SimPrograms ectx_language ectx_language}.
  Context `{sim_GS : !SimGS Σ}.
  Implicit Types constr : constructor.
  Implicit Types l lₜ lₛ : loc.
  Implicit Types idx idxₜ idxₛ : index.
  Implicit Types v vₜ vₛ : val.
  Implicit Types e eₜ eₛ : expr.
  Implicit Types K Kₜ Kₛ : ectx.
  Implicit Types Φ : val → val → iProp Σ.

  Lemma tac_simv_heap_bij_insert id1 p1 id2 lₛ lₜ P Δ :
    (∀ Q, AddModal (|++> Q) Q P) →
    envs_lookup id1 Δ = Some (p1, lₛ ⋈ lₜ)%I →
    match envs_replace id1 p1 true (Esnoc Enil id2 (lₛ ≈ lₜ)) Δ with
    | None =>
        False
    | Some Δ' =>
        envs_entails Δ' P
    end →
    envs_entails Δ P.
  Proof.
    rewrite envs_entails_unseal => HP Hlookup H.
    destruct (envs_replace _ _ _ _ _) as [Δ' |] eqn:HΔ'; last done.
    rewrite envs_replace_singleton_sound //.
    rewrite H.
    rewrite bi.intuitionistically_if_elim /= -bi.intuitionistic.
    setoid_rewrite sim_state_interp_heap_bij_insert. rewrite add_modal //.
  Qed.

  Context (X : sim_protocol Σ).

  Lemma tac_simv_constr_detₛ id0 id1 id2 K constr v1 v2 e Φ Δ :
    ( ∀ l,
      match
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id2 ((l +ₗ 2) ↦ₛ v2))
          id1 ((l +ₗ 1) ↦ₛ v1))
          id0 ((l +ₗ 0) ↦ₛ constr)
        ) Δ
      with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (SIM K @@ #l ≳ e [[ X ]] [[ Φ ]])
      end
    ) →
    envs_entails Δ (SIM K @@ &&constr v1 v2 ≳ e [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hsim.
    rewrite -sim_bindₛ -sim_constr_detₛ. setoid_rewrite <- sim_bind_invₛ.
    apply bi.forall_intro => l. specialize (Hsim l).
    destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    rewrite envs_app_sound // /= right_id Hsim.
    iIntros "H Hl0 Hl1 Hl2". iApply ("H" with "[$Hl0 $Hl1 $Hl2]").
  Qed.
  Lemma tac_simv_constr_detₜ id0 id1 id2 e K constr v1 v2 Φ Δ :
    ( ∀ l,
      match
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id2 ((l +ₗ 2) ↦ₜ v2))
          id1 ((l +ₗ 1) ↦ₜ v1))
          id0 ((l +ₗ 0) ↦ₜ constr)
        ) Δ
      with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (SIM e ≳ K @@ #l [[ X ]] [[ Φ ]])
      end
    ) →
    envs_entails Δ (SIM e ≳ K @@ &&constr v1 v2 [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hsim.
    rewrite -sim_bindₜ -sim_constr_detₜ.
    apply bi.forall_intro => l. specialize (Hsim l).
    destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    rewrite envs_app_sound // /= right_id Hsim sim_bind_invₜ.
    iIntros "H Hl0 Hl1 Hl2". iApply ("H" with "[$Hl0 $Hl1 $Hl2]").
  Qed.
  Lemma tac_simv_constr_det id constr Kₛ vₛ1 vₛ2 Kₜ vₜ1 vₜ2 Φ Δ :
    envs_entails Δ (vₛ1 ≈ vₜ1) →
    envs_entails Δ (vₛ2 ≈ vₜ2) →
    ( ∀ lₛ lₜ,
      match envs_app true (Esnoc Enil id (Loc lₛ ≈ Loc lₜ)) Δ with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (SIM Kₛ @@ #lₛ ≳ Kₜ @@ #lₜ [[ X ]] [[ Φ ]])
      end
    ) →
    envs_entails Δ (SIM Kₛ @@ &&constr vₛ1 vₛ2 ≳ Kₜ @@ &&constr vₜ1 vₜ2 [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hv1 Hv2 Hsim.
    iIntros "HΔ".
    iDestruct (Hv1 with "HΔ") as "#Hv1".
    iDestruct (Hv2 with "HΔ") as "#Hv2".
    iApply sim_bind.
    iApply (sim_constr_det with "Hv1 Hv2"). iIntros "%lₛ %lₜ #Hl !>".
    specialize (Hsim lₛ lₜ). destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    iApply Hsim.
    iApply (envs_app_sound with "HΔ"); first done. simpl. auto with iFrame.
  Qed.

  Lemma tac_simv_constrₛ1 K constr e1 e2 e Φ Δ :
    envs_entails Δ (SIM K @@ let: e1 in let: e2.[ren (+1)] in &&constr $1 $0 ≳ e [[ X ]] [[ Φ ]]) →
    envs_entails Δ (SIM K @@ &constr e1 e2 ≳ e [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal sim_bind_invₛ sim_constrₛ1 sim_bindₛ //.
  Qed.
  Lemma tac_simv_constrₛ2 K constr e1 e2 e Φ Δ :
    envs_entails Δ (SIM K @@ let: e2 in let: e1.[ren (+1)] in &&constr $0 $1 ≳ e [[ X ]] [[ Φ ]]) →
    envs_entails Δ (SIM K @@ &constr e1 e2 ≳ e [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal sim_bind_invₛ sim_constrₛ2 sim_bindₛ //.
  Qed.
  Lemma tac_simv_constrₜ e K constr e1 e2 Φ Δ :
    envs_entails Δ (SIM e ≳ K @@ let: e1 in let: e2.[ren (+1)] in &&constr $1 $0 [[ X ]] [[ Φ ]]) →
    envs_entails Δ (SIM e ≳ K @@ let: e2 in let: e1.[ren (+1)] in &&constr $0 $1 [[ X ]] [[ Φ ]]) →
    envs_entails Δ (SIM e ≳ K @@ &constr e1 e2 [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hsim1 Hsim2.
    rewrite -sim_bindₜ -sim_constrₜ -!sim_bind_invₜ.
    apply bi.and_intro; done.
  Qed.

  Lemma tac_simv_loadₛ id p K l idx v e Φ Δ :
    envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₛ v)%I →
    envs_entails Δ (SIM K @@ #v ≳ e [[ X ]] [[ Φ ]]) →
    envs_entails Δ (SIM K @@ ![idx] l ≳ e [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hlookup Hsim.
    rewrite envs_lookup_split // -sim_bindₛ Hsim.
    destruct p; simpl;
      [iIntros "(#Hl & Hsim)" | iIntros "(Hl & Hsim)"];
      iApply (sim_loadₛ with "Hl"); iIntros;
      iApply sim_bind_invₛ;
      iApply ("Hsim" with "[$]").
  Qed.
  Lemma tac_simv_loadₜ id p e K l idx v Φ Δ :
    envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₜ v)%I →
    envs_entails Δ (SIM e ≳ K @@ #v [[ X ]] [[ Φ ]]) →
    envs_entails Δ (SIM e ≳ K @@ ![idx] l [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hlookup Hsim.
    rewrite envs_lookup_split // -sim_bindₜ Hsim.
    destruct p; simpl;
      [iIntros "(#Hl & Hsim)" | iIntros "(Hl & Hsim)"];
      iApply (sim_loadₜ with "Hl"); iIntros;
      iApply sim_bind_invₜ;
      iApply ("Hsim" with "[$]").
  Qed.
  Lemma tac_simv_load id Kₛ lₛ idxₛ Kₜ lₜ idxₜ Φ Δ :
    envs_entails Δ (Loc lₛ ≈ Loc lₜ) →
    envs_entails Δ (Index idxₛ ≈ Index idxₜ) →
    ( ∀ vₛ vₜ,
      match envs_app true (Esnoc Enil id (vₛ ≈ vₜ)) Δ with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (SIM Kₛ @@ #vₛ ≳ Kₜ @@ #vₜ [[ X ]] [[ Φ ]])
      end
    ) →
    envs_entails Δ (SIM Kₛ @@ ![idxₛ] lₛ ≳ Kₜ @@ ![idxₜ] lₜ [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hl Hidx Hsim.
    iIntros "HΔ".
    iDestruct (Hl with "HΔ") as "#Hl".
    iDestruct (Hidx with "HΔ") as "#Hidx".
    iApply sim_bind.
    iApply (sim_load with "Hl Hidx"). iIntros "%vₛ %vₜ #Hv".
    specialize (Hsim vₛ vₜ). destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    iApply sim_bind_inv. iApply Hsim.
    iApply (envs_app_singleton_sound with "[HΔ] [Hv]"); naive_solver.
  Qed.

  Lemma tac_simv_storeₛ id p K l idx v w e Φ Δ :
    envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₛ w)%I →
    match envs_replace id p false (Esnoc Enil id ((l +ₗ idx) ↦ₛ v)) Δ with
    | None =>
        False
    | Some Δ' =>
        envs_entails Δ' (SIM K @@ #() ≳ e [[ X ]] [[ Φ ]])
    end →
    envs_entails Δ (SIM K @@ #l <-[idx]- v ≳ e [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hlookup Hsim.
    destruct (envs_replace _ _ _ _) as [Δ' |] eqn:HΔ'; last done.
    rewrite envs_replace_singleton_sound // Hsim.
    rewrite bi.intuitionistically_if_elim /=.
    rewrite sim_bind_invₛ -sim_bindₛ. apply bi.wand_elim_l', sim_storeₛ.
  Qed.
  Lemma tac_simv_storeₜ id p e K l idx v w Φ Δ :
    envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₜ w)%I →
    match envs_replace id p false (Esnoc Enil id ((l +ₗ idx) ↦ₜ v)) Δ with
    | None =>
        False
    | Some Δ' =>
        envs_entails Δ' (SIM e ≳ K @@ #() [[ X ]] [[ Φ ]])
    end →
    envs_entails Δ (SIM e ≳ K @@ #l <-[idx]- v [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hlookup Hsim.
    destruct (envs_replace _ _ _ _) as [Δ' |] eqn:HΔ'; last done.
    rewrite envs_replace_singleton_sound // Hsim.
    rewrite bi.intuitionistically_if_elim /=.
    rewrite sim_bind_invₜ -sim_bindₜ. apply bi.wand_elim_l', sim_storeₜ.
  Qed.
  Lemma tac_simv_store Kₛ vₛ1 vₛ2 vₛ3 Kₜ vₜ1 vₜ2 vₜ3 Φ Δ :
    envs_entails Δ (vₛ1 ≈ vₜ1) →
    envs_entails Δ (vₛ2 ≈ vₜ2) →
    envs_entails Δ (vₛ3 ≈ vₜ3) →
    envs_entails Δ (SIM Kₛ @@ #() ≳ Kₜ @@ #() [[ X ]] [[ Φ ]]) →
    envs_entails Δ (SIM Kₛ @@ vₛ1 <-[vₛ2]- vₛ3 ≳ Kₜ @@ vₜ1 <-[vₜ2]- vₜ3 [[ X ]] [[ Φ ]]).
  Proof.
    rewrite definition.simv_unseal /definition.simv_def.
    rewrite envs_entails_unseal => Hv1 Hv2 Hv3 Hsim.
    iIntros "HΔ".
    iDestruct (Hv1 with "HΔ") as "#Hv1".
    iDestruct (Hv2 with "HΔ") as "#Hv2".
    iDestruct (Hv3 with "HΔ") as "#Hv3".
    iApply sim_bind. iApply (sim_store with "Hv1 Hv2 Hv3"). iApply (Hsim with "HΔ").
  Qed.
End sim.

(* #[local] *)
Ltac expr_decompose e tac :=
  let rec go K e :=
    let go k e := go (k :: K) e in
    match e with
    | Let ?e1 ?e2 =>
        go (EctxiLet e2) e1
    | Call ?e1 (Val ?v2) =>
        go (EctxiCall2 v2) e1
    | Call ?e1 ?e2 =>
        go (EctxiCall1 e1) e2
    | Unop ?op ?e =>
        go (EctxiUnop op) e
    | Binop ?op ?e1 (Val ?v2) =>
        go (EctxiBinop2 op v2) e1
    | Binop ?op ?e1 ?e2 =>
        go (EctxiBinop1 op e1) e2
    | If ?e0 ?e1 ?e2 =>
        go (EctxiIf e1 e2) e0
    | Load ?e1 (Val ?v2) =>
        go (EctxiLoad2 v2) e1
    | Load ?e1 ?e2 =>
        go (EctxiLoad1 e1) e2
    | Store ?e1 (Val ?v2) (Val ?v3) =>
        go (EctxiStore3 v2 v3) e1
    | Store ?e1 ?e2 (Val ?v3) =>
        go (EctxiStore2 e1 v3) e2
    | Store ?e1 ?e2 ?e3 =>
        go (EctxiStore1 e1 e2) e3
    | _ =>
        tac K e
    end
  in
  go (∅ : ectx) e.
(* #[local] *)
Tactic Notation "expr_decompose" "[" open_constr(eₛ) open_constr(eₜ) "]" tactic3(tac) :=
  expr_decompose eₛ ltac:(fun Kₛ eₛ' =>
    expr_decompose eₜ ltac:(fun Kₜ eₜ' =>
      tac Kₛ eₛ' Kₜ eₜ'
    )
  ).

Tactic Notation "simv_finish" :=
  simv_finish with asimpl.

Ltac simv_asimpl :=
  simv_eval (asimpl; simpl).
Ltac simv_asimplₛ :=
  simv_evalₛ (asimpl; simpl).
Ltac simv_asimplₜ :=
  simv_evalₜ (asimpl; simpl).

(* #[local] *)
Ltac simv_focalizeₛ e_foc tac_succ tac_fail :=
  on_simv ltac:(fun _ _ _ e _ =>
    tryif
      expr_decompose e ltac:(fun K e' =>
        unify e' e_foc;
        tac_succ K
      )
    then idtac else (
      tac_fail e
    )
  ).
(* #[local] *)
Ltac simv_focalizeₜ e_foc tac_succ tac_fail :=
  on_simv ltac:(fun _ _ _ _ e =>
    tryif
      expr_decompose e ltac:(fun K e' =>
        unify e' e_foc;
        tac_succ K
      )
    then idtac else (
      tac_fail e
    )
  ).
(* #[local] *)
Ltac simv_focalize e_focₛ e_focₜ tac_succ tac_fail :=
  on_simv ltac:(fun _ _ _ eₛ eₜ =>
    tryif
      expr_decompose eₛ ltac:(fun Kₛ eₛ' =>
        unify eₛ' e_focₛ;
        expr_decompose eₜ ltac:(fun Kₜ eₜ' =>
          unify eₜ' e_focₜ;
          tac_succ Kₛ Kₜ
        )
      )
    then idtac else (
      tac_fail eₛ eₜ
    )
  ).

Tactic Notation "simv_bindₛ" open_constr(e_foc) :=
  simv_focalizeₛ e_foc
    ltac:(fun K =>
      simv_bind_coreₛ K
    )
    ltac:(fun e =>
      fail "simv_bindₛ: cannot find" e_foc "in source" e
    ).
Tactic Notation "simv_bindₛ" :=
  simv_bindₛ _.
Tactic Notation "simv_bindₜ" open_constr(e_foc) :=
  simv_focalizeₜ e_foc
    ltac:(fun K =>
      simv_bind_coreₜ K
    )
    ltac:(fun e =>
      fail "simv_bindₜ: cannot find" e_foc "in target" e
    ).
Tactic Notation "simv_bindₜ" :=
  simv_bindₜ _.
Tactic Notation "simv_bind" open_constr(e_focₛ) open_constr(e_focₜ) :=
  on_simv ltac:(fun _ _ _ eₛ eₜ =>
    let Kₛ := open_constr:(_) in
    expr_decompose eₛ ltac:(fun Kₛ' eₛ' =>
      unify eₛ' e_focₛ;
      unify Kₛ' Kₛ
    );
    let Kₜ := open_constr:(_) in
    expr_decompose eₜ ltac:(fun Kₜ' eₜ' =>
      unify eₜ' e_focₜ;
      unify Kₜ' Kₜ
    );
    simv_bind_core Kₛ Kₜ
  ).
Tactic Notation "simv_bind" :=
  simv_bind _ _.

Tactic Notation "simv_pureₛ" open_constr(e_foc) :=
  simv_focalizeₛ e_foc
    ltac:(fun K =>
      simv_pure_coreₛ K
    )
    ltac:(fun e =>
      fail "simv_pureₛ: cannot find" e_foc "in source" e "or" e_foc "is not a redex"
    ).
Tactic Notation "simv_pureₛ" :=
  simv_pureₛ _.
Ltac simv_puresₛ :=
  repeat (simv_pureₛ; []) || simv_finish.
Tactic Notation "simv_pureₜ" open_constr(e_foc) :=
  simv_focalizeₜ e_foc
    ltac:(fun K =>
      simv_pure_coreₜ K
    )
    ltac:(fun e =>
      fail "simv_pureₜ: cannot find" e_foc "in target" e "or" e_foc "is not a redex"
    ).
Tactic Notation "simv_pureₜ" :=
  simv_pureₜ _.
Ltac simv_puresₜ :=
  repeat (simv_pureₜ; []) || simv_finish.
Ltac simv_pures :=
  simv_puresₜ; simv_puresₛ.

#[local] Ltac simv_heap_bij_insert_core Htie Hsimilar :=
  iStartProof;
  eapply (tac_simv_heap_bij_insert Htie _ Hsimilar);
  [ iSolveTC
  | iAssumptionCore ||
    tryif is_evar Htie then (
      fail "simv_heap_bij_insert: cannot find ? ⋈ ?"
    ) else (
      fail "simv_heap_bij_insert: cannot find" Htie ": ? ⋈ ?"
    )
  | pm_reduce;
    tryif goal_is_false then (
      fail "simv_heap_bij_insert:" Hsimilar "not fresh"
    ) else (
      try simv_finish
    )
  ].
Tactic Notation "simv_heap_bij_insert" open_constr(Htie) "as" constr(Hsimilar) :=
  simv_heap_bij_insert_core Htie Hsimilar.
Tactic Notation "simv_heap_bij_insert" open_constr(Htie) :=
  simv_heap_bij_insert Htie as Htie.
Tactic Notation "simv_heap_bij_insert" "as" constr(Hsimilar) :=
  simv_heap_bij_insert _ as Hsimilar.
Tactic Notation "simv_heap_bij_insert" :=
  let Hsimilar := iFresh in
  simv_heap_bij_insert as Hsimilar.

Tactic Notation "simv_constr_detₛ" "as" simple_intropattern(l) constr(Hl0) constr(Hl1) constr(Hl2) :=
  simv_pures;
  let e_foc := open_constr:(ConstrDet _ (Val _) (Val _)) in
  simv_focalizeₛ e_foc
    ltac:(fun K =>
      eapply (tac_simv_constr_detₛ _ Hl0 Hl1 Hl2 K)
    )
    ltac:(fun e =>
      fail "simv_constr_detₛ: cannot find" e_foc "in source" e
    );
  tryif intros l then idtac else (
    fail "simv_constr_detₛ:" l "not fresh"
  );
  pm_reduce;
  tryif goal_is_false then (
    fail "simv_constr_detₛ:" Hl0 "or" Hl1 "or" Hl2 "not fresh"
  ) else (
    simv_finish
  ).
Tactic Notation "simv_constr_detₛ" "as" simple_intropattern(l) :=
  let Hl0 := iFresh in
  let Hl1 := iFresh in
  let Hl2 := iFresh in
  simv_constr_detₛ as l Hl0 Hl1 Hl2.
Tactic Notation "simv_constr_detₛ" :=
  let l := fresh "lₛ" in
  simv_constr_detₛ as l.
Tactic Notation "simv_constr_detₜ" "as" simple_intropattern(l) constr(Hl0) constr(Hl1) constr(Hl2) :=
  simv_pures;
  let e_foc := open_constr:(ConstrDet _ (Val _) (Val _)) in
  simv_focalizeₜ e_foc
    ltac:(fun K =>
      eapply (tac_simv_constr_detₜ _ Hl0 Hl1 Hl2 _ K)
    )
    ltac:(fun e =>
      fail "simv_constr_detₜ: cannot find" e_foc "in target" e
    );
  tryif intros l then idtac else (
    fail "simv_constr_detₜ:" l "not fresh"
  );
  pm_reduce;
  tryif goal_is_false then (
    fail "simv_constr_detₜ:" Hl0 "or" Hl1 "or" Hl2 "not fresh"
  ) else (
    simv_finish
  ).
Tactic Notation "simv_constr_detₜ" "as" simple_intropattern(l) :=
  let Hl0 := iFresh in
  let Hl1 := iFresh in
  let Hl2 := iFresh in
  simv_constr_detₜ as l Hl0 Hl1 Hl2.
Tactic Notation "simv_constr_detₜ" :=
  let l := fresh "lₜ" in
  simv_constr_detₜ as l.
Tactic Notation "simv_constr_det" "as" simple_intropattern(lₛ) simple_intropattern(lₜ) constr(Hl) :=
  simv_pures;
  let e_focₛ := open_constr:(ConstrDet _ (Val _) (Val _)) in
  let e_focₜ := open_constr:(ConstrDet _ (Val _) (Val _)) in
  simv_focalize e_focₛ e_focₜ
    ltac:(fun Kₛ Kₜ =>
      eapply (tac_simv_constr_det _ Hl _ Kₛ _ _ Kₜ)
    )
    ltac:(fun eₛ eₜ =>
      fail "simv_constr_det: cannot find" e_focₛ "in source" eₛ "or" e_focₜ "in target" eₜ
    );
  [ try done
  | try done
  | tryif intros lₛ then (
      tryif intros lₜ then (
        pm_reduce;
        tryif goal_is_false then (
          fail "simv_constr_det:" Hl "not fresh"
        ) else (
          simv_finish
        )
      ) else (
        fail "simv_constr_det:" lₜ "not fresh"
      )
    ) else (
      fail "simv_constr_det:" lₛ "not fresh"
    )
  ].
Tactic Notation "simv_constr_det" "as" simple_intropattern(lₛ) simple_intropattern(lₜ) :=
  let Hl := iFresh in
  simv_constr_det as lₜ lₛ Hl.
Tactic Notation "simv_constr_det" :=
  simv_constr_det as ? ?.

Ltac simv_constrₛ1 :=
  simv_pures;
  let e_foc := open_constr:(Constr _ _ _) in
  simv_focalizeₛ e_foc
    ltac:(fun K =>
      eapply (tac_simv_constrₛ1 _ K)
    )
    ltac:(fun e =>
      fail "simv_constrₛ1: cannot find" e_foc "in source" e
    );
  simv_finish.
Ltac simv_constrₛ2 :=
  simv_pures;
  let e_foc := open_constr:(Constr _ _ _) in
  simv_focalizeₛ e_foc
    ltac:(fun K =>
      eapply (tac_simv_constrₛ2 _ K)
    )
    ltac:(fun e =>
      fail "simv_constrₛ2: cannot find" e_foc "in source" e
    );
  simv_finish.
Ltac simv_constrₜ :=
  simv_pures;
  let e_foc := open_constr:(Constr _ _ _) in
  simv_focalizeₜ e_foc
    ltac:(fun K =>
      eapply (tac_simv_constrₜ _ _ K)
    )
    ltac:(fun e =>
      fail "simv_constrₜ: cannot find" e_foc "in target" e
    );
  simv_finish.

Tactic Notation "simv_loadₛ" :=
  simv_pures;
  let e_foc := open_constr:(Load (Val (Loc _)) (Val (Index _))) in
  simv_focalizeₛ e_foc
    ltac:(fun K =>
      eapply (tac_simv_loadₛ _ _ _ K)
    )
    ltac:(fun e =>
      fail "simv_loadₛ: cannot find" e_foc "in source" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₛ ?l _ _) => l end in
    fail "simv_loadₛ: cannot find" l "↦ₛ ?"
  | simv_finish
  ].
Tactic Notation "simv_loadₜ" :=
  simv_pures;
  let e_foc := open_constr:(Load (Val (Loc _)) (Val (Index _))) in
  simv_focalizeₜ e_foc
    ltac:(fun K =>
      eapply (tac_simv_loadₜ _ _ _ _ K)
    )
    ltac:(fun e =>
      fail "simv_loadₜ: cannot find" e_foc "in target" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₜ ?l _ _) => l end in
    fail "simv_loadₜ: cannot find" l "↦ₜ ?"
  | simv_finish
  ].
Tactic Notation "simv_load" "as" simple_intropattern(vₛ) simple_intropattern(vₜ) constr(Hv) :=
  simv_pures;
  let e_focₛ := open_constr:(Load (Val (Loc _)) (Val (Index _))) in
  let e_focₜ := open_constr:(Load (Val (Loc _)) (Val (Index _))) in
  simv_focalize e_focₛ e_focₜ
    ltac:(fun Kₛ Kₜ =>
      eapply (tac_simv_load _ Hv Kₛ _ _ Kₜ)
    )
    ltac:(fun eₛ eₜ =>
      fail "simv_load: cannot find" e_focₛ "in source" eₛ "or" e_focₜ "in target" eₜ
    );
  [ try done
  | try done
  | tryif intros vₛ then (
      tryif intros vₜ then (
        pm_reduce;
        tryif goal_is_false then (
          fail "simv_load:" Hv "not fresh"
        ) else (
          simv_finish
        )
      ) else (
        fail "simv_load:" vₜ "not fresh"
      )
    ) else (
      fail "simv_load:" vₛ "not fresh"
    )
  ].
Tactic Notation "simv_load" "as" simple_intropattern(vₛ) simple_intropattern(vₜ) :=
  let Hv := iFresh in
  simv_load as vₛ vₜ Hv.
Tactic Notation "simv_load" :=
  simv_load as ? ?.

Ltac simv_storeₛ :=
  simv_pures;
  let e_foc := open_constr:(Store (Val (Loc _)) (Val (Index _)) (Val _)) in
  simv_focalizeₛ e_foc
    ltac:(fun K =>
      eapply (tac_simv_storeₛ _ _ _ K)
    )
    ltac:(fun e =>
      fail "simv_storeₛ: cannot find" e_foc "in source" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₛ ?l _ _) => l end in
    fail "simv_storeₛ: cannot find" l "↦ₛ ?"
  | pm_reduce; simv_finish
  ].
Ltac simv_storeₜ :=
  simv_pures;
  let e_foc := open_constr:(Store (Val (Loc _)) (Val (Index _)) (Val _)) in
  simv_focalizeₜ e_foc
    ltac:(fun K =>
      eapply (tac_simv_storeₜ _ _ _ _ K)
    )
    ltac:(fun e =>
      fail "simv_storeₜ: cannot find" e_foc "in source" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₜ ?l _ _) => l end in
    fail "simv_storeₜ: cannot find" l "↦ₜ ?"
  | pm_reduce; simv_finish
  ].
Ltac simv_store :=
  simv_pures;
  let e_focₜ := open_constr:(Store (Val (Loc _)) (Val (Index _)) (Val _)) in
  let e_focₛ := open_constr:(Store (Val (Loc _)) (Val (Index _)) (Val _)) in
  simv_focalize e_focₜ e_focₛ
    ltac:(fun Kₛ Kₜ =>
      eapply (tac_simv_store _ Kₛ _ _ _ Kₜ)
    )
    ltac:(fun eₛ eₜ =>
      fail "simv_store: cannot find" e_focₛ "in source" eₛ "or" e_focₜ "in target" eₜ
    );
  [ try done
  | try done
  | try done
  | simv_finish
  ].

Tactic Notation "simv_apply" open_constr(H) :=
  on_simv ltac:(fun _ _ _ eₛ eₜ =>
    tryif
      iPoseProofCore H as false ltac:(fun H =>
        expr_decompose [eₛ eₜ] ltac:(fun Kₛ _ Kₜ _ =>
          simv_bind_core Kₛ Kₜ;
          iApplyHyp H;
          try done
        )
      )
    then idtac else (
      let P := type of H in
      fail "simv_apply: cannot apply" H ":" P
    )
  ).
Tactic Notation "simv_smart_apply" open_constr(H) :=
  simv_pures;
  simv_apply H.

Tactic Notation "simv_mono" open_constr(H) :=
  on_simv ltac:(fun _ _ _ eₛ eₜ =>
    tryif
      iPoseProofCore H as false ltac:(fun H =>
        expr_decompose [eₛ eₜ] ltac:(fun Kₛ _ Kₜ _ =>
          simv_bind_core Kₛ Kₜ;
          let H_sel :=
            open_constr:(
              spec_patterns.SGoal (
                spec_patterns.SpecGoal
                  spec_patterns.GSpatial false [] [H] false
              )
            )
          in
          iApply (simv_mono' with H_sel);
          [ iApplyHyp H; try done
          | try solve [done | iIntros "% % ? //"]
          ]
        )
      )
    then idtac else (
      let P := type of H in
      fail "simv_mono: cannot apply" H ":" P
    )
  ).
Tactic Notation "simv_smart_mono" open_constr(H) :=
  simv_pures;
  simv_mono H.
