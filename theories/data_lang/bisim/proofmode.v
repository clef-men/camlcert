From iris.proofmode Require Import
  coq_tactics
  reduction.

From simuliris Require Import
  prelude.
From simuliris.program_logic Require Export
  bisim.proofmode.
From simuliris.data_lang Require Export
  (* FIXME: remove this dependency *)
  sim.proofmode
  bisim.basic_rules.
From simuliris.data_lang Require Import
  bisim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms data_ectx_lang data_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Context (Χ : sim_protocol Σ).
  Implicit Types tag : data_tag.
  Implicit Types l lₜ lₛ : loc.
  Implicit Types idx idxₜ idxₛ : data_index.
  Implicit Types v vₜ vₛ : data_val.
  Implicit Types e eₜ eₛ : data_expr.
  Implicit Types K Kₜ Kₛ : data_ectx.
  Implicit Types Φ : data_expr → data_expr → iProp Σ.

  Lemma tac_bisim_binopₛ Δ Φ K op e1 e2 e :
    envs_entails Δ (BISIM K @@ let: e1 in let: e2.[ren (+1)] in DataBinopDet op $1 $0 ≃ e [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM K @@ let: e2 in let: e1.[ren (+1)] in DataBinopDet op $0 $1 ≃ e [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM K @@ DataBinop op e1 e2 ≃ e [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hbisim1 Hbisim2.
    rewrite -bisim_bindₛ -bisim_binopₛ -!bisim_bind_invₛ.
    apply bi.and_intro; done.
  Qed.
  Lemma tac_bisim_binopₜ Δ Φ e K op e1 e2 :
    envs_entails Δ (BISIM e ≃ K @@ let: e1 in let: e2.[ren (+1)] in DataBinopDet op $1 $0 [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM e ≃ K @@ let: e2 in let: e1.[ren (+1)] in DataBinopDet op $0 $1 [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM e ≃ K @@ DataBinop op e1 e2 [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hbisim1 Hbisim2.
    rewrite -bisim_bindₜ -bisim_binopₜ -!bisim_bind_invₜ.
    apply bi.and_intro; done.
  Qed.

  Lemma tac_bisim_constrₛ Δ Φ K tag e1 e2 e :
    envs_entails Δ (BISIM K @@ let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 ≃ e [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM K @@ let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 ≃ e [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM K @@ &tag e1 e2 ≃ e [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hbisim1 Hbisim2.
    rewrite -bisim_bindₛ -bisim_constrₛ -!bisim_bind_invₛ.
    apply bi.and_intro; done.
  Qed.
  Lemma tac_bisim_constrₜ Δ Φ e K tag e1 e2 :
    envs_entails Δ (BISIM e ≃ K @@ let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM e ≃ K @@ let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM e ≃ K @@ &tag e1 e2 [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hbisim1 Hbisim2.
    rewrite -bisim_bindₜ -bisim_constrₜ -!bisim_bind_invₜ.
    apply bi.and_intro; done.
  Qed.

  Lemma tac_bisim_constr_detₛ Δ Φ id0 id1 id2 K tag v1 v2 e :
    ( ∀ l,
      match
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id2 ((l +ₗ 2) ↦ₛ v2))
          id1 ((l +ₗ 1) ↦ₛ v1))
          id0 ((l +ₗ 0) ↦ₛ tag)
        ) Δ
      with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (BISIM K @@ #l ≃ e [[ Χ ]] {{ Φ }})
      end
    ) →
    envs_entails Δ (BISIM K @@ &&tag v1 v2 ≃ e [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hbisim.
    rewrite -bisim_bindₛ -bisim_constr_detₛ. setoid_rewrite <- bisim_bind_invₛ.
    apply bi.forall_intro => l. specialize (Hbisim l).
    destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    rewrite envs_app_sound // /= right_id Hbisim.
    iIntros "H Hl0 Hl1 Hl2". iApply ("H" with "[$Hl0 $Hl1 $Hl2]").
  Qed.
  Lemma tac_bisim_constr_detₜ Δ Φ id0 id1 id2 e K tag v1 v2 :
    ( ∀ l,
      match
        envs_app false (Esnoc (Esnoc (Esnoc Enil
          id2 ((l +ₗ 2) ↦ₜ v2))
          id1 ((l +ₗ 1) ↦ₜ v1))
          id0 ((l +ₗ 0) ↦ₜ tag)
        ) Δ
      with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (BISIM e ≃ K @@ #l [[ Χ ]] {{ Φ }})
      end
    ) →
    envs_entails Δ (BISIM e ≃ K @@ &&tag v1 v2 [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hbisim.
    rewrite -bisim_bindₜ -bisim_constr_detₜ.
    apply bi.forall_intro => l. specialize (Hbisim l).
    destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    rewrite envs_app_sound // /= right_id Hbisim bisim_bind_invₜ.
    iIntros "H Hl0 Hl1 Hl2". iApply ("H" with "[$Hl0 $Hl1 $Hl2]").
  Qed.
  Lemma tac_bisim_constr_det Δ Φ id tag Kₛ vₛ1 vₛ2 Kₜ vₜ1 vₜ2 :
    envs_entails Δ (vₛ1 ≈ vₜ1) →
    envs_entails Δ (vₛ2 ≈ vₜ2) →
    ( ∀ lₛ lₜ,
      match envs_app true (Esnoc Enil id (DataLoc lₛ ≈ DataLoc lₜ)) Δ with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (BISIM Kₛ @@ #lₛ ≃ Kₜ @@ #lₜ [[ Χ ]] {{ Φ }})
      end
    ) →
    envs_entails Δ (BISIM Kₛ @@ &&tag vₛ1 vₛ2 ≃ Kₜ @@ &&tag vₜ1 vₜ2 [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hv1 Hv2 Hbisim.
    iIntros "HΔ".
    iDestruct (Hv1 with "HΔ") as "#Hv1".
    iDestruct (Hv2 with "HΔ") as "#Hv2".
    iApply bisim_bind.
    iApply (bisim_constr_det with "Hv1 Hv2"). iIntros "%lₛ %lₜ #Hl !>".
    specialize (Hbisim lₛ lₜ). destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    iApply Hbisim.
    iApply (envs_app_sound with "HΔ"); first done. naive_solver.
  Qed.

  Lemma tac_bisim_loadₛ Δ Φ id p K l idx v e :
    envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₛ v)%I →
    envs_entails Δ (BISIM K @@ #v ≃ e [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM K @@ ![idx] l ≃ e [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hlookup Hbisim.
    rewrite envs_lookup_split // -bisim_bindₛ Hbisim.
    destruct p; simpl;
      [iIntros "(#Hl & Hbisim)" | iIntros "(Hl & Hbisim)"];
      iApply (bisim_loadₛ with "Hl"); iIntros;
      iApply bisim_bind_invₛ; iSmash.
  Qed.
  Lemma tac_bisim_loadₜ Δ Φ id p e K l idx v :
    envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₜ v)%I →
    envs_entails Δ (BISIM e ≃ K @@ #v [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM e ≃ K @@ ![idx] l [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hlookup Hbisim.
    rewrite envs_lookup_split // -bisim_bindₜ Hbisim.
    destruct p; simpl;
      [iIntros "(#Hl & Hbisim)" | iIntros "(Hl & Hbisim)"];
      iApply (bisim_loadₜ with "Hl"); iIntros;
      iApply bisim_bind_invₜ; iSmash.
  Qed.
  Lemma tac_bisim_load Δ Φ id Kₛ lₛ idxₛ Kₜ lₜ idxₜ :
    envs_entails Δ (DataLoc lₛ ≈ DataLoc lₜ) →
    envs_entails Δ (DataIndex idxₛ ≈ DataIndex idxₜ) →
    ( ∀ vₛ vₜ,
      match envs_app true (Esnoc Enil id (vₛ ≈ vₜ)) Δ with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (BISIM Kₛ @@ #vₛ ≃ Kₜ @@ #vₜ [[ Χ ]] {{ Φ }})
      end
    ) →
    envs_entails Δ (BISIM Kₛ @@ ![idxₛ] lₛ ≃ Kₜ @@ ![idxₜ] lₜ [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hl Hidx Hbisim.
    iIntros "HΔ".
    iDestruct (Hl with "HΔ") as "#Hl".
    iDestruct (Hidx with "HΔ") as "#Hidx".
    iApply bisim_bind.
    iApply (bisim_load with "Hl Hidx"). iIntros "%vₛ %vₜ #Hv".
    specialize (Hbisim vₛ vₜ). destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
    iApply Hbisim.
    iApply (envs_app_singleton_sound with "[HΔ] [Hv]"); naive_solver.
  Qed.

  Lemma tac_bisim_storeₛ Δ Φ id p K l idx v w e :
    envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₛ w)%I →
    match envs_replace id p false (Esnoc Enil id ((l +ₗ idx) ↦ₛ v)) Δ with
    | None =>
        False
    | Some Δ' =>
        envs_entails Δ' (BISIM K @@ #() ≃ e [[ Χ ]] {{ Φ }})
    end →
    envs_entails Δ (BISIM K @@ #l <-[idx]- v ≃ e [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hlookup Hbisim.
    destruct (envs_replace _ _ _ _) as [Δ' |] eqn:HΔ'; last done.
    rewrite envs_replace_singleton_sound // Hbisim.
    rewrite bi.intuitionistically_if_elim /=.
    rewrite bisim_bind_invₛ -bisim_bindₛ.
    apply bi.wand_elim_l', bi.wand_entails, bisim_storeₛ.
  Qed.
  Lemma tac_bisim_storeₜ Δ Φ id p e K l idx v w :
    envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₜ w)%I →
    match envs_replace id p false (Esnoc Enil id ((l +ₗ idx) ↦ₜ v)) Δ with
    | None =>
        False
    | Some Δ' =>
        envs_entails Δ' (BISIM e ≃ K @@ #() [[ Χ ]] {{ Φ }})
    end →
    envs_entails Δ (BISIM e ≃ K @@ #l <-[idx]- v [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hlookup Hbisim.
    destruct (envs_replace _ _ _ _) as [Δ' |] eqn:HΔ'; last done.
    rewrite envs_replace_singleton_sound // Hbisim.
    rewrite bi.intuitionistically_if_elim /=.
    rewrite bisim_bind_invₜ -bisim_bindₜ.
    apply bi.wand_elim_l', bi.wand_entails, bisim_storeₜ.
  Qed.
  Lemma tac_bisim_store Δ Φ Kₛ vₛ1 vₛ2 vₛ3 Kₜ vₜ1 vₜ2 vₜ3 :
    envs_entails Δ (vₛ1 ≈ vₜ1) →
    envs_entails Δ (vₛ2 ≈ vₜ2) →
    envs_entails Δ (vₛ3 ≈ vₜ3) →
    envs_entails Δ (BISIM Kₛ @@ #() ≃ Kₜ @@ #() [[ Χ ]] {{ Φ }}) →
    envs_entails Δ (BISIM Kₛ @@ vₛ1 <-[vₛ2]- vₛ3 ≃ Kₜ @@ vₜ1 <-[vₜ2]- vₜ3 [[ Χ ]] {{ Φ }}).
  Proof.
    rewrite envs_entails_unseal => Hv1 Hv2 Hv3 Hbisim.
    iIntros "HΔ".
    iDestruct (Hv1 with "HΔ") as "#Hv1".
    iDestruct (Hv2 with "HΔ") as "#Hv2".
    iDestruct (Hv3 with "HΔ") as "#Hv3".
    iApply bisim_bind. iApply (bisim_store with "Hv1 Hv2 Hv3"). iApply (Hbisim with "HΔ").
  Qed.
End sim_GS.

#[local] Ltac expr_decompose_core e tac :=
  let rec go K e :=
    let go k e := go (k :: K) e in
    match e with
    | DataLet ?e1 ?e2 =>
        go (DataEctxiLet e2) e1
    | DataCall ?e1 (DataVal ?v2) =>
        go (DataEctxiCall2 v2) e1
    | DataCall ?e1 ?e2 =>
        go (DataEctxiCall1 e1) e2
    | DataUnop ?op ?e =>
        go (DataEctxiUnop op) e
    | DataIf ?e0 ?e1 ?e2 =>
        go (DataEctxiIf e1 e2) e0
    | DataLoad ?e1 (DataVal ?v2) =>
        go (DataEctxiLoad2 v2) e1
    | DataLoad ?e1 ?e2 =>
        go (DataEctxiLoad1 e1) e2
    | DataStore ?e1 (DataVal ?v2) (DataVal ?v3) =>
        go (DataEctxiStore3 v2 v3) e1
    | DataStore ?e1 ?e2 (DataVal ?v3) =>
        go (DataEctxiStore2 e1 v3) e2
    | DataStore ?e1 ?e2 ?e3 =>
        go (DataEctxiStore1 e1 e2) e3
    | _ =>
        tac K e
    end
  in
  go (∅ : data_ectx) e.
#[local] Ltac expr_decompose e tac :=
  let e := eval simpl in e in
  expr_decompose_core e tac.
#[local] Tactic Notation "expr_decompose" "[" open_constr(eₛ) open_constr(eₜ) "]" tactic3(tac) :=
  expr_decompose eₛ ltac:(fun Kₛ eₛ' =>
    expr_decompose eₜ ltac:(fun Kₜ eₜ' =>
      tac Kₛ eₛ' Kₜ eₜ'
    )
  ).

Tactic Notation "bisim_finish" :=
  bisim_finish asimpl.
Tactic Notation "bisim_finisher" :=
  bisim_finisher asimpl.

Ltac bisim_asimpl :=
  bisim_eval (asimpl; simpl).
Ltac bisim_asimplₛ :=
  bisim_evalₛ (asimpl; simpl).
Ltac bisim_asimplₜ :=
  bisim_evalₜ (asimpl; simpl).

#[local] Ltac bisim_focalizeₛ e_foc tac_succ tac_fail :=
  on_bisim ltac:(fun _ _ _ e _ =>
    tryif
      expr_decompose e ltac:(fun K e' =>
        unify e' e_foc;
        tac_succ K
      )
    then idtac else (
      tac_fail e
    )
  ).
#[local] Ltac bisim_focalizeₜ e_foc tac_succ tac_fail :=
  on_bisim ltac:(fun _ _ _ _ e =>
    tryif
      expr_decompose e ltac:(fun K e' =>
        unify e' e_foc;
        tac_succ K
      )
    then idtac else (
      tac_fail e
    )
  ).
#[local] Ltac bisim_focalize e_focₛ e_focₜ tac_succ tac_fail :=
  on_bisim ltac:(fun _ _ _ eₛ eₜ =>
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

Tactic Notation "bisim_bindₛ" open_constr(e_foc) :=
  bisim_focalizeₛ e_foc
    ltac:(fun K => bisim_bind_coreₛ K)
    ltac:(fun e => fail "bisim_bindₛ: cannot find" e_foc "in source" e).
Tactic Notation "bisim_bindₛ" :=
  bisim_bindₛ _.
Tactic Notation "bisim_bindₜ" open_constr(e_foc) :=
  bisim_focalizeₜ e_foc
    ltac:(fun K => bisim_bind_coreₜ K)
    ltac:(fun e => fail "bisim_bindₜ: cannot find" e_foc "in target" e).
Tactic Notation "bisim_bindₜ" :=
  bisim_bindₜ _.
Tactic Notation "bisim_bind" open_constr(e_focₛ) open_constr(e_focₜ) :=
  on_bisim ltac:(fun _ _ _ eₛ eₜ =>
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
    bisim_bind_core Kₛ Kₜ
  ).
Tactic Notation "bisim_bind" :=
  bisim_bind _ _.

#[local] Tactic Notation "bisim_pure_coreₛ" open_constr(e_foc) :=
  bisim_focalizeₛ e_foc
    ltac:(fun K => bisim_pure_coreₛ K)
    ltac:(fun e => fail "bisim_pureₛ: cannot find" e_foc "in source" e "or" e_foc "is not a redex").
Tactic Notation "bisim_pureₛ" open_constr(e_foc) :=
  bisim_pure_coreₛ e_foc; last bisim_finisher.
Tactic Notation "bisim_pureₛ" :=
  bisim_pureₛ _.
Ltac bisim_puresₛ :=
  repeat (bisim_pure_coreₛ _; []);
  bisim_finisher.
#[local] Tactic Notation "bisim_pure_coreₜ" open_constr(e_foc) :=
  bisim_focalizeₜ e_foc
    ltac:(fun K => bisim_pure_coreₜ K)
    ltac:(fun e => fail "bisim_pureₜ: cannot find" e_foc "in target" e "or" e_foc "is not a redex").
Tactic Notation "bisim_pureₜ" open_constr(e_foc) :=
  bisim_pure_coreₜ e_foc; last bisim_finisher.
Tactic Notation "bisim_pureₜ" :=
  bisim_pureₜ _.
Ltac bisim_puresₜ :=
  repeat (bisim_pure_coreₜ _; []);
  bisim_finisher.
Ltac bisim_pures :=
  bisim_puresₜ;
  bisim_puresₛ.

Ltac bisim_binopₛ :=
  bisim_puresₛ;
  let e_foc := open_constr:(DataBinop _ _ _) in
  bisim_focalizeₛ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_binopₛ _ _ _ K)
      )
    )
    ltac:(fun e =>
      fail "bisim_binopₛ: cannot find" e_foc "in source" e
    );
  bisim_finisher.
Ltac bisim_binopₜ :=
  bisim_puresₜ;
  let e_foc := open_constr:(DataBinop _ _ _) in
  bisim_focalizeₜ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_binopₜ _ _ _ _ K)
      )
    )
    ltac:(fun e =>
      fail "bisim_binopₜ: cannot find" e_foc "in target" e
    );
  bisim_finisher.

Ltac bisim_constrₛ :=
  bisim_puresₛ;
  let e_foc := open_constr:(DataConstr _ _ _) in
  bisim_focalizeₛ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_constrₛ _ _ _ K)
      )
    )
    ltac:(fun e =>
      fail "bisim_constrₛ: cannot find" e_foc "in source" e
    );
  bisim_finisher.
Ltac bisim_constrₜ :=
  bisim_puresₜ;
  let e_foc := open_constr:(DataConstr _ _ _) in
  bisim_focalizeₜ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_constrₜ _ _ _ _ K)
      )
    )
    ltac:(fun e =>
      fail "bisim_constrₜ: cannot find" e_foc "in target" e
    );
  bisim_finisher.

Tactic Notation "bisim_constr_detₛ" "as" simple_intropattern(l) constr(Hl0) constr(Hl1) constr(Hl2) :=
  bisim_puresₛ;
  let e_foc := open_constr:(DataConstrDet _ (DataVal _) (DataVal _)) in
  bisim_focalizeₛ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_constr_detₛ _ _ _ Hl0 Hl1 Hl2 K)
      )
    )
    ltac:(fun e =>
      fail "bisim_constr_detₛ: cannot find" e_foc "in source" e
    );
  tryif intros l then idtac else (
    fail "bisim_constr_detₛ:" l "not fresh"
  );
  pm_reduce;
  tryif goal_is_false then (
    fail "bisim_constr_detₛ:" Hl0 "or" Hl1 "or" Hl2 "not fresh"
  ) else (
    bisim_finisher
  ).
Tactic Notation "bisim_constr_detₛ" "as" simple_intropattern(l) :=
  let Hl0 := iFresh in
  let Hl1 := iFresh in
  let Hl2 := iFresh in
  bisim_constr_detₛ as l Hl0 Hl1 Hl2.
Tactic Notation "bisim_constr_detₛ" :=
  let l := fresh "lₛ" in
  bisim_constr_detₛ as l.
Tactic Notation "bisim_constr_detₜ" "as" simple_intropattern(l) constr(Hl0) constr(Hl1) constr(Hl2) :=
  bisim_puresₜ;
  let e_foc := open_constr:(DataConstrDet _ (DataVal _) (DataVal _)) in
  bisim_focalizeₜ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_constr_detₜ _ _ _ Hl0 Hl1 Hl2 _ K)
      )
    )
    ltac:(fun e =>
      fail "bisim_constr_detₜ: cannot find" e_foc "in target" e
    );
  tryif intros l then idtac else (
    fail "bisim_constr_detₜ:" l "not fresh"
  );
  pm_reduce;
  tryif goal_is_false then (
    fail "bisim_constr_detₜ:" Hl0 "or" Hl1 "or" Hl2 "not fresh"
  ) else (
    bisim_finisher
  ).
Tactic Notation "bisim_constr_detₜ" "as" simple_intropattern(l) :=
  let Hl0 := iFresh in
  let Hl1 := iFresh in
  let Hl2 := iFresh in
  bisim_constr_detₜ as l Hl0 Hl1 Hl2.
Tactic Notation "bisim_constr_detₜ" :=
  let l := fresh "lₜ" in
  bisim_constr_detₜ as l.
Tactic Notation "bisim_constr_det" "as" simple_intropattern(lₛ) simple_intropattern(lₜ) constr(Hl) :=
  bisim_pures;
  let e_focₛ := open_constr:(DataConstrDet _ (DataVal _) (DataVal _)) in
  let e_focₜ := open_constr:(DataConstrDet _ (DataVal _) (DataVal _)) in
  bisim_focalize e_focₛ e_focₜ
    ltac:(fun Kₛ Kₜ =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_constr_det _ _ _ Hl _ Kₛ _ _ Kₜ)
      )
    )
    ltac:(fun eₛ eₜ =>
      fail "bisim_constr_det: cannot find" e_focₛ "in source" eₛ "or" e_focₜ "in target" eₜ
    );
  [ try iSmash+
  | try iSmash+
  | tryif intros lₛ then (
      tryif intros lₜ then (
        pm_reduce;
        tryif goal_is_false then (
          fail "bisim_constr_det:" Hl "not fresh"
        ) else (
          bisim_finisher
        )
      ) else (
        fail "bisim_constr_det:" lₜ "not fresh"
      )
    ) else (
      fail "bisim_constr_det:" lₛ "not fresh"
    )
  ].
Tactic Notation "bisim_constr_det" "as" simple_intropattern(lₛ) simple_intropattern(lₜ) :=
  let Hl := iFresh in
  bisim_constr_det as lₜ lₛ Hl.
Tactic Notation "bisim_constr_det" :=
  bisim_constr_det as ? ?.

Tactic Notation "bisim_loadₛ" :=
  bisim_puresₛ;
  let e_foc := open_constr:(DataLoad (DataVal (DataLoc _)) (DataVal (DataIndex _))) in
  bisim_focalizeₛ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_loadₛ _ _ _ _ _ K)
      )
    )
    ltac:(fun e =>
      fail "bisim_loadₛ: cannot find" e_foc "in source" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₛ ?l _ _) => l end in
    fail "bisim_loadₛ: cannot find" l "↦ₛ ?"
  | bisim_finisher
  ].
Tactic Notation "bisim_loadₜ" :=
  bisim_puresₜ;
  let e_foc := open_constr:(DataLoad (DataVal (DataLoc _)) (DataVal (DataIndex _))) in
  bisim_focalizeₜ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_loadₜ _ _ _ _ _ _ K)
      )
    )
    ltac:(fun e =>
      fail "bisim_loadₜ: cannot find" e_foc "in target" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₜ ?l _ _) => l end in
    fail "bisim_loadₜ: cannot find" l "↦ₜ ?"
  | bisim_finisher
  ].
Tactic Notation "bisim_load" "as" simple_intropattern(vₛ) simple_intropattern(vₜ) constr(Hv) :=
  bisim_pures;
  let e_focₛ := open_constr:(DataLoad (DataVal (DataLoc _)) (DataVal (DataIndex _))) in
  let e_focₜ := open_constr:(DataLoad (DataVal (DataLoc _)) (DataVal (DataIndex _))) in
  bisim_focalize e_focₛ e_focₜ
    ltac:(fun Kₛ Kₜ =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_load _ _ _ Hv Kₛ _ _ Kₜ)
      )
    )
    ltac:(fun eₛ eₜ =>
      fail "bisim_load: cannot find" e_focₛ "in source" eₛ "or" e_focₜ "in target" eₜ
    );
  [ try iSmash+
  | try iSmash+
  | tryif intros vₛ then (
      tryif intros vₜ then (
        pm_reduce;
        tryif goal_is_false then (
          fail "bisim_load:" Hv "not fresh"
        ) else (
          bisim_finisher
        )
      ) else (
        fail "bisim_load:" vₜ "not fresh"
      )
    ) else (
      fail "bisim_load:" vₛ "not fresh"
    )
  ].
Tactic Notation "bisim_load" "as" simple_intropattern(vₛ) simple_intropattern(vₜ) :=
  let Hv := iFresh in
  bisim_load as vₛ vₜ Hv.
Tactic Notation "bisim_load" :=
  bisim_load as ? ?.

Ltac bisim_storeₛ :=
  bisim_puresₛ;
  let e_foc := open_constr:(DataStore (DataVal (DataLoc _)) (DataVal (DataIndex _)) (DataVal _)) in
  bisim_focalizeₛ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_storeₛ _ _ _ _ _ K)
      )
    )
    ltac:(fun e =>
      fail "bisim_storeₛ: cannot find" e_foc "in source" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₛ ?l _ _) => l end in
    fail "bisim_storeₛ: cannot find" l "↦ₛ ?"
  | pm_reduce; bisim_finisher
  ].
Ltac bisim_storeₜ :=
  bisim_puresₜ;
  let e_foc := open_constr:(DataStore (DataVal (DataLoc _)) (DataVal (DataIndex _)) (DataVal _)) in
  bisim_focalizeₜ e_foc
    ltac:(fun K =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_storeₜ _ _ _ _ _ _ K)
      )
    )
    ltac:(fun e =>
      fail "bisim_storeₜ: cannot find" e_foc "in source" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₜ ?l _ _) => l end in
    fail "bisim_storeₜ: cannot find" l "↦ₜ ?"
  | pm_reduce; bisim_finisher
  ].
Ltac bisim_store :=
  bisim_pures;
  let e_focₜ := open_constr:(DataStore (DataVal (DataLoc _)) (DataVal (DataIndex _)) (DataVal _)) in
  let e_focₛ := open_constr:(DataStore (DataVal (DataLoc _)) (DataVal (DataIndex _)) (DataVal _)) in
  bisim_focalize e_focₜ e_focₛ
    ltac:(fun Kₛ Kₜ =>
      on_bisim ltac:(fun _ _ _ _ _ =>
        eapply (tac_bisim_store _ _ _ Kₛ _ _ _ Kₜ)
      )
    )
    ltac:(fun eₛ eₜ =>
      fail "bisim_store: cannot find" e_focₛ "in source" eₛ "or" e_focₜ "in target" eₜ
    );
  [ try iSmash+
  | try iSmash+
  | try iSmash+
  | bisim_finisher
  ].

Tactic Notation "bisim_apply" open_constr(H) :=
  bisim_pures;
  on_bisim ltac:(fun _ _ _ eₛ eₜ =>
    tryif
      iPoseProofCore H as false ltac:(fun H =>
        expr_decompose [eₛ eₜ] ltac:(fun Kₛ _ Kₜ _ =>
          bisim_bind_core Kₛ Kₜ;
          iApplyHyp H
        )
      );
      try iSmash+
    then idtac else (
      fail "bisim_apply: cannot apply" H
    )
  ).

Tactic Notation "bisim_mono" open_constr(H) :=
  bisim_pures;
  on_bisim ltac:(fun _ _ _ eₛ eₜ =>
    tryif
      iPoseProofCore H as false ltac:(fun H =>
        expr_decompose [eₛ eₜ] ltac:(fun Kₛ _ Kₜ _ =>
          bisim_bind_core Kₛ Kₜ;
          let H_sel :=
            open_constr:(
              spec_patterns.SGoal (
                spec_patterns.SpecGoal
                  spec_patterns.GSpatial false [] [H] false
              )
            )
          in
          on_bisim_or_bisimv
            ltac:(fun _ _ _ _ _ => iApply (bisim_mono' with H_sel))
            ltac:(fun _ _ _ _ _ => iApply (bisimv_mono' with H_sel));
          [ iApplyHyp H
          | idtac
          ]
        )
      );
      try iSmash+
    then idtac else (
      fail "bisim_mono: cannot apply" H
    )
  ).
