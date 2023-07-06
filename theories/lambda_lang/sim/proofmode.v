From iris.proofmode Require Import
  coq_tactics
  reduction.

From simuliris Require Import
  prelude.
From simuliris.common Require Import
  tactics.
From simuliris.program_logic Require Export
  sim.proofmode.
From simuliris.lambda_lang Require Export
  sim.basic_rules.
From simuliris.lambda_lang Require Import
  sim.notations.

Section sim_GS.
  Context `{sim_programs : !SimPrograms lambda_ectx_lang lambda_ectx_lang}.
  Context `{sim_GS : !SimGS Σ}.
  Implicit Types tag : lambda_tag.
  Implicit Types l lₜ lₛ : loc.
  Implicit Types idx idxₜ idxₛ : lambda_index.
  Implicit Types v vₜ vₛ : lambda_val.
  Implicit Types e eₜ eₛ : lambda_expr.
  Implicit Types K Kₜ Kₛ : lambda_ectx.

  Lemma tac_sim_heap_bij_insert id1 p1 id2 lₛ lₜ P Δ :
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

  Section sim.
    Implicit Types Φ : lambda_expr → lambda_expr → iProp Σ.

    Lemma tac_sim_binopₛ1 K op e1 e2 e Φ Δ :
      envs_entails Δ (SIM K @@ let: e1 in let: e2.[ren (+1)] in LambdaBinopDet op $1 $0 ≳ e [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM K @@ LambdaBinop op e1 e2 ≳ e [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal sim_bind_invₛ sim_binopₛ1 sim_bindₛ //.
    Qed.
    Lemma tac_sim_binopₛ2 K op e1 e2 e Φ Δ :
      envs_entails Δ (SIM K @@ let: e2 in let: e1.[ren (+1)] in LambdaBinopDet op $0 $1 ≳ e [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM K @@ LambdaBinop op e1 e2 ≳ e [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal sim_bind_invₛ sim_binopₛ2 sim_bindₛ //.
    Qed.
    Lemma tac_sim_binopₜ e K op e1 e2 Φ Δ :
      envs_entails Δ (SIM e ≳ K @@ let: e1 in let: e2.[ren (+1)] in LambdaBinopDet op $1 $0 [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM e ≳ K @@ let: e2 in let: e1.[ren (+1)] in LambdaBinopDet op $0 $1 [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM e ≳ K @@ LambdaBinop op e1 e2 [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => Hsim1 Hsim2.
      rewrite -sim_bindₜ -sim_binopₜ -!sim_bind_invₜ.
      apply bi.and_intro; done.
    Qed.

    Lemma tac_sim_constrₛ1 K tag e1 e2 e Φ Δ :
      envs_entails Δ (SIM K @@ let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 ≳ e [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM K @@ &tag e1 e2 ≳ e [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal sim_bind_invₛ sim_constrₛ1 sim_bindₛ //.
    Qed.
    Lemma tac_sim_constrₛ2 K tag e1 e2 e Φ Δ :
      envs_entails Δ (SIM K @@ let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 ≳ e [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM K @@ &tag e1 e2 ≳ e [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal sim_bind_invₛ sim_constrₛ2 sim_bindₛ //.
    Qed.
    Lemma tac_sim_constrₜ e K tag e1 e2 Φ Δ :
      envs_entails Δ (SIM e ≳ K @@ let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM e ≳ K @@ let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM e ≳ K @@ &tag e1 e2 [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => Hsim1 Hsim2.
      rewrite -sim_bindₜ -sim_constrₜ -!sim_bind_invₜ.
      apply bi.and_intro; done.
    Qed.

    Lemma tac_sim_constr_detₛ id0 id1 id2 K tag v1 v2 e Φ Δ :
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
            envs_entails Δ' (SIM K @@ #l ≳ e [[ X ]] {{ Φ }})
        end
      ) →
      envs_entails Δ (SIM K @@ &&tag v1 v2 ≳ e [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => Hsim.
      rewrite -sim_bindₛ -sim_constr_detₛ. setoid_rewrite <- sim_bind_invₛ.
      apply bi.forall_intro => l. specialize (Hsim l).
      destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
      rewrite envs_app_sound // /= right_id Hsim.
      iIntros "H Hl0 Hl1 Hl2". iApply ("H" with "[$Hl0 $Hl1 $Hl2]").
    Qed.
    Lemma tac_sim_constr_detₜ id0 id1 id2 e K tag v1 v2 Φ Δ :
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
            envs_entails Δ' (SIM e ≳ K @@ #l [[ X ]] {{ Φ }})
        end
      ) →
      envs_entails Δ (SIM e ≳ K @@ &&tag v1 v2 [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => Hsim.
      rewrite -sim_bindₜ -sim_constr_detₜ.
      apply bi.forall_intro => l. specialize (Hsim l).
      destruct (envs_app _ _ _) as [Δ' |] eqn:HΔ'; last done.
      rewrite envs_app_sound // /= right_id Hsim sim_bind_invₜ.
      iIntros "H Hl0 Hl1 Hl2". iApply ("H" with "[$Hl0 $Hl1 $Hl2]").
    Qed.
    Lemma tac_sim_constr_det id tag Kₛ vₛ1 vₛ2 Kₜ vₜ1 vₜ2 Φ Δ :
      envs_entails Δ (vₛ1 ≈ vₜ1) →
      envs_entails Δ (vₛ2 ≈ vₜ2) →
      ( ∀ lₛ lₜ,
        match envs_app true (Esnoc Enil id (LambdaLoc lₛ ≈ LambdaLoc lₜ)) Δ with
        | None =>
            False
        | Some Δ' =>
            envs_entails Δ' (SIM Kₛ @@ #lₛ ≳ Kₜ @@ #lₜ [[ X ]] {{ Φ }})
        end
      ) →
      envs_entails Δ (SIM Kₛ @@ &&tag vₛ1 vₛ2 ≳ Kₜ @@ &&tag vₜ1 vₜ2 [[ X ]] {{ Φ }}).
    Proof.
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

    Lemma tac_sim_loadₛ id p K l idx v e Φ Δ :
      envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₛ v)%I →
      envs_entails Δ (SIM K @@ #v ≳ e [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM K @@ ![idx] l ≳ e [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => Hlookup Hsim.
      rewrite envs_lookup_split // -sim_bindₛ Hsim.
      destruct p; simpl;
        [iIntros "(#Hl & Hsim)" | iIntros "(Hl & Hsim)"];
        iApply (sim_loadₛ with "Hl"); iIntros;
        iApply sim_bind_invₛ;
        iApply ("Hsim" with "[$]").
    Qed.
    Lemma tac_sim_loadₜ id p e K l idx v Φ Δ :
      envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₜ v)%I →
      envs_entails Δ (SIM e ≳ K @@ #v [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM e ≳ K @@ ![idx] l [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => Hlookup Hsim.
      rewrite envs_lookup_split // -sim_bindₜ Hsim.
      destruct p; simpl;
        [iIntros "(#Hl & Hsim)" | iIntros "(Hl & Hsim)"];
        iApply (sim_loadₜ with "Hl"); iIntros;
        iApply sim_bind_invₜ;
        iApply ("Hsim" with "[$]").
    Qed.
    Lemma tac_sim_load id Kₛ lₛ idxₛ Kₜ lₜ idxₜ Φ Δ :
      envs_entails Δ (LambdaLoc lₛ ≈ LambdaLoc lₜ) →
      envs_entails Δ (LambdaIndex idxₛ ≈ LambdaIndex idxₜ) →
      ( ∀ vₛ vₜ,
        match envs_app true (Esnoc Enil id (vₛ ≈ vₜ)) Δ with
        | None =>
            False
        | Some Δ' =>
            envs_entails Δ' (SIM Kₛ @@ #vₛ ≳ Kₜ @@ #vₜ [[ X ]] {{ Φ }})
        end
      ) →
      envs_entails Δ (SIM Kₛ @@ ![idxₛ] lₛ ≳ Kₜ @@ ![idxₜ] lₜ [[ X ]] {{ Φ }}).
    Proof.
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

    Lemma tac_sim_storeₛ id p K l idx v w e Φ Δ :
      envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₛ w)%I →
      match envs_replace id p false (Esnoc Enil id ((l +ₗ idx) ↦ₛ v)) Δ with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (SIM K @@ #() ≳ e [[ X ]] {{ Φ }})
      end →
      envs_entails Δ (SIM K @@ #l <-[idx]- v ≳ e [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => Hlookup Hsim.
      destruct (envs_replace _ _ _ _) as [Δ' |] eqn:HΔ'; last done.
      rewrite envs_replace_singleton_sound // Hsim.
      rewrite bi.intuitionistically_if_elim /=.
      rewrite sim_bind_invₛ -sim_bindₛ. apply bi.wand_elim_l', sim_storeₛ.
    Qed.
    Lemma tac_sim_storeₜ id p e K l idx v w Φ Δ :
      envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₜ w)%I →
      match envs_replace id p false (Esnoc Enil id ((l +ₗ idx) ↦ₜ v)) Δ with
      | None =>
          False
      | Some Δ' =>
          envs_entails Δ' (SIM e ≳ K @@ #() [[ X ]] {{ Φ }})
      end →
      envs_entails Δ (SIM e ≳ K @@ #l <-[idx]- v [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => Hlookup Hsim.
      destruct (envs_replace _ _ _ _) as [Δ' |] eqn:HΔ'; last done.
      rewrite envs_replace_singleton_sound // Hsim.
      rewrite bi.intuitionistically_if_elim /=.
      rewrite sim_bind_invₜ -sim_bindₜ. apply bi.wand_elim_l', sim_storeₜ.
    Qed.
    Lemma tac_sim_store Kₛ vₛ1 vₛ2 vₛ3 Kₜ vₜ1 vₜ2 vₜ3 Φ Δ :
      envs_entails Δ (vₛ1 ≈ vₜ1) →
      envs_entails Δ (vₛ2 ≈ vₜ2) →
      envs_entails Δ (vₛ3 ≈ vₜ3) →
      envs_entails Δ (SIM Kₛ @@ #() ≳ Kₜ @@ #() [[ X ]] {{ Φ }}) →
      envs_entails Δ (SIM Kₛ @@ vₛ1 <-[vₛ2]- vₛ3 ≳ Kₜ @@ vₜ1 <-[vₜ2]- vₜ3 [[ X ]] {{ Φ }}).
    Proof.
      rewrite envs_entails_unseal => Hv1 Hv2 Hv3 Hsim.
      iIntros "HΔ".
      iDestruct (Hv1 with "HΔ") as "#Hv1".
      iDestruct (Hv2 with "HΔ") as "#Hv2".
      iDestruct (Hv3 with "HΔ") as "#Hv3".
      iApply sim_bind. iApply (sim_store with "Hv1 Hv2 Hv3"). iApply (Hsim with "HΔ").
    Qed.
  End sim.

  Section simv.
    Implicit Types Φ : lambda_val → lambda_val → iProp Σ.

    Lemma tac_simv_binopₛ1 K op e1 e2 e Φ Δ :
      envs_entails Δ (SIM K @@ let: e1 in let: e2.[ren (+1)] in LambdaBinopDet op $1 $0 ≳ e [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM K @@ LambdaBinop op e1 e2 ≳ e [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_binopₛ1.
    Qed.
    Lemma tac_simv_binopₛ2 K op e1 e2 e Φ Δ :
      envs_entails Δ (SIM K @@ let: e2 in let: e1.[ren (+1)] in LambdaBinopDet op $0 $1 ≳ e [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM K @@ LambdaBinop op e1 e2 ≳ e [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_binopₛ2.
    Qed.
    Lemma tac_simv_binopₜ e K op e1 e2 Φ Δ :
      envs_entails Δ (SIM e ≳ K @@ let: e1 in let: e2.[ren (+1)] in LambdaBinopDet op $1 $0 [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM e ≳ K @@ let: e2 in let: e1.[ren (+1)] in LambdaBinopDet op $0 $1 [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM e ≳ K @@ LambdaBinop op e1 e2 [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_binopₜ.
    Qed.

    Lemma tac_simv_constrₛ1 K tag e1 e2 e Φ Δ :
      envs_entails Δ (SIM K @@ let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 ≳ e [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM K @@ &tag e1 e2 ≳ e [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_constrₛ1.
    Qed.
    Lemma tac_simv_constrₛ2 K tag e1 e2 e Φ Δ :
      envs_entails Δ (SIM K @@ let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 ≳ e [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM K @@ &tag e1 e2 ≳ e [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_constrₛ2.
    Qed.
    Lemma tac_simv_constrₜ e K tag e1 e2 Φ Δ :
      envs_entails Δ (SIM e ≳ K @@ let: e1 in let: e2.[ren (+1)] in &&tag $1 $0 [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM e ≳ K @@ let: e2 in let: e1.[ren (+1)] in &&tag $0 $1 [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM e ≳ K @@ &tag e1 e2 [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_constrₜ.
    Qed.

    Lemma tac_simv_constr_detₛ id0 id1 id2 K tag v1 v2 e Φ Δ :
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
            envs_entails Δ' (SIM K @@ #l ≳ e [[ X ]] [[ Φ ]])
        end
      ) →
      envs_entails Δ (SIM K @@ &&tag v1 v2 ≳ e [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_constr_detₛ.
    Qed.
    Lemma tac_simv_constr_detₜ id0 id1 id2 e K tag v1 v2 Φ Δ :
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
            envs_entails Δ' (SIM e ≳ K @@ #l [[ X ]] [[ Φ ]])
        end
      ) →
      envs_entails Δ (SIM e ≳ K @@ &&tag v1 v2 [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_constr_detₜ.
    Qed.
    Lemma tac_simv_constr_det id tag Kₛ vₛ1 vₛ2 Kₜ vₜ1 vₜ2 Φ Δ :
      envs_entails Δ (vₛ1 ≈ vₜ1) →
      envs_entails Δ (vₛ2 ≈ vₜ2) →
      ( ∀ lₛ lₜ,
        match envs_app true (Esnoc Enil id (LambdaLoc lₛ ≈ LambdaLoc lₜ)) Δ with
        | None =>
            False
        | Some Δ' =>
            envs_entails Δ' (SIM Kₛ @@ #lₛ ≳ Kₜ @@ #lₜ [[ X ]] [[ Φ ]])
        end
      ) →
      envs_entails Δ (SIM Kₛ @@ &&tag vₛ1 vₛ2 ≳ Kₜ @@ &&tag vₜ1 vₜ2 [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_constr_det.
    Qed.

    Lemma tac_simv_loadₛ id p K l idx v e Φ Δ :
      envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₛ v)%I →
      envs_entails Δ (SIM K @@ #v ≳ e [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM K @@ ![idx] l ≳ e [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_loadₛ.
    Qed.
    Lemma tac_simv_loadₜ id p e K l idx v Φ Δ :
      envs_lookup id Δ = Some (p, (l +ₗ idx) ↦ₜ v)%I →
      envs_entails Δ (SIM e ≳ K @@ #v [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM e ≳ K @@ ![idx] l [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_loadₜ.
    Qed.
    Lemma tac_simv_load id Kₛ lₛ idxₛ Kₜ lₜ idxₜ Φ Δ :
      envs_entails Δ (LambdaLoc lₛ ≈ LambdaLoc lₜ) →
      envs_entails Δ (LambdaIndex idxₛ ≈ LambdaIndex idxₜ) →
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
      apply tac_sim_load.
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
      apply tac_sim_storeₛ.
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
      apply tac_sim_storeₜ.
    Qed.
    Lemma tac_simv_store Kₛ vₛ1 vₛ2 vₛ3 Kₜ vₜ1 vₜ2 vₜ3 Φ Δ :
      envs_entails Δ (vₛ1 ≈ vₜ1) →
      envs_entails Δ (vₛ2 ≈ vₜ2) →
      envs_entails Δ (vₛ3 ≈ vₜ3) →
      envs_entails Δ (SIM Kₛ @@ #() ≳ Kₜ @@ #() [[ X ]] [[ Φ ]]) →
      envs_entails Δ (SIM Kₛ @@ vₛ1 <-[vₛ2]- vₛ3 ≳ Kₜ @@ vₜ1 <-[vₜ2]- vₜ3 [[ X ]] [[ Φ ]]).
    Proof.
      rewrite definition.simv_unseal /definition.simv_def.
      apply tac_sim_store.
    Qed.
  End simv.
End sim_GS.

#[local] Ltac expr_decompose e tac :=
  let rec go K e :=
    let go k e := go (k :: K) e in
    match e with
    | LambdaLet ?e1 ?e2 =>
        go (LambdaEctxiLet e2) e1
    | LambdaCall ?e1 (LambdaVal ?v2) =>
        go (LambdaEctxiCall2 v2) e1
    | LambdaCall ?e1 ?e2 =>
        go (LambdaEctxiCall1 e1) e2
    | LambdaUnop ?op ?e =>
        go (LambdaEctxiUnop op) e
    | LambdaIf ?e0 ?e1 ?e2 =>
        go (LambdaEctxiIf e1 e2) e0
    | LambdaLoad ?e1 (LambdaVal ?v2) =>
        go (LambdaEctxiLoad2 v2) e1
    | LambdaLoad ?e1 ?e2 =>
        go (LambdaEctxiLoad1 e1) e2
    | LambdaStore ?e1 (LambdaVal ?v2) (LambdaVal ?v3) =>
        go (LambdaEctxiStore3 v2 v3) e1
    | LambdaStore ?e1 ?e2 (LambdaVal ?v3) =>
        go (LambdaEctxiStore2 e1 v3) e2
    | LambdaStore ?e1 ?e2 ?e3 =>
        go (LambdaEctxiStore1 e1 e2) e3
    | _ =>
        tac K e
    end
  in
  go (∅ : lambda_ectx) e.
#[local] Tactic Notation "expr_decompose" "[" open_constr(eₛ) open_constr(eₜ) "]" tactic3(tac) :=
  expr_decompose eₛ ltac:(fun Kₛ eₛ' =>
    expr_decompose eₜ ltac:(fun Kₜ eₜ' =>
      tac Kₛ eₛ' Kₜ eₜ'
    )
  ).

Tactic Notation "sim_finish" :=
  sim_finish with asimpl.

Ltac sim_asimpl :=
  sim_eval (asimpl; simpl).
Ltac sim_asimplₛ :=
  sim_evalₛ (asimpl; simpl).
Ltac sim_asimplₜ :=
  sim_evalₜ (asimpl; simpl).

#[local] Ltac sim_focalizeₛ e_foc tac_succ tac_fail :=
  on_sim_or_simv' ltac:(fun _ _ _ e _ =>
    tryif
      expr_decompose e ltac:(fun K e' =>
        unify e' e_foc;
        tac_succ K
      )
    then idtac else (
      tac_fail e
    )
  ).
#[local] Ltac sim_focalizeₜ e_foc tac_succ tac_fail :=
  on_sim_or_simv' ltac:(fun _ _ _ _ e =>
    tryif
      expr_decompose e ltac:(fun K e' =>
        unify e' e_foc;
        tac_succ K
      )
    then idtac else (
      tac_fail e
    )
  ).
#[local] Ltac sim_focalize e_focₛ e_focₜ tac_succ tac_fail :=
  on_sim_or_simv' ltac:(fun _ _ _ eₛ eₜ =>
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

Tactic Notation "sim_bindₛ" open_constr(e_foc) :=
  sim_focalizeₛ e_foc
    ltac:(fun K => sim_bind_coreₛ K)
    ltac:(fun e => fail "sim_bindₛ: cannot find" e_foc "in source" e).
Tactic Notation "sim_bindₛ" :=
  sim_bindₛ _.
Tactic Notation "sim_bindₜ" open_constr(e_foc) :=
  sim_focalizeₜ e_foc
    ltac:(fun K => sim_bind_coreₜ K)
    ltac:(fun e => fail "sim_bindₜ: cannot find" e_foc "in target" e).
Tactic Notation "sim_bindₜ" :=
  sim_bindₜ _.
Tactic Notation "sim_bind" open_constr(e_focₛ) open_constr(e_focₜ) :=
  on_sim ltac:(fun _ _ _ eₛ eₜ =>
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
    sim_bind_core Kₛ Kₜ
  ).
Tactic Notation "sim_bind" :=
  sim_bind _ _.

Tactic Notation "sim_pureₛ" open_constr(e_foc) :=
  sim_focalizeₛ e_foc
    ltac:(fun K => sim_pure_coreₛ K)
    ltac:(fun e => fail "sim_pureₛ: cannot find" e_foc "in source" e "or" e_foc "is not a redex").
Tactic Notation "sim_pureₛ" :=
  sim_pureₛ _.
Ltac sim_puresₛ :=
  repeat (sim_pureₛ; []) || sim_finish.
Tactic Notation "sim_pureₜ" open_constr(e_foc) :=
  sim_focalizeₜ e_foc
    ltac:(fun K => sim_pure_coreₜ K)
    ltac:(fun e => fail "sim_pureₜ: cannot find" e_foc "in target" e "or" e_foc "is not a redex").
Tactic Notation "sim_pureₜ" :=
  sim_pureₜ _.
Ltac sim_puresₜ :=
  repeat (sim_pureₜ; []) || sim_finish.
Ltac sim_pures :=
  sim_puresₜ; sim_puresₛ.

#[local] Ltac sim_heap_bij_insert_core Htie Hsimilar :=
  iStartProof;
  eapply (tac_sim_heap_bij_insert Htie _ Hsimilar);
  [ iSolveTC
  | iAssumptionCore ||
    tryif is_evar Htie then (
      fail "sim_heap_bij_insert: cannot find ? ⋈ ?"
    ) else (
      fail "sim_heap_bij_insert: cannot find" Htie ": ? ⋈ ?"
    )
  | pm_reduce;
    tryif goal_is_false then (
      fail "sim_heap_bij_insert:" Hsimilar "not fresh"
    ) else (
      try sim_finish
    )
  ].
Tactic Notation "sim_heap_bij_insert" open_constr(Htie) "as" constr(Hsimilar) :=
  sim_heap_bij_insert_core Htie Hsimilar.
Tactic Notation "sim_heap_bij_insert" open_constr(Htie) :=
  sim_heap_bij_insert Htie as Htie.
Tactic Notation "sim_heap_bij_insert" "as" constr(Hsimilar) :=
  sim_heap_bij_insert _ as Hsimilar.
Tactic Notation "sim_heap_bij_insert" :=
  let Htie := open_constr:(_) in
  sim_heap_bij_insert_core Htie Htie.

Ltac sim_binopₛ1 :=
  sim_pures;
  let e_foc := open_constr:(LambdaBinop _ _ _) in
  sim_focalizeₛ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_binopₛ1 _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_binopₛ1 _ K))
    )
    ltac:(fun e =>
      fail "sim_binopₛ1: cannot find" e_foc "in source" e
    );
  sim_finish.
Ltac sim_binopₛ2 :=
  sim_pures;
  let e_foc := open_constr:(LambdaBinop _ _ _) in
  sim_focalizeₛ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_binopₛ2 _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_binopₛ2 _ K))
    )
    ltac:(fun e =>
      fail "sim_binopₛ2: cannot find" e_foc "in source" e
    );
  sim_finish.
Ltac sim_binopₜ :=
  sim_pures;
  let e_foc := open_constr:(LambdaBinop _ _ _) in
  sim_focalizeₜ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_binopₜ _ _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_binopₜ _ _ K))
    )
    ltac:(fun e =>
      fail "sim_binopₜ: cannot find" e_foc "in target" e
    );
  sim_finish.

Ltac sim_constrₛ1 :=
  sim_pures;
  let e_foc := open_constr:(LambdaConstr _ _ _) in
  sim_focalizeₛ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_constrₛ1 _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_constrₛ1 _ K))
    )
    ltac:(fun e =>
      fail "sim_constrₛ1: cannot find" e_foc "in source" e
    );
  sim_finish.
Ltac sim_constrₛ2 :=
  sim_pures;
  let e_foc := open_constr:(LambdaConstr _ _ _) in
  sim_focalizeₛ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_constrₛ2 _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_constrₛ2 _ K))
    )
    ltac:(fun e =>
      fail "sim_constrₛ2: cannot find" e_foc "in source" e
    );
  sim_finish.
Ltac sim_constrₜ :=
  sim_pures;
  let e_foc := open_constr:(LambdaConstr _ _ _) in
  sim_focalizeₜ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_constrₜ _ _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_constrₜ _ _ K))
    )
    ltac:(fun e =>
      fail "sim_constrₜ: cannot find" e_foc "in target" e
    );
  sim_finish.

Tactic Notation "sim_constr_detₛ" "as" simple_intropattern(l) constr(Hl0) constr(Hl1) constr(Hl2) :=
  sim_pures;
  let e_foc := open_constr:(LambdaConstrDet _ (LambdaVal _) (LambdaVal _)) in
  sim_focalizeₛ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_constr_detₛ _ Hl0 Hl1 Hl2 K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_constr_detₛ _ Hl0 Hl1 Hl2 K))
    )
    ltac:(fun e =>
      fail "sim_constr_detₛ: cannot find" e_foc "in source" e
    );
  tryif intros l then idtac else (
    fail "sim_constr_detₛ:" l "not fresh"
  );
  pm_reduce;
  tryif goal_is_false then (
    fail "sim_constr_detₛ:" Hl0 "or" Hl1 "or" Hl2 "not fresh"
  ) else (
    sim_finish
  ).
Tactic Notation "sim_constr_detₛ" "as" simple_intropattern(l) :=
  let Hl0 := iFresh in
  let Hl1 := iFresh in
  let Hl2 := iFresh in
  sim_constr_detₛ as l Hl0 Hl1 Hl2.
Tactic Notation "sim_constr_detₛ" :=
  let l := fresh "lₛ" in
  sim_constr_detₛ as l.
Tactic Notation "sim_constr_detₜ" "as" simple_intropattern(l) constr(Hl0) constr(Hl1) constr(Hl2) :=
  sim_pures;
  let e_foc := open_constr:(LambdaConstrDet _ (LambdaVal _) (LambdaVal _)) in
  sim_focalizeₜ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_constr_detₜ _ Hl0 Hl1 Hl2 _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_constr_detₜ _ Hl0 Hl1 Hl2 _ K))
    )
    ltac:(fun e =>
      fail "sim_constr_detₜ: cannot find" e_foc "in target" e
    );
  tryif intros l then idtac else (
    fail "sim_constr_detₜ:" l "not fresh"
  );
  pm_reduce;
  tryif goal_is_false then (
    fail "sim_constr_detₜ:" Hl0 "or" Hl1 "or" Hl2 "not fresh"
  ) else (
    sim_finish
  ).
Tactic Notation "sim_constr_detₜ" "as" simple_intropattern(l) :=
  let Hl0 := iFresh in
  let Hl1 := iFresh in
  let Hl2 := iFresh in
  sim_constr_detₜ as l Hl0 Hl1 Hl2.
Tactic Notation "sim_constr_detₜ" :=
  let l := fresh "lₜ" in
  sim_constr_detₜ as l.
Tactic Notation "sim_constr_det" "as" simple_intropattern(lₛ) simple_intropattern(lₜ) constr(Hl) :=
  sim_pures;
  let e_focₛ := open_constr:(LambdaConstrDet _ (LambdaVal _) (LambdaVal _)) in
  let e_focₜ := open_constr:(LambdaConstrDet _ (LambdaVal _) (LambdaVal _)) in
  sim_focalize e_focₛ e_focₜ
    ltac:(fun Kₛ Kₜ =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_constr_det _ Hl _ Kₛ _ _ Kₜ))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_constr_det _ Hl _ Kₛ _ _ Kₜ))
    )
    ltac:(fun eₛ eₜ =>
      fail "sim_constr_det: cannot find" e_focₛ "in source" eₛ "or" e_focₜ "in target" eₜ
    );
  [ try done
  | try done
  | tryif intros lₛ then (
      tryif intros lₜ then (
        pm_reduce;
        tryif goal_is_false then (
          fail "sim_constr_det:" Hl "not fresh"
        ) else (
          sim_finish
        )
      ) else (
        fail "sim_constr_det:" lₜ "not fresh"
      )
    ) else (
      fail "sim_constr_det:" lₛ "not fresh"
    )
  ].
Tactic Notation "sim_constr_det" "as" simple_intropattern(lₛ) simple_intropattern(lₜ) :=
  let Hl := iFresh in
  sim_constr_det as lₜ lₛ Hl.
Tactic Notation "sim_constr_det" :=
  sim_constr_det as ? ?.

Tactic Notation "sim_loadₛ" :=
  sim_pures;
  let e_foc := open_constr:(LambdaLoad (LambdaVal (LambdaLoc _)) (LambdaVal (LambdaIndex _))) in
  sim_focalizeₛ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_loadₛ _ _ _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_loadₛ _ _ _ K))
    )
    ltac:(fun e =>
      fail "sim_loadₛ: cannot find" e_foc "in source" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₛ ?l _ _) => l end in
    fail "sim_loadₛ: cannot find" l "↦ₛ ?"
  | sim_finish
  ].
Tactic Notation "sim_loadₜ" :=
  sim_pures;
  let e_foc := open_constr:(LambdaLoad (LambdaVal (LambdaLoc _)) (LambdaVal (LambdaIndex _))) in
  sim_focalizeₜ e_foc
    ltac:(fun K =>
    on_sim_or_simv
      ltac:(fun _ _ _ _ _ => eapply (tac_sim_loadₜ _ _ _ _ K))
      ltac:(fun _ _ _ _ _ => eapply (tac_simv_loadₜ _ _ _ _ K))
    )
    ltac:(fun e =>
      fail "sim_loadₜ: cannot find" e_foc "in target" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₜ ?l _ _) => l end in
    fail "sim_loadₜ: cannot find" l "↦ₜ ?"
  | sim_finish
  ].
Tactic Notation "sim_load" "as" simple_intropattern(vₛ) simple_intropattern(vₜ) constr(Hv) :=
  sim_pures;
  let e_focₛ := open_constr:(LambdaLoad (LambdaVal (LambdaLoc _)) (LambdaVal (LambdaIndex _))) in
  let e_focₜ := open_constr:(LambdaLoad (LambdaVal (LambdaLoc _)) (LambdaVal (LambdaIndex _))) in
  sim_focalize e_focₛ e_focₜ
    ltac:(fun Kₛ Kₜ =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_load _ Hv Kₛ _ _ Kₜ))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_load _ Hv Kₛ _ _ Kₜ))
    )
    ltac:(fun eₛ eₜ =>
      fail "sim_load: cannot find" e_focₛ "in source" eₛ "or" e_focₜ "in target" eₜ
    );
  [ try done
  | try done
  | tryif intros vₛ then (
      tryif intros vₜ then (
        pm_reduce;
        tryif goal_is_false then (
          fail "sim_load:" Hv "not fresh"
        ) else (
          sim_finish
        )
      ) else (
        fail "sim_load:" vₜ "not fresh"
      )
    ) else (
      fail "sim_load:" vₛ "not fresh"
    )
  ].
Tactic Notation "sim_load" "as" simple_intropattern(vₛ) simple_intropattern(vₜ) :=
  let Hv := iFresh in
  sim_load as vₛ vₜ Hv.
Tactic Notation "sim_load" :=
  sim_load as ? ?.

Ltac sim_storeₛ :=
  sim_pures;
  let e_foc := open_constr:(LambdaStore (LambdaVal (LambdaLoc _)) (LambdaVal (LambdaIndex _)) (LambdaVal _)) in
  sim_focalizeₛ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_storeₛ _ _ _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_storeₛ _ _ _ K))
    )
    ltac:(fun e =>
      fail "sim_storeₛ: cannot find" e_foc "in source" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₛ ?l _ _) => l end in
    fail "sim_storeₛ: cannot find" l "↦ₛ ?"
  | pm_reduce; sim_finish
  ].
Ltac sim_storeₜ :=
  sim_pures;
  let e_foc := open_constr:(LambdaStore (LambdaVal (LambdaLoc _)) (LambdaVal (LambdaIndex _)) (LambdaVal _)) in
  sim_focalizeₜ e_foc
    ltac:(fun K =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_storeₜ _ _ _ _ K))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_storeₜ _ _ _ _ K))
    )
    ltac:(fun e =>
      fail "sim_storeₜ: cannot find" e_foc "in source" e
    );
  [ iAssumptionCore ||
    let l := match goal with |- _ = Some (_, mapstoₜ ?l _ _) => l end in
    fail "sim_storeₜ: cannot find" l "↦ₜ ?"
  | pm_reduce; sim_finish
  ].
Ltac sim_store :=
  sim_pures;
  let e_focₜ := open_constr:(LambdaStore (LambdaVal (LambdaLoc _)) (LambdaVal (LambdaIndex _)) (LambdaVal _)) in
  let e_focₛ := open_constr:(LambdaStore (LambdaVal (LambdaLoc _)) (LambdaVal (LambdaIndex _)) (LambdaVal _)) in
  sim_focalize e_focₜ e_focₛ
    ltac:(fun Kₛ Kₜ =>
      on_sim_or_simv
        ltac:(fun _ _ _ _ _ => eapply (tac_sim_store _ Kₛ _ _ _ Kₜ))
        ltac:(fun _ _ _ _ _ => eapply (tac_simv_store _ Kₛ _ _ _ Kₜ))
    )
    ltac:(fun eₛ eₜ =>
      fail "sim_store: cannot find" e_focₛ "in source" eₛ "or" e_focₜ "in target" eₜ
    );
  [ try done
  | try done
  | try done
  | sim_finish
  ].

Tactic Notation "sim_apply" open_constr(H) :=
  on_sim_or_simv' ltac:(fun _ _ _ eₛ eₜ =>
    tryif
      iPoseProofCore H as false ltac:(fun H =>
        expr_decompose [eₛ eₜ] ltac:(fun Kₛ _ Kₜ _ =>
          sim_bind_core Kₛ Kₜ;
          iApplyHyp H;
          try done
        )
      )
    then idtac else (
      let P := type of H in
      fail "sim_apply: cannot apply" H ":" P
    )
  ).
Tactic Notation "sim_smart_apply" open_constr(H) :=
  sim_pures;
  sim_apply H.

Tactic Notation "sim_mono" open_constr(H) :=
  on_sim_or_simv' ltac:(fun _ _ _ eₛ eₜ =>
    tryif
      iPoseProofCore H as false ltac:(fun H =>
        expr_decompose [eₛ eₜ] ltac:(fun Kₛ _ Kₜ _ =>
          sim_bind_core Kₛ Kₜ;
          let H_sel :=
            open_constr:(
              spec_patterns.SGoal (
                spec_patterns.SpecGoal
                  spec_patterns.GSpatial false [] [H] false
              )
            )
          in
          on_sim_or_simv
            ltac:(fun _ _ _ _ _ => iApply (sim_mono' with H_sel))
            ltac:(fun _ _ _ _ _ => iApply (simv_mono' with H_sel));
          [ iApplyHyp H; try done
          | try solve [done | iIntros "% % ? //"]
          ]
        )
      )
    then idtac else (
      let P := type of H in
      fail "sim_mono: cannot apply" H ":" P
    )
  ).
Tactic Notation "sim_smart_mono" open_constr(H) :=
  sim_pures;
  sim_mono H.
