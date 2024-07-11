From camlcert Require Import
  prelude.
From camlcert.iris.program_logic Require Import
  sim.adequacy.
From camlcert.data_lang Require Import
  refinement
  sim.proofmode
  sim.notations.
From camlcert Require Import
  options.

Implicit Types func : data_function.
Implicit Types vₛ vₜ : data_val.

Lemma sim_adequacy `{sim_programs : !SimPrograms _ _} :
  ( ∀ `{sim_GS : !SimGS sim_Σ} func defₛ vₛ vₜ,
    sim_progₛ !! func = Some defₛ →
    data_val_well_formed sim_progₛ vₛ →
    vₛ ≈ vₜ →
    ⊢@{iPropI sim_Σ} SIM func vₛ ≳ func vₜ {{# (≈) }}
  ) →
  data_program_refinement sim_progₛ sim_progₜ.
Proof.
  intros H func defₛ Hfuncₛ vₛ vₜ Hvₛ Hv.
  apply: (sim_adequacy' (M := (iResUR sim_Σ))).
  iMod (sim_init ∅ ∅) as "(%sim_GS & Hsi & _ & _ & _ & _)".
  iModIntro. iExists _, _. iFrame. iSplitR.
  { clear dependent vₛ vₜ. iIntros "!> %vₛ %vₜ #Hv".
    iApply (data_val_bi_similar_similar with "Hv").
  }
  iApply H; done.
Qed.
