From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  refinement.
From simuliris.lambda_human_lang Require Export
  compilation.
From simuliris.lambda_human_lang Require Import
  notations.
From simuliris.aps_plus Require Import
  definition.

Definition list_sum : lambda_human_program := {[
  "list_sum" := (BNamed "arg", (
    match: ![𝟙] "arg" with
      NIL =>
        0
    | CONS "x", "xs" =>
        "x" + $"list_sum" "xs"
    end
  )%lambda_human_expr)
]}.

Definition list_sum_aps_plus : lambda_human_program := {[
  "list_sum" := (BNamed "arg", (
    match: ![𝟙] "arg" with
      NIL =>
        0
    | CONS "x", "xs" =>
        let: "acc" := "x" in
        let: "arg" := "xs" in
        $"list_sum_aps" ("acc", "arg")
    end
  )%lambda_human_expr) ;
  "list_sum_aps" := (BNamed "arg", (
    let: "acc" := ![𝟙] "arg" in
    let: "arg" := ![𝟚] "arg" in
    match: ![𝟙] "arg" with
      NIL =>
        0 + "acc"
    | CONS "x", "xs" =>
        let: "acc'" := "x" in
        let: "arg" := "xs" in
        $"list_sum_aps" ("acc'" + "acc", "arg")
    end
  )%lambda_human_expr)
]}.

Goal
  aps_plus
    (lambda_human_program_compile list_sum)
    (lambda_human_program_compile list_sum_aps_plus).
Proof.
  rewrite /list_sum /list_sum_aps_plus.
  rewrite /lambda_human_program_compile map_fmap_singleton fmap_insert map_fmap_singleton /=.
  exists {["list_sum" := "list_sum_aps"]}; try set_solver.
  + intros * (<- & <-)%lookup_singleton_Some.
    rewrite lookup_insert.
    eexists. split; last done. repeat econstructor.
  + intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some.
    eexists. split; last done.
    repeat constructor. eapply aps_plus_aps_plus_1; first constructor.
    * eapply aps_plus_aps_call; repeat constructor.
    * done.
Qed.

(* Lemma list_sum_aps_plus_sound : *)
(*   lambda_program_refinement *)
(*     (lambda_human_program_compile list_sum) *)
(*     (lambda_human_program_compile list_sum_aps_plus). *)
(* Proof. *)
(*   rewrite /list_sum /list_sum_aps_plus. apply aps_plus_sound. *)
(*   - split. *)
(*     + apply lambda_human_program_compile_well_formed. *)
(*       rewrite /lambda_human_program_well_formed map_Forall_singleton //. *)
(*     + apply lambda_human_program_compile_closed. *)
(*   - rewrite /lambda_human_program_compile map_fmap_singleton fmap_insert map_fmap_singleton /=. *)
(*     exists {["list_sum" := "list_sum_aps"]}; try set_solver. *)
(*     + intros * (<- & <-)%lookup_singleton_Some. *)
(*       rewrite lookup_insert. *)
(*       eexists. split; last done. repeat econstructor. *)
(*     + intros * (<- & <-)%lookup_singleton_Some (_ & <-)%lookup_singleton_Some. *)
(*       eexists. split; last done. *)
(*       repeat constructor. eapply aps_plus_aps_plus_1; first constructor. *)
(*       * eapply aps_plus_aps_call; repeat constructor. *)
(*       * done. *)
(* Qed. *)
