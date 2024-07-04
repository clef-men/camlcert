From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  metatheory.
From camlcert.tmc_2 Require Export
  definition.
From camlcert Require Import
  options.

Section tmc_ctxi.
  Implicit Types c : tmc_ctxi.

  Lemma tmc_ctxi_hsubst_comp c ς1 ς2 :
    c.|[ς1].|[ς2] = c.|[ς1 >> ς2].
  Proof.
    destruct c as (?, [], ?); autosubst.
  Qed.
  Lemma tmc_ctxi_fill_subst c e ς :
    (c @@ e).[ς] = c.|[ς] @@ e.[ς].
  Proof.
    destruct c as (?, [], ?); done.
  Qed.

  Definition tmc_ctxi_scoped scope c :=
    data_expr_scoped scope c.(tmc_ctxi_expr).

  Lemma tmc_ctxi_fill_scoped c e scope :
    tmc_ctxi_scoped scope c →
    data_expr_scoped scope e →
    data_expr_scoped scope (c @@ e).
  Proof.
    destruct c as (?, [], ?); done.
  Qed.
  Lemma tmc_ctxi_scoped_lift1 scope c :
    tmc_ctxi_scoped scope c →
    tmc_ctxi_scoped (S scope) c.|[ren (+1)].
  Proof.
    destruct c as (?, [], ?); apply data_expr_scoped_lift1.
  Qed.
End tmc_ctxi.

#[global] Hint Rewrite tmc_ctxi_hsubst_comp : autosubst.
#[global] Hint Rewrite tmc_ctxi_fill_subst : autosubst.

Section tmc_ctx.
  Implicit Types C : tmc_ctx.

  Lemma tmc_ctx_fill_nil e :
    ([] : tmc_ctx) @@ e = e.
  Proof.
    done.
  Qed.
  Lemma tmc_ctx_fill_cons c C e :
    (c :: C) @@ e = C @@ c @@ e.
  Proof.
    done.
  Qed.
  Lemma tmc_ctx_fill_app C1 C2 e :
    (C1 ++ C2) @@ e = C2 @@ C1 @@ e.
  Proof.
    apply foldl_app.
  Qed.
  Lemma tmc_ctx_fill_snoc c C e :
    (C ++ [c]) @@ e = c @@ C @@ e.
  Proof.
    rewrite tmc_ctx_fill_app //.
  Qed.

  Lemma tmc_ctx_hsubst_nil ς :
    ([] : tmc_ctx).|[ς] = [].
  Proof.
    done.
  Qed.
  Lemma tmc_ctx_hsubst_cons c C ς :
    (c :: C).|[ς] = c.|[ς] :: C.|[ς].
  Proof.
    done.
  Qed.
  Lemma tmc_ctx_hsubst_comp C ς1 ς2 :
    C.|[ς1].|[ς2] = C.|[ς1 >> ς2].
  Proof.
    setoid_rewrite <- list_fmap_compose.
    apply list_fmap_ext. intros. cbn.
    rewrite tmc_ctxi_hsubst_comp //.
  Qed.
  Lemma tmc_ctx_fill_subst C e ς :
    (C @@ e).[ς] = C.|[ς] @@ e.[ς].
  Proof.
    move: e. induction C as [| c C IH] => e; first done.
    rewrite IH tmc_ctxi_fill_subst //.
  Qed.

  Definition tmc_ctx_scoped scope : tmc_ctx → Prop :=
    Forall (tmc_ctxi_scoped scope).

  Lemma tmc_ctx_scoped_nil scope :
    tmc_ctx_scoped scope [].
  Proof.
    apply Forall_nil_2.
  Qed.
  Lemma tmc_ctx_scoped_cons scope c C :
    tmc_ctxi_scoped scope c →
    tmc_ctx_scoped scope C →
    tmc_ctx_scoped scope (c :: C).
  Proof.
    apply Forall_cons_2.
  Qed.
  Lemma tmc_ctx_scoped_cons_inv scope c C :
    tmc_ctx_scoped scope (c :: C) →
      tmc_ctxi_scoped scope c ∧
      tmc_ctx_scoped scope C.
  Proof.
    apply Forall_cons.
  Qed.

  Lemma tmc_ctx_fill_scoped C e scope :
    tmc_ctx_scoped scope C →
    data_expr_scoped scope e →
    data_expr_scoped scope (C @@ e).
  Proof.
    move: e. induction C as [| c C IH] => e HC He; first done.
    apply tmc_ctx_scoped_cons_inv in HC as (Hc & HC).
    rewrite tmc_ctx_fill_cons.
    apply IH; first done.
    apply tmc_ctxi_fill_scoped; done.
  Qed.
  Lemma tmc_ctx_scoped_lift1 scope C :
    tmc_ctx_scoped scope C →
    tmc_ctx_scoped (S scope) C.|[ren (+1)].
  Proof.
    intros H.
    apply Forall_fmap, (Forall_impl _ _ _ H), tmc_ctxi_scoped_lift1.
  Qed.
End tmc_ctx.

#[global] Hint Rewrite tmc_ctx_hsubst_cons : autosubst.
#[global] Hint Rewrite tmc_ctx_hsubst_comp : autosubst.
#[global] Hint Rewrite tmc_ctx_fill_subst : autosubst.

#[global] Hint Resolve tmc_ctx_scoped_nil : core.

Section tmc_rctxi.
  Implicit Types c : tmc_rctxi.

  #[global] Instance tmc_rctxi_to_ctxi_inj :
    Inj (=) (=) tmc_rctxi_to_ctxi.
  Proof.
    intros [] []. naive_solver.
  Qed.

  Lemma tmc_rctxi_hsubst c ς :
    (c : tmc_ctxi).|[ς] = c.
  Proof.
    done.
  Qed.
End tmc_rctxi.

#[global] Hint Rewrite tmc_rctxi_hsubst : autosubst.

Section tmc_rctx.
  Implicit Types C : tmc_rctx.

  #[global] Instance tmc_rctx_to_ctx_inj :
    Inj (=) (=) tmc_rctx_to_ctx.
  Proof.
    apply _.
  Qed.

  Lemma tmc_rctx_hsubst C ς :
    (C : tmc_ctx).|[ς] = C.
  Proof.
    induction C as [| c C IH]; first done.
    rewrite tmc_ctx_hsubst_cons tmc_rctxi_hsubst IH //.
  Qed.
End tmc_rctx.

#[global] Hint Rewrite tmc_rctx_hsubst : autosubst.

Section tmc_expr.
  Context (ξ : tmc_mapping).

  Lemma tmc_expr_dir_refl e :
    tmc_expr_dir ξ e e.
  Proof.
    induction e; auto with tmc.
  Qed.

  Lemma tmc_expr_subst :
    ( ∀ eₛ eₜ,
      tmc_expr_dir ξ eₛ eₜ →
      ∀ eₛ' eₜ' ς,
      eₛ' = eₛ.[ς] →
      eₜ' = eₜ.[ς] →
      tmc_expr_dir ξ eₛ' eₜ'
    ) ∧ (
      ∀ dst idx C eₛ eₜ,
      tmc_expr_dps ξ dst idx C eₛ eₜ →
      ∀ dst' idx' C' eₛ' eₜ' ς,
      dst' = dst.[ς] →
      idx' = idx.[ς] →
      C' = C.|[ς] →
      eₛ' = eₛ.[ς] →
      eₜ' = eₜ.[ς] →
      tmc_expr_dps ξ dst' idx' C' eₛ' eₜ'
    ).
  Proof.
    apply tmc_expr_ind; try solve
    [ intros; simplify;
      eauto using tmc_expr_dir_refl with tmc
    | intros * ? ? ? IHdps **; simplify;
      econstructor; try naive_solver; try apply IHdps with (up ς); autosubst
    | intros * ? IHdps1 ? IHdps2 **; simplify;
      econstructor;
      [ apply IHdps1 with (up ς); autosubst
      | apply IHdps2 with (up ς); autosubst
      | autosubst
      ]
    ].
    - intros. simplify.
      econstructor; [naive_solver | asimpl; done].
    - intros * ? IHdps **. simplify.
      econstructor; first apply IHdps with (up ς); autosubst.
  Qed.
  Lemma tmc_expr_dir_subst ς eₛ eₛ' eₜ eₜ' :
    tmc_expr_dir ξ eₛ eₜ →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    tmc_expr_dir ξ eₛ' eₜ'.
  Proof.
    eauto using (proj1 tmc_expr_subst).
  Qed.
  Lemma tmc_expr_dps_subst ς dst dst' idx idx' C C' eₛ eₛ' eₜ eₜ' :
    tmc_expr_dps ξ dst idx C eₛ eₜ →
    dst' = dst.[ς] →
    idx' = idx.[ς] →
    eₛ' = eₛ.[ς] →
    eₜ' = eₜ.[ς] →
    C' = C.|[ς] →
    tmc_expr_dps ξ dst' idx' C' eₛ' eₜ'.
  Proof.
    eauto using (proj2 tmc_expr_subst).
  Qed.

  Lemma data_expr_scoped_tmc_expr :
    ( ∀ eₛ eₜ,
      tmc_expr_dir ξ eₛ eₜ →
      ∀ scope,
      data_expr_scoped scope eₛ →
      data_expr_scoped scope eₜ
    ) ∧ (
      ∀ dst idx C eₛ eₜ,
      tmc_expr_dps ξ dst idx C eₛ eₜ →
      ∀ scope,
      data_expr_scoped scope dst →
      data_expr_scoped scope idx →
      tmc_ctx_scoped scope C →
      data_expr_scoped scope eₛ →
      data_expr_scoped scope eₜ
    ).
  Proof.
    apply tmc_expr_ind; try naive_solver.
    - intros * Hdir1 IH1 Hdps2 IH2 scope (Hscoped1 & Hscoped2).
      simpl. split_and!; try naive_solver lia.
      apply IH2; try naive_solver auto with lia.
      apply data_expr_scoped_lift1. done.
    - intros * Hdir2 IH2 Hdps1 IH1 scope (Hscoped1 & Hscoped2).
      simpl. split_and!; try naive_solver lia.
      apply IH1; try naive_solver auto with lia.
      apply data_expr_scoped_lift1. done.
    - intros * Hdps1 IH1 Hdps2 IH2 -> scope (Hscoped1 & Hscoped2).
      simpl. split_and!; try lia.
      + apply IH1; try naive_solver auto with lia.
        apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1.
        apply IH2; try naive_solver auto with lia.
        apply data_expr_scoped_lift1. done.
    - intros * Hdir IH -> scope Hdst Hidx HC Heₛ.
      split_and!; try naive_solver.
      auto using tmc_ctx_fill_scoped.
    - intros * Hdir1 IH1 Hdps2 IH2 scope Hdst Hidx HC (Hscoped1 & Hscoped2).
      split; first auto.
      apply IH2; try done.
      + apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
      + apply tmc_ctx_scoped_lift1. done.
    - intros * Hξ Hdir IH -> scope Hdst Hidx HC (_ & Hscoped).
      simpl. split_and!; [eauto using data_expr_scoped_lift1.. | lia].
    - intros * Hdir1 IH1 Hdps2 IH2 -> scope Hdst Hidx HC (Hscoped1 & Hscoped2).
      split; first auto.
      apply IH2; try done.
      + apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
      + apply tmc_ctx_scoped_cons.
        * cbn. lia.
        * apply tmc_ctx_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
    - intros * Hdir1 IH1 Hdps2 IH2 -> scope Hdst Hidx HC (Hscoped1 & Hscoped2).
      split; first auto.
      apply IH2; try done.
      + apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
      + apply tmc_ctx_scoped_cons.
        * cbn. lia.
        * apply tmc_ctx_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
    - intros * Hdps IH -> scope Hdst Hidx (Hc & HC)%tmc_ctx_scoped_cons_inv Heₛ.
      simpl. split_and!.
      + apply tmc_ctxi_fill_scoped; done.
      + apply data_expr_scoped_lift1. done.
      + apply data_expr_scoped_lift1. done.
      + apply tmc_ctx_fill_scoped.
        * apply tmc_ctx_scoped_lift1. done.
        * simpl. lia.
      + apply data_expr_scoped_lift1, IH; try naive_solver auto with lia.
        apply data_expr_scoped_lift1. done.
  Qed.
  Lemma data_expr_scoped_tmc_expr_dir scope eₛ eₜ :
    tmc_expr_dir ξ eₛ eₜ →
    data_expr_scoped scope eₛ →
    data_expr_scoped scope eₜ.
  Proof.
    eauto using (proj1 data_expr_scoped_tmc_expr).
  Qed.
  Lemma data_expr_scoped_tmc_expr_dps scope dst idx C eₛ eₜ :
    tmc_expr_dps ξ dst idx C eₛ eₜ →
    data_expr_scoped scope dst →
    data_expr_scoped scope idx →
      tmc_ctx_scoped scope C →
    data_expr_scoped scope eₛ →
    data_expr_scoped scope eₜ.
  Proof.
    eauto using (proj2 data_expr_scoped_tmc_expr).
  Qed.
End tmc_expr.

#[global] Hint Resolve tmc_expr_dir_refl : tmc.

Lemma data_program_scoped_tmc progₛ progₜ :
  tmc progₛ progₜ →
  data_program_scoped progₛ →
  data_program_scoped progₜ.
Proof.
  intros tmc. rewrite /data_program_scoped !map_Forall_lookup. intros Hscoped func defₜ Hfuncₜ.
  apply elem_of_dom_2 in Hfuncₜ as Hfuncₜ'. rewrite tmc.(tmc_dom) elem_of_union in Hfuncₜ'.
  destruct Hfuncₜ' as [Hfuncₛ%lookup_lookup_total_dom | (func_dir & Hξ)%elem_of_map_img].
  - edestruct tmc.(tmc_dir) as (eₜ & Hdir & Heq); first done.
    eapply data_expr_scoped_tmc_expr_dir; last naive_solver.
    rewrite Heq in Hfuncₜ. naive_solver.
  - pose proof Hξ as Hfunc_dirₛ%elem_of_dom_2%(tmc.(tmc_ξ_dom))%lookup_lookup_total_dom.
    edestruct tmc.(tmc_dps) as (eₜ & Hdps & Heq); [done.. |].
    rewrite Hfuncₜ in Heq. simplify.
    repeat constructor. eapply data_expr_scoped_tmc_expr_dps; [naive_solver.. |].
    apply (data_expr_scoped_le 1); naive_solver lia.
Qed.
