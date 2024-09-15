From camlcert Require Import
  prelude.
From camlcert.common Require Export
  autosubst
  loc.
From camlcert.flam Require Export
  syntax.
From camlcert Require Import
  options.

Implicit Types i : nat.
Implicit Types n : Z.
Implicit Types l : loc.
Implicit Types symb : flam_symbol.
Implicit Types func : flam_func.
Implicit Types funcs : list flam_func.
Implicit Types x f : flam_var.
Implicit Types k : flam_cont.
Implicit Types simple : flam_simple.
Implicit Types simples : list flam_simple.
Implicit Types mut : flam_mut.
Implicit Types rec : flam_rec.
Implicit Types tag : flam_tag.
Implicit Types named : flam_named.
Implicit Types arity : flam_arity.
Implicit Types arm : flam_arm.
Implicit Types arms : gmap flam_tag flam_arm.
Implicit Types tm : flam_term.

Unset Elimination Schemes.
Inductive flam_const :=
  | FlamConstInt n
  | FlamConstBlock tag (consts : list flam_const).
Set Elimination Schemes.
Implicit Types const : flam_const.
Implicit Types consts : list flam_const.

Section flam_const_ind.
  Variable P : flam_const → Prop.

  Variable HInt :
    ∀ n,
    P (FlamConstInt n).
  Variable HBlock :
    ∀ tag,
    ∀ consts, Forall P consts →
    P (FlamConstBlock tag consts).

  Fixpoint flam_const_ind const :=
    match const with
    | FlamConstInt n =>
        HInt n
    | FlamConstBlock tag consts =>
        HBlock tag
          consts (Forall_true P consts flam_const_ind)
    end.
End flam_const_ind.

Record flam_prog := {
  flam_prog_symbols : gmap flam_symbol flam_const ;
  flam_prog_funcs : gmap flam_func (flam_arity * flam_term) ;
}.
Implicit Types prog : flam_prog.

Unset Elimination Schemes.
Inductive flam_val :=
  | FlamValInt n
  | FlamValLoc l
  | FlamValBlock tag (vs : list flam_val)
  | FlamValClos funcs (vs : list flam_val) i.
Set Elimination Schemes.
Implicit Types v : flam_val.
Implicit Types vs ws : list flam_val.

Section flam_val_ind.
  Variable P : flam_val → Prop.

  Variable HInt :
    ∀ n,
    P (FlamValInt n).
  Variable HLoc :
    ∀ l,
    P (FlamValLoc l).
  Variable HBlock :
    ∀ tag,
    ∀ vs, Forall P vs →
    P (FlamValBlock tag vs).
  Variable HClos :
    ∀ funcs,
    ∀ vs, Forall P vs →
    ∀ i,
    P (FlamValClos funcs vs i).

  Fixpoint flam_val_ind v :=
    match v with
    | FlamValInt n =>
        HInt n
    | FlamValLoc l =>
        HLoc l
    | FlamValBlock tag vs =>
        HBlock
          tag
          vs (Forall_true P vs flam_val_ind)
    | FlamValClos funcs vs i =>
        HClos
          funcs
          vs (Forall_true P vs flam_val_ind)
          i
    end.
End flam_val_ind.

Definition FlamValBool b :=
  FlamValInt (Z.b2z b).
Definition FlamValNat (n : nat) :=
  FlamValInt (Z.of_nat n).
Definition FlamValTag tag :=
  FlamValNat tag.
Definition FlamValUnit :=
  FlamValInt 0.

#[global] Instance flam_val_inhabited : Inhabited flam_val :=
  populate FlamValUnit.

Fixpoint flam_val_of_const const :=
  match const with
  | FlamConstInt n =>
      FlamValInt n
  | FlamConstBlock tag consts =>
      FlamValBlock tag (flam_val_of_const <$> consts)
  end.
#[global] Arguments flam_val_of_const !_ / : assert.

Definition flam_val_neq v1 v2 :=
  match v1 with
  | FlamValInt n1 =>
      match v2 with
      | FlamValInt n2 =>
          n1 ≠ n2
      | _ =>
          True
      end
  | FlamValLoc l1 =>
      match v2 with
      | FlamValLoc l2 =>
          l1 ≠ l2
      | _ =>
          True
      end
  | FlamValBlock _ _
  | FlamValClos _ _ _ =>
      True
  end.
#[global] Arguments flam_val_neq !_ !_ / : assert.

Inductive flam_env :=
  FlamEnv (vals : flam_var → flam_val) (conts : flam_cont → flam_continuation)
with flam_continuation :=
  | FlamContinuation0
  | FlamContinuation rec arity tm (env : flam_env).
Implicit Types env : flam_env.
Implicit Types cont : flam_continuation.

Scheme flam_env_mutind :=
  Induction for flam_env Sort Prop
with flam_continuation_mutind :=
  Induction for flam_continuation Sort Prop.
Combined Scheme flam_env_continuation_mutind from
  flam_env_mutind,
  flam_continuation_mutind.

Definition flam_env_vals env :=
  match env with
  | FlamEnv vals _ =>
      vals
  end.
#[global] Arguments flam_env_vals !_ /.
Notation "env '.(flam_env_vals)'" := (
  flam_env_vals env
)(at level 2,
  left associativity,
  format "env .(flam_env_vals)"
) : stdpp_scope.
Definition flam_env_conts env :=
  match env with
  | FlamEnv _ conts =>
      conts
  end.
#[global] Arguments flam_env_conts !_ /.
Notation "env '.(flam_env_conts)'" := (
  flam_env_conts env
)(at level 2,
  left associativity,
  format "env .(flam_env_conts)"
) : stdpp_scope.

Definition flam_env_update_vals fn env :=
  FlamEnv
    (fn env.(flam_env_vals))
    env.(flam_env_conts).
Definition flam_env_update_conts fn env :=
  FlamEnv
    env.(flam_env_vals)
    (fn env.(flam_env_conts)).

Definition flam_env_push_val v env :=
  flam_env_update_vals (λ vals, v .: vals) env.
Definition flam_env_push_cont cont env :=
  flam_env_update_conts (λ conts, cont .: conts) env.

Definition flam_env_push_vals vals env :=
  flam_env_update_vals (λ vals', vals .+ vals') env.
Definition flam_env_push_conts conts env :=
  flam_env_update_conts (λ conts', conts .+ conts') env.

#[global] Instance flam_continuation_inhabited : Inhabited flam_continuation :=
  populate FlamContinuation0.
#[global] Instance flam_env_inhabited : Inhabited flam_env :=
  populate (FlamEnv inhabitant inhabitant).

Record flam_header := FlamHeader {
  flam_header_tag : flam_tag ;
  flam_header_size : nat ;
}.
Add Printing Constructor flam_header.
Implicit Types hdr : flam_header.

Record flam_state := {
  flam_state_headers : gmap loc flam_header ;
  flam_state_heap : gmap loc flam_val ;
}.
Implicit Types σ : flam_state.

Definition flam_state_update_heap fn σ :=
  {|flam_state_headers := σ.(flam_state_headers) ;
    flam_state_heap := fn σ.(flam_state_heap) ;
  |}.
Definition flam_state_update_headers fn σ :=
  {|flam_state_headers := fn σ.(flam_state_headers) ;
    flam_state_heap := σ.(flam_state_heap) ;
  |}.

Definition flam_eval_simple prog env simple :=
  match simple with
  | FlamSymbol symb =>
      flam_val_of_const <$> prog.(flam_prog_symbols) !! symb
  | FlamInt n =>
      Some $ FlamValInt n
  | FlamVar x =>
      Some $ env.(flam_env_vals) x
  end.
#[global] Arguments flam_eval_simple _ _ !_ / : assert.

Definition flam_eval_op1 op n :=
  match op with
  | FlamNeg =>
      - n
  | FlamNot =>
      if decide (n = 0) then 1 else 0
  end%Z.
#[global] Arguments flam_eval_op1 !_ _ / : assert.

Definition flam_eval_prim1 σ prim v :=
  match prim with
  | FlamIsInt =>
      Some
        match v with
        | FlamValInt _ =>
            FlamValBool true
        | _ =>
            FlamValBool false
        end
  | FlamTag =>
      match v with
      | FlamValBlock tag _ =>
          Some $ FlamValTag tag
      | FlamValLoc l =>
          hdr ← σ.(flam_state_headers) !! l ;
          Some $ FlamValTag hdr.(flam_header_tag)
      | _ =>
          None
      end
  | FlamSize =>
      match v with
      | FlamValBlock _ vs =>
          Some $ FlamValNat $ length vs
      | FlamValLoc l =>
          hdr ← σ.(flam_state_headers) !! l ;
          Some $ FlamValNat hdr.(flam_header_size)
      | _ =>
          None
      end
  | FlamOp1 op =>
      match v with
      | FlamValInt n =>
          Some $ FlamValInt $ flam_eval_op1 op n
      | _ =>
          None
      end
  | FlamClosVal i1 i2 =>
      match v with
      | FlamValClos _ vs i =>
          if decide (i = i1) then
            vs !! i2
          else
            None
      | _ =>
          None
      end
  | FlamClosFunc i1 i2 =>
      match v with
      | FlamValClos funcs vs i =>
          if decide (i = i1) then
            Some $ FlamValClos funcs vs i2
          else
            None
      | _ =>
          None
      end
  end.
#[global] Arguments flam_eval_prim1 _ !_ _ / : assert.

Definition flam_eval_op2 op n1 n2 :=
  match op with
  | FlamPlus =>
      n1 + n2
  | FlamMinus =>
      n1 - n2
  | FlamMult =>
      n1 * n2
  | FlamQuot =>
      n1 `quot` n2
  | FlamRem =>
      n1 `rem` n2
  | FlamLe =>
      Z.b2z $ bool_decide (n1 ≤ n2)
  | FlamLt =>
      Z.b2z $ bool_decide (n1 < n2)
  | FlamGe =>
      Z.b2z $ bool_decide (n1 >= n2)
  | FlamGt =>
      Z.b2z $ bool_decide (n1 > n2)
  end%Z.
#[global] Arguments flam_eval_op2 !_ _ _ / : assert.

Definition flam_eval_prim2 σ prim v1 v2 :=
  match prim with
  | FlamOp2 op =>
      match v1, v2 with
      | FlamValInt n1, FlamValInt n2 =>
          Some $ FlamValInt $ flam_eval_op2 op n1 n2
      | _, _ =>
          None
      end
  | FlamEqual =>
      None
  | FlamLoad =>
      match v2 with
      | FlamValInt i =>
          if decide (0 ≤ i)%Z then
            match v1 with
            | FlamValBlock _ vs =>
                vs !! Z.to_nat i
            | FlamValLoc l =>
                σ.(flam_state_heap) !! (l +ₗ i)
            | _ =>
                None
            end
          else
            None
      | _ =>
          None
      end
  end.
#[global] Arguments flam_eval_prim2 _ !_ _ _ / : assert.

Definition flam_eval_prim3 σ op v1 v2 v3 :=
  match op with
  | FlamStore =>
      match v2 with
      | FlamValInt i =>
          if decide (0 ≤ i)%Z then
            match v1 with
            | FlamValLoc l =>
                σ.(flam_state_heap) !! (l +ₗ i) ;;
                let σ := flam_state_update_heap (insert (l +ₗ i) v3) σ in
                Some (σ, FlamValUnit)
            | _ =>
                None
            end
          else
            None
      | _ =>
          None
      end
  end.
#[global] Arguments flam_eval_prim3 _ !_ _ _ _ / : assert.

Definition flam_eval_prim prim vs :=
  match prim with
  | FlamBlock Immutable tag =>
      if decide (0 < length vs) then
        Some $ FlamValBlock tag vs
      else
        None
  | FlamBlock Mutable _ =>
      None
  end.
#[global] Arguments flam_eval_prim !_ _ : assert.

Definition flam_eval_named prog σ env named :=
  match named with
  | FlamSimple simple =>
      v ← flam_eval_simple prog env simple ;
      Some (σ, v)
  | FlamPrim1 prim simple =>
      v ← flam_eval_simple prog env simple ;
      res ← flam_eval_prim1 σ prim v ;
      Some (σ, res)
  | FlamPrim2 prim simple1 simple2 =>
      v1 ← flam_eval_simple prog env simple1 ;
      v2 ← flam_eval_simple prog env simple2 ;
      res ← flam_eval_prim2 σ prim v1 v2 ;
      Some (σ, res)
  | FlamPrim3 prim simple1 simple2 simple3 =>
      v1 ← flam_eval_simple prog env simple1 ;
      v2 ← flam_eval_simple prog env simple2 ;
      v3 ← flam_eval_simple prog env simple3 ;
      flam_eval_prim3 σ prim v1 v2 v3
  | FlamPrim prim simples =>
      None
  end.
#[global] Arguments flam_eval_named _ _ _ !_ / : assert.

Fixpoint flam_heap_array l vs : gmap loc flam_val :=
  match vs with
  | [] =>
      ∅
  | v :: vs =>
      <[l := v]> (flam_heap_array (l +ₗ 1) vs)
  end.
#[global] Arguments flam_heap_array _ !_ / : assert.

Definition flam_state_alloc l hdr vs σ :=
  {|flam_state_headers := <[l := hdr]> σ.(flam_state_headers) ;
    flam_state_heap := flam_heap_array l vs ∪ σ.(flam_state_heap) ;
  |}.

Inductive flam_step prog : flam_env → flam_term → flam_state → flam_env → flam_term → flam_state → Prop :=
  | flam_step_let env named tm σ σ' v :
      flam_eval_named prog σ env named = Some (σ', v) →
      flam_step prog
        env
        (FlamLet named tm)
        σ
        (flam_env_push_val v env)
        tm
        σ'
  | flam_step_let_equal_fail env simple1 v1 simple2 v2 tm σ :
      flam_eval_simple prog env simple1 = Some v1 →
      flam_eval_simple prog env simple2 = Some v2 →
      flam_val_neq v1 v2 →
      flam_step prog
        env
        (FlamLet (FlamPrim2 FlamEqual simple1 simple2) tm)
        σ
        (flam_env_push_val (FlamValBool false) env)
        tm
        σ
  | flam_step_let_equal_suc env simple1 v1 simple2 v2 tm σ :
      flam_eval_simple prog env simple1 = Some v1 →
      flam_eval_simple prog env simple2 = Some v2 →
      v1 = v2 →
      flam_step prog
        env
        (FlamLet (FlamPrim2 FlamEqual simple1 simple2) tm)
        σ
        (flam_env_push_val (FlamValBool true) env)
        tm
        σ
  | flam_step_let_block env tag simples vs tm σ l :
      0 < length simples →
      (flam_eval_simple prog env) <$> simples = Some <$> vs →
      σ.(flam_state_headers) !! l = None →
      ( ∀ i,
        i < length simples →
        σ.(flam_state_heap) !! (l +ₗ Z.of_nat i) = None
      ) →
      flam_step prog
        env
        (FlamLet (FlamPrim (FlamBlock Mutable tag) simples) tm)
        σ
        (flam_env_push_val (FlamValLoc l) env)
        tm
        (flam_state_alloc l (FlamHeader tag (length simples)) vs σ)
  | flam_step_letclos env funcs simples vs tm σ :
      (flam_eval_simple prog env) <$> simples = Some <$> vs →
      flam_step prog
        env
        (FlamLetClos funcs simples tm)
        σ
        (flam_env_push_vals (FlamValClos funcs vs <$> seq 0 (length funcs)) env)
        tm
        σ
  | flam_step_letcont env rec arity tm1 tm2 σ :
      flam_step prog
        env
        (FlamLetCont rec arity tm1 tm2)
        σ
        (flam_env_push_cont (FlamContinuation rec arity tm1 env) env)
        tm2
        σ
  | flam_step_apply env kind f func k1 cont1 k2 cont2 simples vs σ arity tm funcs ws i :
      prog.(flam_prog_funcs) !! func = Some (arity, tm) →
      length simples = arity →
      env.(flam_env_vals) f = FlamValClos funcs ws i →
      funcs !! i = Some func →
      (if kind is FlamDirect func' then func' = func else True) →
      (flam_eval_simple prog env) <$> simples = Some <$> vs →
      env.(flam_env_conts) k1 = cont1 →
      env.(flam_env_conts) k2 = cont2 →
      flam_step prog
        env
        (FlamApply kind f simples k1 k2)
        σ
        (flam_env_push_conts [cont1; cont2] $ flam_env_push_vals (FlamValClos funcs ws i :: vs) inhabitant)
        tm
        σ
  | flam_step_applycont env k simples vs σ rec arity tm env' :
      let cont := FlamContinuation rec arity tm env' in
      env.(flam_env_conts) k = cont →
      length simples = arity →
      (flam_eval_simple prog env) <$> simples = Some <$> vs →
      flam_step prog
        env
        (FlamApplyCont (FlamCont k) simples)
        σ
        ( let env' := flam_env_push_vals vs env' in
          if rec then flam_env_push_cont cont env' else env'
        )
        tm
        σ
  | flam_step_switch env simple i arms σ arm :
      flam_eval_simple prog env simple = Some (FlamValInt (Z.of_nat i)) →
      arms !! i = Some arm →
      flam_step prog
        env
        (FlamSwitch simple arms)
        σ
        env
        (FlamApplyCont arm.(flam_arm_cont) arm.(flam_arm_args))
        σ.
