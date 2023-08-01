From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  syntax.

Definition constant_propagation_bindings :=
  list (option data_val).
Implicit Types bdgs : constant_propagation_bindings.

Fixpoint constant_propagation_expr bdgs e :=
  match e with
  | DataVal _ =>
      e
  | DataVar x =>
      match bdgs !! x with
      | Some (Some v) =>
          DataVal v
      | _ =>
          e
      end
  | DataLet e1 e2 =>
      let e1 := constant_propagation_expr bdgs e1 in
      match e1 with
      | DataVal v1 =>
          constant_propagation_expr (Some v1 :: bdgs) e2
      | _ =>
          let e2 := constant_propagation_expr (None :: bdgs) e2 in
          DataLet e1 e2
      end
  | DataCall e1 e2 =>
      let e1 := constant_propagation_expr bdgs e1 in
      let e2 := constant_propagation_expr bdgs e2 in
      DataCall e1 e2
  | DataUnop op e =>
      let e := constant_propagation_expr bdgs e in
      match op with
      | DataOpNeg =>
          match e with
          | DataVal (DataBool b) =>
              DataVal (DataBool (negb b))
          | DataUnop DataOpNeg e =>
              e
          | _ =>
              DataUnop DataOpNeg e
          end
      | DataOpUminus =>
          match e with
          | DataVal (DataInt n) =>
              DataVal (DataInt (- n))
          | DataUnop DataOpUminus e =>
              e
          | DataBinop op (DataVal (DataInt n1)) e2 =>
              match op with
              | DataOpPlus =>
                  DataBinop DataOpMinus (DataVal (DataInt (- n1))) e2
              | DataOpMinus =>
                  DataBinop DataOpPlus (DataVal (DataInt (- n1))) e2
              | DataOpMult =>
                  DataBinop DataOpMult (DataVal (DataInt (- n1))) e2
              (* | DataOpQuot => *)
              (* | DataOpRem => *)
              | _ =>
                  DataUnop DataOpUminus e
              end
          | _ =>
              DataUnop DataOpUminus e
          end
      end
  | DataBinop op e1 e2 =>
      let e1 := constant_propagation_expr bdgs e1 in
      let e2 := constant_propagation_expr bdgs e2 in
      match op with
      | DataOpPlus =>
          match e1, e2 with
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataInt (n1 + n2))
          | DataVal (DataInt n1), DataUnop DataOpUminus e2 =>
              DataBinop DataOpMinus (DataVal (DataInt n1)) e2
          (* | DataVal (DataInt n1), DataBinop op e21 e22 => *)
          | _, DataVal _ =>
              DataBinop DataOpPlus e2 e1
          (* | DataBinop op1 (DataVal (DataInt n1)) e1, DataBinop op2 (DataVal (DataInt n2)) e2 => *)
          | _, _ =>
              DataBinop DataOpPlus e1 e2
          end
      | DataOpMinus =>
          match e1, e2 with
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataInt (n1 - n2))
          | _, _ =>
              DataBinop DataOpMinus e1 e2
          end
      | DataOpMult =>
          match e1, e2 with
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataInt (n1 * n2))
          | _, _ =>
              DataBinop DataOpMult e1 e2
          end
      | DataOpQuot =>
          match e1, e2 with
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataInt (n1 `quot` n2))
          | _, _ =>
              DataBinop DataOpQuot e1 e2
          end
      | DataOpRem =>
          match e1, e2 with
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataInt (n1 `rem` n2))
          | _, _ =>
              DataBinop DataOpRem e1 e2
          end
      | DataOpLe =>
          match e1, e2 with
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataBool (bool_decide (n1 ≤ n2)%Z))
          | _, _ =>
              DataBinop DataOpLe e1 e2
          end
      | DataOpLt =>
          match e1, e2 with
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataBool(bool_decide (n1 < n2)%Z))
          | _, _ =>
              DataBinop DataOpLt e1 e2
          end
      | DataOpGe =>
          match e1, e2 with
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataBool (bool_decide (n1 >= n2)%Z))
          | _, _ =>
              DataBinop DataOpGe e1 e2
          end
      | DataOpGt =>
          match e1, e2 with
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataBool (bool_decide (n1 > n2)%Z))
          | _, _ =>
              DataBinop DataOpGt e1 e2
          end
      | DataOpEq =>
          match e1, e2 with
          | DataVal DataUnit, DataVal DataUnit =>
              DataVal (DataBool true)
          | DataVal (DataIndex idx1), DataVal (DataIndex idx2) =>
              DataVal (DataBool (bool_decide (idx1 = idx2)))
          | DataVal (DataTag tag1), DataVal (DataTag tag2) =>
              DataVal (DataBool (bool_decide (tag1 = tag2)))
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataBool (bool_decide (n1 = n2)))
          | DataVal (DataBool b1), DataVal (DataBool b2) =>
              DataVal (DataBool (bool_decide (b1 = b2)))
          | DataVal (DataLoc l1), DataVal (DataLoc l2) =>
              DataVal (DataBool (bool_decide (l1 = l2)))
          | DataVal (DataFunc func1 _), DataVal (DataFunc func2 _) =>
              DataVal (DataBool (bool_decide (func1 = func2)))
          | _, _ =>
              DataBinop DataOpEq e1 e2
          end
      | DataOpNe =>
          match e1, e2 with
          | DataVal DataUnit, DataVal DataUnit =>
              DataVal (DataBool false)
          | DataVal (DataIndex idx1), DataVal (DataIndex idx2) =>
              DataVal (DataBool (bool_decide (idx1 ≠ idx2)))
          | DataVal (DataTag tag1), DataVal (DataTag tag2) =>
              DataVal (DataBool (bool_decide (tag1 ≠ tag2)))
          | DataVal (DataInt n1), DataVal (DataInt n2) =>
              DataVal (DataBool (bool_decide (n1 ≠ n2)))
          | DataVal (DataBool b1), DataVal (DataBool b2) =>
              DataVal (DataBool (bool_decide (b1 ≠ b2)))
          | DataVal (DataLoc l1), DataVal (DataLoc l2) =>
              DataVal (DataBool (bool_decide (l1 ≠ l2)))
          | DataVal (DataFunc func1 _), DataVal (DataFunc func2 _) =>
              DataVal (DataBool (bool_decide (func1 ≠ func2)))
          | _, _ =>
              DataBinop DataOpNe e1 e2
          end
      end
  | DataBinopDet op e1 e2 =>
      let e1 := constant_propagation_expr bdgs e1 in
      let e2 := constant_propagation_expr bdgs e2 in
      DataBinopDet op e1 e2
  | DataIf e0 e1 e2 =>
      let e0 := constant_propagation_expr bdgs e0 in
      match e0 with
      | DataVal (DataBool b0) =>
          if b0
          then constant_propagation_expr bdgs e1
          else constant_propagation_expr bdgs e2
      | DataUnop DataOpNeg e0 =>
          DataIf e0 e2 e1
      | _ =>
          let e1 := constant_propagation_expr bdgs e1 in
          let e2 := constant_propagation_expr bdgs e2 in
          DataIf e0 e1 e2
      end
  | DataConstr tag e1 e2 =>
      let e1 := constant_propagation_expr bdgs e1 in
      let e2 := constant_propagation_expr bdgs e2 in
      DataConstr tag e1 e2
  | DataConstrDet tag e1 e2 =>
      let e1 := constant_propagation_expr bdgs e1 in
      let e2 := constant_propagation_expr bdgs e2 in
      DataConstrDet tag e1 e2
  | DataLoad e1 e2 =>
      let e1 := constant_propagation_expr bdgs e1 in
      let e2 := constant_propagation_expr bdgs e2 in
      DataLoad e1 e2
  | DataStore e1 e2 e3 =>
      let e1 := constant_propagation_expr bdgs e1 in
      let e2 := constant_propagation_expr bdgs e2 in
      let e3 := constant_propagation_expr bdgs e3 in
      DataStore e1 e2 e3
  end.

Definition constant_propagation (prog : data_program) :=
  constant_propagation_expr [None] <$> prog.
