From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  syntax.

Coercion lambda_index_to_Z (idx : lambda_index) : Z :=
  match idx with
  | Zero => 0
  | One => 1
  | Two => 2
  end.

Coercion LambdaIndex : lambda_index >-> lambda_val.
Coercion LambdaInt : Z >-> lambda_val.
Coercion LambdaBool : bool >-> lambda_val.
Coercion LambdaLoc : loc >-> lambda_val.
Coercion LambdaFunc : lambda_function >-> lambda_val.

Coercion LambdaVal : lambda_val >-> lambda_expr.
Coercion LambdaCall : lambda_expr >-> Funclass.

Notation "𝟘" := Zero.
Notation "𝟙" := One.
Notation "𝟚" := Two.

Declare Scope lambda_val_scope.
Delimit Scope lambda_val_scope with lambda_val.
Bind Scope lambda_val_scope with lambda_val.

Notation "()" := LambdaUnit
: lambda_val_scope.

Declare Scope lambda_expr_scope.
Delimit Scope lambda_expr_scope with lambda_expr.
Bind Scope lambda_expr_scope with lambda_expr.

Notation "# v" := (LambdaVal v%Z%lambda_val%stdpp)
( at level 5,
  format "# v"
).

Notation "'Fail'" := (#() #())%lambda_expr
: lambda_expr_scope.

Notation "$ x" := (LambdaVar x%nat)
( at level 5,
  format "$ x"
) : lambda_expr_scope.

Notation "'let:' e1 'in' e2" := (LambdaLet e1%lambda_expr e2%lambda_expr)
( at level 200,
  e1, e2 at level 200,
  format "'[v' 'let:'  '[' e1 ']'  'in' '/' e2 ']'"
) : lambda_expr_scope.
Notation "e1 ;; e2" := (let: e1 in e2.[ren (+1)])%lambda_expr
( at level 100,
  e2 at level 200,
  format "'[v' '[hv' '[' e1 ']'  ;; ']' '/' e2 ']'"
) : lambda_expr_scope.

Notation "~ e" := (LambdaUnop LambdaOpNeg e%lambda_expr)
: lambda_expr_scope.
Notation "- e" := (LambdaUnop LambdaOpUminus e%lambda_expr)
: lambda_expr_scope.

Notation "e1 + e2" := (LambdaBinop LambdaOpPlus e1%lambda_expr e2%lambda_expr)
: lambda_expr_scope.
Notation "e1 - e2" := (LambdaBinop LambdaOpMinus e1%lambda_expr e2%lambda_expr)
: lambda_expr_scope.
Notation "e1 * e2" := (LambdaBinop LambdaOpMult e1%lambda_expr e2%lambda_expr)
: lambda_expr_scope.
Notation "e1 `quot` e2" := (LambdaBinop LambdaOpQuot e1%lambda_expr e2%lambda_expr)
: lambda_expr_scope.
Notation "e1 `rem` e2" := (LambdaBinop LambdaOpRem e1%lambda_expr e2%lambda_expr)
: lambda_expr_scope.
Notation "e1 ≤ e2" := (LambdaBinop LambdaOpLe e1%lambda_expr e2%lambda_expr)
: lambda_expr_scope.
Notation "e1 < e2" := (LambdaBinop LambdaOpLt e1%lambda_expr e2%lambda_expr)
: lambda_expr_scope.
Notation "e1 = e2" := (LambdaBinop LambdaOpEq e1%lambda_expr e2%lambda_expr)
: lambda_expr_scope.
Notation "e1 ≠ e2" := (~ (e1 = e2))%lambda_expr
: lambda_expr_scope.

Notation "'if:' e0 'then' e1 'else' e2" := (LambdaIf e0%lambda_expr e1%lambda_expr e2%lambda_expr)
( at level 200,
  e0, e1, e2 at level 200
) : lambda_expr_scope.
Notation "e1 && e2" := (if: e1 then e2 else #false)%lambda_expr
( only parsing
) : lambda_expr_scope.
Notation "e1 || e2" := (if: e1 then #true else e2)%lambda_expr
( only parsing
) : lambda_expr_scope.

Notation "& constr" := (LambdaConstr constr)
( at level 5,
  format "& constr"
) : lambda_expr_scope.
Notation "&& constr" := (LambdaConstrDet constr)
( at level 5,
  format "&& constr"
) : lambda_expr_scope.

Notation "![ e2 ] e1" := (LambdaLoad e1%lambda_expr e2%lambda_expr)
( at level 9,
  right associativity,
  format "![ e2 ]  e1"
) : lambda_expr_scope.
Notation "! e" := (LambdaLoad e%lambda_expr 𝟘)
( at level 9,
  right associativity,
  format "! e"
) : lambda_expr_scope.

Notation "e1 <-[ e2 ]- e3" := (LambdaStore e1%lambda_expr e2%lambda_expr e3%lambda_expr)
( at level 20,
  format "e1  <-[ e2 ]-  e3"
) : lambda_expr_scope.

Definition CONSTR_PAIR := 0.
Notation "( e1 , e2 , .. , en )" := (&CONSTR_PAIR .. (&CONSTR_PAIR e1 e2) .. en)%lambda_expr
: lambda_expr_scope.

Definition CONSTR_NIL := 0.
Definition CONSTR_CONS := 1.
Notation NIL := (&CONSTR_NIL #() #())%lambda_expr (only parsing).
Notation CONS := (&CONSTR_CONS)%lambda_expr (only parsing).
Notation HEAD e := (![𝟙] e)%lambda_expr (only parsing).
Notation TAIL e := (![𝟚] e)%lambda_expr (only parsing).
Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' => e2 'end'" := (
  let: e0 in
  if: !$0 = #(Z.of_nat CONSTR_NIL) then (
    e1.[ren (+1)]
  ) else (
    let: TAIL $0 in
    let: HEAD $1 in
    e2.[$0 .: $1 .: ren (+3)]
  )
)%lambda_expr (
  only parsing,
  e0, e1, e2 at level 200
) : lambda_expr_scope.
