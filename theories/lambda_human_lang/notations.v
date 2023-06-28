From simuliris Require Import
  prelude.
From simuliris.lambda_lang Require Export
  notations.
From simuliris.lambda_human_lang Require Export
  syntax.

Coercion LambdaHumanIndex : lambda_index >-> lambda_human_val.
Coercion LambdaHumanInt : Z >-> lambda_human_val.
Coercion LambdaHumanBool : bool >-> lambda_human_val.

Coercion LambdaHumanVal : lambda_human_val >-> lambda_human_expr.
Coercion LambdaHumanVar : lambda_human_name >-> lambda_human_expr.
Coercion LambdaHumanCall : lambda_human_expr >-> Funclass.

Declare Scope lambda_human_val_scope.
Delimit Scope lambda_human_val_scope with lambda_human_val.
Bind Scope lambda_human_val_scope with lambda_human_val.

Notation "()" := LambdaHumanUnit
: lambda_human_val_scope.

Declare Scope lambda_human_expr_scope.
Delimit Scope lambda_human_expr_scope with lambda_human_expr.
Bind Scope lambda_human_expr_scope with lambda_human_expr.

Notation "#ₕ v" := (LambdaHumanVal v%Z%lambda_human_val%stdpp)
( at level 5,
  format "#ₕ v"
).

Notation "'Fail'" := (#ₕ() #ₕ())%lambda_human_expr
: lambda_human_expr_scope.

Notation "$ x" := (LambdaHumanFunc x)
( at level 5,
  format "$ x"
) : lambda_human_expr_scope.

Notation "'let:' x := e1 'in' e2" := (LambdaHumanLet x%binder e1%lambda_human_expr e2%lambda_human_expr)
( at level 200,
  x at level 1,
  e1, e2 at level 200,
  format "'[v' 'let:'  x  :=  '[' e1 ']'  'in' '/' e2 ']'"
) : lambda_human_expr_scope.
Notation "e1 ;; e2" := (LambdaHumanLet BAnon e1%lambda_human_expr e2%lambda_human_expr)
( at level 100,
  e2 at level 200,
  format "'[v' '[hv' '[' e1 ']'  ;; ']' '/' e2 ']'"
) : lambda_human_expr_scope.

Notation "~ e" := (LambdaHumanUnop LambdaOpNeg e%lambda_human_expr)
: lambda_human_expr_scope.
Notation "- e" := (LambdaHumanUnop LambdaOpUminus e%lambda_human_expr)
: lambda_human_expr_scope.

Notation "e1 + e2" := (LambdaHumanBinop LambdaOpPlus e1%lambda_human_expr e2%lambda_human_expr)
: lambda_human_expr_scope.
Notation "e1 - e2" := (LambdaHumanBinop LambdaOpMinus e1%lambda_human_expr e2%lambda_human_expr)
: lambda_human_expr_scope.
Notation "e1 * e2" := (LambdaHumanBinop LambdaOpMult e1%lambda_human_expr e2%lambda_human_expr)
: lambda_human_expr_scope.
Notation "e1 `quot` e2" := (LambdaHumanBinop LambdaOpQuot e1%lambda_human_expr e2%lambda_human_expr)
: lambda_human_expr_scope.
Notation "e1 `rem` e2" := (LambdaHumanBinop LambdaOpRem e1%lambda_human_expr e2%lambda_human_expr)
: lambda_human_expr_scope.
Notation "e1 ≤ e2" := (LambdaHumanBinop LambdaOpLe e1%lambda_human_expr e2%lambda_human_expr)
: lambda_human_expr_scope.
Notation "e1 < e2" := (LambdaHumanBinop LambdaOpLt e1%lambda_human_expr e2%lambda_human_expr)
: lambda_human_expr_scope.
Notation "e1 = e2" := (LambdaHumanBinop LambdaOpEq e1%lambda_human_expr e2%lambda_human_expr)
: lambda_human_expr_scope.
Notation "e1 ≠ e2" := (~ (e1 = e2))%lambda_human_expr
: lambda_human_expr_scope.

Notation "'if:' e0 'then' e1 'else' e2" := (LambdaHumanIf e0%lambda_human_expr e1%lambda_human_expr e2%lambda_human_expr)
( at level 200,
  e0, e1, e2 at level 200
) : lambda_human_expr_scope.
Notation "e1 && e2" := (if: e1 then e2 else #ₕfalse)%lambda_human_expr
( only parsing
) : lambda_human_expr_scope.
Notation "e1 || e2" := (if: e1 then #ₕtrue else e2)%lambda_human_expr
( only parsing
) : lambda_human_expr_scope.

Notation "& constr" := (LambdaHumanConstr constr)
( at level 5,
  format "& constr"
) : lambda_human_expr_scope.

Notation "![ e2 ] e1" := (LambdaHumanLoad e1%lambda_human_expr e2%lambda_human_expr)
( at level 9,
  right associativity,
  format "![ e2 ]  e1"
) : lambda_human_expr_scope.
Notation "! e" := (LambdaHumanLoad e%lambda_human_expr 𝟘)
( at level 9,
  right associativity,
  format "! e"
) : lambda_human_expr_scope.

Notation "e1 <-[ e2 ]- e3" := (LambdaHumanStore e1%lambda_human_expr e2%lambda_human_expr e3%lambda_human_expr)
( at level 20,
  format "e1  <-[ e2 ]-  e3"
) : lambda_human_expr_scope.

Notation "( e1 , e2 , .. , en )" := (&CONSTR_PAIR .. (&CONSTR_PAIR e1 e2) .. en)%lambda_human_expr
: lambda_human_expr_scope.

Notation NILₕ := (&CONSTR_NIL #ₕ() #ₕ())%lambda_human_expr (only parsing).
Notation CONSₕ := (&CONSTR_CONS)%lambda_human_expr (only parsing).
Notation HEADₕ e := (![𝟙] e)%lambda_human_expr (only parsing).
Notation TAILₕ e := (![𝟚] e)%lambda_human_expr (only parsing).
Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' x , y => e2 'end'" := (
  let: "__match" := e0 in
  if: !"__match" = #ₕ(Z.of_nat CONSTR_NIL) then (
    e1
  ) else (
    let: y := TAILₕ "__match" in
    let: x := HEADₕ "__match" in
    e2
  )
)%lambda_human_expr (
  only parsing,
  e0, e1, x, y, e2 at level 200
) : lambda_human_expr_scope.
