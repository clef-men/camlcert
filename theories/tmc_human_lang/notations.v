From simuliris Require Import
  prelude.
From simuliris.tmc_lang Require Export
  notations.
From simuliris.tmc_human_lang Require Export
  syntax.

Coercion HumanIndex : index >-> human_val.
Coercion HumanInt : Z >-> human_val.
Coercion HumanBool : bool >-> human_val.

Coercion HumanVal : human_val >-> human_expr.
Coercion HumanVar : name >-> human_expr.
Coercion HumanCall : human_expr >-> Funclass.

Declare Scope human_val_scope.
Delimit Scope human_val_scope with HV.
Bind Scope human_val_scope with human_val.

Notation "()" := HumanUnit
: human_val_scope.

Declare Scope human_expr_scope.
Delimit Scope human_expr_scope with HE.
Bind Scope human_expr_scope with human_expr.

Notation "#ₕ v" := (HumanVal v%Z%HV%stdpp)
( at level 5,
  format "#ₕ v"
).

Notation "'Fail'" := (#ₕ() #ₕ())%HE
: human_expr_scope.

Notation "$ x" := (HumanFunc x)
( at level 5,
  format "$ x"
) : human_expr_scope.

Notation "'let:' x := e1 'in' e2" := (HumanLet x%binder e1%HE e2%HE)
( at level 200,
  x at level 1,
  e1, e2 at level 200,
  format "'[v' 'let:'  x  :=  '[' e1 ']'  'in' '/' e2 ']'"
) : human_expr_scope.
Notation "e1 ;; e2" := (HumanLet BAnon e1%HE e2%HE)
( at level 100,
  e2 at level 200,
  format "'[v' '[hv' '[' e1 ']'  ;; ']' '/' e2 ']'"
) : human_expr_scope.

Notation "~ e" := (HumanUnop OpNeg e%HE)
: human_expr_scope.
Notation "- e" := (HumanUnop OpUminus e%HE)
: human_expr_scope.

Notation "e1 + e2" := (HumanBinop OpPlus e1%HE e2%HE)
: human_expr_scope.
Notation "e1 - e2" := (HumanBinop OpMinus e1%HE e2%HE)
: human_expr_scope.
Notation "e1 * e2" := (HumanBinop OpMult e1%HE e2%HE)
: human_expr_scope.
Notation "e1 `quot` e2" := (HumanBinop OpQuot e1%HE e2%HE)
: human_expr_scope.
Notation "e1 `rem` e2" := (HumanBinop OpRem e1%HE e2%HE)
: human_expr_scope.
Notation "e1 ≤ e2" := (HumanBinop OpLe e1%HE e2%HE)
: human_expr_scope.
Notation "e1 < e2" := (HumanBinop OpLt e1%HE e2%HE)
: human_expr_scope.
Notation "e1 = e2" := (HumanBinop OpEq e1%HE e2%HE)
: human_expr_scope.
Notation "e1 ≠ e2" := (~ (e1 = e2))%HE
: human_expr_scope.

Notation "'if:' e0 'then' e1 'else' e2" := (HumanIf e0%HE e1%HE e2%HE)
( at level 200,
  e0, e1, e2 at level 200
) : human_expr_scope.
Notation "e1 && e2" := (if: e1 then e2 else #ₕfalse)%HE
( only parsing
) : human_expr_scope.
Notation "e1 || e2" := (if: e1 then #ₕtrue else e2)%HE
( only parsing
) : human_expr_scope.

Notation "& constr" := (HumanConstr constr)
( at level 5,
  format "& constr"
) : human_expr_scope.

Notation "![ e2 ] e1" := (HumanLoad e1%HE e2%HE)
( at level 9,
  right associativity,
  format "![ e2 ]  e1"
) : human_expr_scope.
Notation "! e" := (HumanLoad e%HE 𝟘)
( at level 9,
  right associativity,
  format "! e"
) : human_expr_scope.

Notation "e1 <-[ e2 ]- e3" := (HumanStore e1%HE e2%HE e3%HE)
( at level 20,
  format "e1  <-[ e2 ]-  e3"
) : human_expr_scope.

Notation "( e1 , e2 , .. , en )" := (&CONSTR_PAIR .. (&CONSTR_PAIR e1 e2) .. en)%HE
: human_expr_scope.

Notation NILₕ := (&CONSTR_NIL #ₕ() #ₕ())%HE (only parsing).
Notation CONSₕ := (&CONSTR_CONS)%HE (only parsing).
Notation HEADₕ e := (![𝟙] e)%HE (only parsing).
Notation TAILₕ e := (![𝟚] e)%HE (only parsing).
Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' x , y => e2 'end'" := (
  let: "__match" := e0 in
  if: !"__match" = #ₕ(Z.of_nat CONSTR_NIL) then (
    e1
  ) else (
    let: y := TAILₕ "__match" in
    let: x := HEADₕ "__match" in
    e2
  )
)%HE (
  only parsing,
  e0, e1, x, y, e2 at level 200
) : human_expr_scope.
