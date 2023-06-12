From simuliris Require Import
  prelude.
From simuliris.language Require Export
  syntax.

Coercion Int : Z >-> val.
Coercion Bool : bool >-> val.
Coercion Loc : loc >-> val.
Coercion Func : function >-> val.

Coercion Val : val >-> expr.
Coercion Call : expr >-> Funclass.

Declare Scope val_scope.
Delimit Scope val_scope with V.
Bind Scope val_scope with val.

Notation "()" := Unit
: val_scope.

Declare Scope expr_scope.
Delimit Scope expr_scope with E.
Bind Scope expr_scope with expr.

Notation "# v" := (Val v%Z%V%stdpp)
( at level 5,
  format "# v"
).

Notation Fail := (#() #())%E.

Notation "$ x" := (Var x%nat)
( at level 5,
  format "$ x"
) : expr_scope.

Notation "'let:' e1 'in' e2" := (Let e1%E e2%E)
( at level 200,
  e1, e2 at level 200,
  format "'[v' 'let:'  '[' e1 ']'  'in' '/' e2 ']'"
) : expr_scope.
Notation "e1 ;; e2" := (let: e1 in e2.[ren (+1)])%E
( at level 100,
  e2 at level 200,
  format "'[v' '[hv' '[' e1 ']'  ;; ']' '/' e2 ']'"
) : expr_scope.

Notation "~ e" := (Unop OpNeg e%E)
: expr_scope.
Notation "- e" := (Unop OpUminus e%E)
: expr_scope.

Notation "e1 + e2" := (Binop OpPlus e1%E e2%E)
: expr_scope.
Notation "e1 - e2" := (Binop OpMinus e1%E e2%E)
: expr_scope.
Notation "e1 * e2" := (Binop OpMult e1%E e2%E)
: expr_scope.
Notation "e1 `quot` e2" := (Binop OpQuot e1%E e2%E)
: expr_scope.
Notation "e1 `rem` e2" := (Binop OpRem e1%E e2%E)
: expr_scope.
Notation "e1 ≤ e2" := (Binop OpLe e1%E e2%E)
: expr_scope.
Notation "e1 < e2" := (Binop OpLt e1%E e2%E)
: expr_scope.
Notation "e1 = e2" := (Binop OpEq e1%E e2%E)
: expr_scope.
Notation "e1 ≠ e2" := (~ (e1 = e2))%E
: expr_scope.
Notation "e1 +ₗ e2" := (Binop OpOffset e1%E e2%E)
: expr_scope.

Notation "'if:' e0 'then' e1 'else' e2" := (If e0%E e1%E e2%E)
( at level 200,
  e0, e1, e2 at level 200
) : expr_scope.
Notation "e1 && e2" := (if: e1 then e2 else #false)%E
( only parsing
) : expr_scope.
Notation "e1 || e2" := (if: e1 then #true else e2)%E
( only parsing
) : expr_scope.

Notation "& constr" := (Constr constr)
( at level 5,
  format "& constr"
) : expr_scope.
Notation "&& constr" := (ConstrDet constr)
( at level 5,
  format "&& constr"
) : expr_scope.

Notation "! e" := (Load e%E)
( at level 9,
  right associativity
) : expr_scope.

Notation "e1 <- e2" := (Store e1%E e2%E)
( at level 20
) : expr_scope.

Notation "e .(1)" := (e +ₗ #1)%E
( at level 6,
  left associativity,
  format "e .(1)"
) : expr_scope.
Notation "e .(2)" := (e +ₗ #2)%E
( at level 6,
  left associativity,
  format "e .(2)"
) : expr_scope.

Definition CONSTR_PAIR := 0.
Notation "( e1 , e2 , .. , en )" := (&CONSTR_PAIR .. (&CONSTR_PAIR e1 e2) .. en)%E
: expr_scope.
Notation FST e := (!e.(1))%E (only parsing).
Notation SND e := (!e.(2))%E (only parsing).

Definition CONSTR_NIL := 0.
Definition CONSTR_CONS := 1.
Notation NIL := (&CONSTR_NIL #() #())%E (only parsing).
Notation CONS := (&CONSTR_CONS)%E (only parsing).
Notation HEAD e := e.(1)%E (only parsing).
Notation TAIL e := e.(2)%E (only parsing).
Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' => e2 'end'" := (
  let: e0 in
  if: !$0 = #(Z.of_nat CONSTR_NIL) then (
    e1.[ren (+1)]
  ) else (
    let: TAIL $0 in
    let: HEAD $1 in
    e2.[$0 .: $1 .: ren (+1)]
  )
)%E (
  only parsing,
  e0, e1, e2 at level 200
) : expr_scope.
