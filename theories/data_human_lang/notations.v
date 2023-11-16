From simuliris Require Import
  prelude.
From simuliris.data_lang Require Export
  notations.
From simuliris.data_human_lang Require Export
  syntax.

Coercion DataHumanIndex : data_index >-> data_human_val.
Coercion DataHumanTag : data_tag >-> data_human_val.
Coercion DataHumanInt : Z >-> data_human_val.
Coercion DataHumanBool : bool >-> data_human_val.

Coercion DataHumanVal : data_human_val >-> data_human_expr.
Coercion DataHumanVar : data_human_name >-> data_human_expr.
Coercion DataHumanCall : data_human_expr >-> Funclass.

Declare Scope data_human_val_scope.
Delimit Scope data_human_val_scope with data_human_val.
Bind Scope data_human_val_scope with data_human_val.

Notation "()" :=
  DataHumanUnit
: data_human_val_scope.

Declare Scope data_human_expr_scope.
Delimit Scope data_human_expr_scope with data_human_expr.
Bind Scope data_human_expr_scope with data_human_expr.

Notation "#ₕ v" := (
  DataHumanVal v%Z%data_human_val%stdpp
)(at level 5,
  format "#ₕ v"
).

Notation "'Fail'" :=
  (#ₕ() #ₕ())%data_human_expr
: data_human_expr_scope.

Notation "$ x" := (
  DataHumanFunc x []
)(at level 5,
  format "$ x"
) : data_human_expr_scope.

Notation "'let:' x := e1 'in' e2" := (
  DataHumanLet x%binder e1%data_human_expr e2%data_human_expr
)(at level 200,
  x at level 1,
  e1, e2 at level 200,
  format "'[v' 'let:'  x  :=  '[' e1 ']'  'in' '/' e2 ']'"
) : data_human_expr_scope.
Notation "e1 ;; e2" := (
  DataHumanLet BAnon e1%data_human_expr e2%data_human_expr
)(at level 100,
  e2 at level 200,
  format "'[v' '[hv' '[' e1 ']'  ;; ']' '/' e2 ']'"
) : data_human_expr_scope.

Notation "~ e" := (
  DataHumanUnop DataOpNeg e%data_human_expr
) : data_human_expr_scope.
Notation "- e" := (
  DataHumanUnop DataOpUminus e%data_human_expr
) : data_human_expr_scope.

Notation "e1 + e2" := (
  DataHumanBinop DataOpPlus e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 - e2" := (
  DataHumanBinop DataOpMinus e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 * e2" := (
  DataHumanBinop DataOpMult e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 `quot` e2" := (
  DataHumanBinop DataOpQuot e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 `rem` e2" := (
  DataHumanBinop DataOpRem e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 ≤ e2" := (
  DataHumanBinop DataOpLe e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 < e2" := (
  DataHumanBinop DataOpLt e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 ≥ e2" := (
  DataHumanBinop DataOpGe e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 > e2" := (
  DataHumanBinop DataOpGt e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 = e2" := (
  DataHumanBinop DataOpEq e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.
Notation "e1 ≠ e2" := (
  DataHumanBinop DataOpNe e1%data_human_expr e2%data_human_expr
) : data_human_expr_scope.

Notation "'if:' e0 'then' e1 'else' e2" := (
  DataHumanIf e0%data_human_expr e1%data_human_expr e2%data_human_expr
)(at level 200,
  e0, e1, e2 at level 200
) : data_human_expr_scope.
Notation "e1 && e2" :=
  (if: e1 then e2 else #ₕfalse)%data_human_expr
( only parsing
) : data_human_expr_scope.
Notation "e1 || e2" :=
  (if: e1 then #ₕtrue else e2)%data_human_expr
( only parsing
) : data_human_expr_scope.

Notation "& tag" := (
  DataHumanBlock tag
)(at level 5,
  format "& tag"
) : data_human_expr_scope.

Notation "![ e2 ] e1" := (
  DataHumanLoad e1%data_human_expr e2%data_human_expr
)(at level 9,
  right associativity,
  format "![ e2 ]  e1"
) : data_human_expr_scope.
Notation "! e" := (
  DataHumanLoad e%data_human_expr 𝟘
)(at level 9,
  right associativity,
  format "! e"
) : data_human_expr_scope.

Notation "e1 <-[ e2 ]- e3" := (
  DataHumanStore e1%data_human_expr e2%data_human_expr e3%data_human_expr
)(at level 20,
  format "e1  <-[ e2 ]-  e3"
) : data_human_expr_scope.

Notation "( e1 , e2 , .. , en )" :=
  (&data_tag_pair .. (&data_tag_pair e1 e2) .. en)%data_human_expr
: data_human_expr_scope.

Notation NILₕ :=
  (&data_tag_nil #ₕ() #ₕ())%data_human_expr
( only parsing
).
Notation CONSₕ :=
  (&data_tag_cons)%data_human_expr
( only parsing
).
Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' x , y => e2 'end'" :=
  ( let: "__match" := e0 in
    if: !"__match" = data_tag_nil then (
      e1
    ) else (
      let: y := ![𝟚] "__match" in
      let: x := ![𝟙] "__match" in
      e2
    )
  )%data_human_expr
( only parsing,
  e0, e1, x, y, e2 at level 200
) : data_human_expr_scope.

Declare Scope data_human_def_scope.
Delimit Scope data_human_def_scope with data_human_def.
Bind Scope data_human_def_scope with data_human_definition.

Notation "'rec:' annot param := body" := (
  Build_data_human_definition annot param%binder body%data_human_expr
)(at level 200,
  annot at level 1,
  param at level 1,
  body at level 200,
  format "'[' 'rec:'  annot  param  :=  '/  ' body ']'"
) : data_human_def_scope.
Notation "'rec:' param := body" := (
  Build_data_human_definition [] param%binder body%data_human_expr
)(at level 200,
  param at level 1,
  body at level 200,
  format "'[' 'rec:'  param  :=  '/  ' body ']'"
) : data_human_def_scope.
