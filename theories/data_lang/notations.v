From camlcert Require Import
  prelude.
From camlcert.data_lang Require Export
  syntax.
From camlcert Require Import
  options.

Coercion DataIndex : data_index >-> data_val.
Coercion DataTag : data_tag >-> data_val.
Coercion DataInt : Z >-> data_val.
Coercion DataBool : bool >-> data_val.
Coercion DataLoc : loc >-> data_val.
Coercion DataFunc' : data_function >-> data_val.

Coercion DataVal : data_val >-> data_expr.
Coercion DataCall : data_expr >-> Funclass.

Notation "𝟘" :=
  DataZero.
Notation "𝟙" :=
  DataOne.
Notation "𝟚" :=
  DataTwo.

Declare Scope data_val_scope.
Delimit Scope data_val_scope with data_val.
Bind Scope data_val_scope with data_val.

Notation "()" :=
  DataUnit
: data_val_scope.

Declare Scope data_expr_scope.
Delimit Scope data_expr_scope with data_expr.
Bind Scope data_expr_scope with data_expr.

Notation "# v" := (
  DataVal v%Z%data_val%stdpp
)(at level 5,
  format "# v"
).

Notation "'Fail'" :=
  (#() #())%data_expr
: data_expr_scope.

Notation "$ x" := (
  DataVar x%nat
)(at level 5,
  format "$ x"
) : data_expr_scope.

Notation "'let:' e1 'in' e2" := (
  DataLet e1%data_expr e2%data_expr
)(at level 200,
  e1, e2 at level 200,
  format "'[v' 'let:'  '[' e1 ']'  'in' '/' e2 ']'"
) : data_expr_scope.
Notation "e1 ;; e2" :=
  (let: e1 in e2.[ren (+1)])%data_expr
( at level 100,
  e2 at level 200,
  format "'[v' '[hv' '[' e1 ']'  ;; ']' '/' e2 ']'"
) : data_expr_scope.

Notation "~ e" := (
  DataUnop DataNeg e%data_expr
) : data_expr_scope.
Notation "- e" := (
  DataUnop DataUminus e%data_expr
) : data_expr_scope.

Notation "e1 + e2" := (
  DataBinop DataPlus e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 - e2" := (
  DataBinop DataMinus e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 * e2" := (
  DataBinop DataMult e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 `quot` e2" := (
  DataBinop DataQuot e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 `rem` e2" := (
  DataBinop DataRem e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 ≤ e2" := (
  DataBinop DataLe e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 < e2" := (
  DataBinop DataLt e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 ≥ e2" := (
  DataBinop DataGe e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 > e2" := (
  DataBinop DataGt e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 = e2" := (
  DataBinop DataEq e1%data_expr e2%data_expr
) : data_expr_scope.
Notation "e1 ≠ e2" := (
  DataBinop DataNe e1%data_expr e2%data_expr
) : data_expr_scope.

Notation "'if:' e0 'then' e1 'else' e2" := (
  DataIf e0%data_expr e1%data_expr e2%data_expr
)(at level 200,
  e0, e1, e2 at level 200
) : data_expr_scope.
Notation "e1 && e2" :=
  (if: e1 then e2 else #false)%data_expr
( only parsing
) : data_expr_scope.
Notation "e1 || e2" :=
  (if: e1 then #true else e2)%data_expr
( only parsing
) : data_expr_scope.

Notation "& tag" := (
  DataBlock tag
)(at level 5,
  format "& tag"
) : data_expr_scope.
Notation "&& tag" := (
  DataBlockDet tag
)(at level 5,
  format "&& tag"
) : data_expr_scope.

Notation "![ e2 ] e1" := (
  DataLoad e1%data_expr e2%data_expr
)(at level 9,
  right associativity,
  format "![ e2 ]  e1"
) : data_expr_scope.
Notation "! e" := (
  DataLoad e%data_expr 𝟘
)(at level 9,
  right associativity,
  format "! e"
) : data_expr_scope.

Notation "e1 <-[ e2 ] e3" := (
  DataStore e1%data_expr e2%data_expr e3%data_expr
)(at level 20,
  format "e1  <-[ e2 ]  e3"
) : data_expr_scope.

Notation "( e1 , e2 , .. , en )" :=
  (&data_tag_pair .. (&data_tag_pair e1 e2) .. en)%data_expr
: data_expr_scope.

Notation NIL :=
  #()
( only parsing
).
Notation CONS :=
  (&0)%data_expr
( only parsing
).
Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' => e2 'end'" :=
  ( let: e0 in
    if: $0 = NIL then (
      e1.[ren (+1)]
    ) else (
      let: ![𝟚] $0 in
      let: ![𝟙] $1 in
      e2.[$0 .: $1 .: ren (+3)]
    )
  )%data_expr
( only parsing,
  e0, e1, e2 at level 200
) : data_expr_scope.

Declare Scope data_def_scope.
Delimit Scope data_def_scope with data_def.
Bind Scope data_def_scope with data_definition.

Notation "'rec:' annot := body" := (
  Build_data_definition annot body%data_expr
)(at level 200,
  annot at level 1,
  body at level 200,
  format "'[' 'rec:'  annot  :=  '/  ' body ']'"
) : data_def_scope.
Notation "'rec:=' body" := (
  Build_data_definition [] body%data_expr
)(at level 200,
  body at level 200,
  format "'[' 'rec:='  '/  ' body ']'"
) : data_def_scope.
