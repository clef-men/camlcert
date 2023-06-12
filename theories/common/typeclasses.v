From iris.bi Require Import
  notation.

From simuliris Require Import
  prelude.

Class SqSubset X :=
  sqsubset : relation X.
Infix "⊏" := sqsubset
( at level 70
) : stdpp_scope.
Infix "⊏@{ X }" := (@sqsubset X _)
( at level 70,
  only parsing
) : stdpp_scope.
Notation "(⊏)" := sqsubset
( only parsing
) : stdpp_scope.
Notation "(⊏@{ X } )" := (@sqsubset X _)
( only parsing
) : stdpp_scope.
Notation "( x ⊏.)" := (sqsubset x)
( only parsing
) : stdpp_scope.
Notation "(.⊏ y )" := (λ x, sqsubset x y)
( only parsing
) : stdpp_scope.

Class Fill ctx expr := {
  fill : ctx → expr → expr ;
}.
#[global] Arguments Build_Fill {_ _} _ : assert.
#[global] Arguments fill {_ _ _} !_ !_ / : simpl nomatch, assert.
Notation "C @@ e" := (fill C e)
( at level 30,
  right associativity
) : stdpp_scope.
Notation "(@@)" := fill
( only parsing
) : stdpp_scope.
Notation "( C @@.)" := (fill C)
( only parsing
) : stdpp_scope.
Notation "(.@@ e )" := (λ C, fill C e)
( only parsing
) : stdpp_scope.

Class Similar X Y :=
  similar : X → Y → Prop.
Infix "≈" := similar
( at level 70,
  no associativity
) : stdpp_scope.
Infix "{ X }@≈@{ Y }" := (@similar X Y _)
( at level 70,
  no associativity,
  only parsing
) : stdpp_scope.
Notation "(≈)" := similar
( only parsing
) : stdpp_scope.
Notation "({ X }@≈@{ Y } )" := (@similar X Y _)
( only parsing
) : stdpp_scope.
Notation "( x ≈.)" := (similar x)
( only parsing
) : stdpp_scope.
Notation "(.≈ y )" := (λ x, similar x y)
( only parsing
) : stdpp_scope.

Class BiSimilar PROP X Y :=
  bi_similar : X → Y → PROP.
Infix "≈" := bi_similar
( at level 70,
  no associativity
) : bi_scope.
Infix "{ X }@≈@{ Y }" := (@bi_similar _ X Y _)
( at level 70,
  no associativity,
  only parsing
) : bi_scope.
Notation "(≈)" := bi_similar
( only parsing
) : bi_scope.
Notation "({ X }@≈@{ Y } )" := (@bi_similar _ X Y _)
( only parsing
) : bi_scope.
Notation "( x ≈.)" := (bi_similar x)
( only parsing
) : bi_scope.
Notation "(.≈ y )" := (λ x, bi_similar x y)
( only parsing
) : bi_scope.

Class BiTie PROP X Y :=
  bi_tie : X → Y → PROP.
Infix "⟷" := bi_tie
( at level 70,
  no associativity
) : bi_scope.
Infix "{ X }@⟷@{ Y }" := (@bi_tie _ X Y _)
( at level 70,
  no associativity,
  only parsing
) : bi_scope.
Notation "(⟷)" := bi_tie
( only parsing
) : bi_scope.
Notation "({ X }@⟷@{ Y } )" := (@bi_tie _ X Y _)
( only parsing
) : bi_scope.
Notation "( x ⟷.)" := (bi_tie x)
( only parsing
) : bi_scope.
Notation "(.⟷ y )" := (λ x, bi_tie x y)
( only parsing
) : bi_scope.
