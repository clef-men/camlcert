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

Class Similar X1 X2 :=
  similar : X1 → X2 → Prop.
Infix "≈" := similar
( at level 70,
  no associativity
) : stdpp_scope.
Notation "(≈)" := similar
( only parsing
) : stdpp_scope.
Notation "( x1 ≈.)" := (similar x1)
( only parsing
) : stdpp_scope.
Notation "(.≈ x2 )" := (λ x1, similar x1 x2)
( only parsing
) : stdpp_scope.

Class BiSimilar PROP X1 X2 :=
  bi_similar : X1 → X2 → PROP.
Infix "≈" := bi_similar
( at level 70,
  no associativity
) : bi_scope.
Notation "(≈)" := bi_similar
( only parsing
) : bi_scope.
Notation "( x1 ≈.)" := (bi_similar x1)
( only parsing
) : bi_scope.
Notation "(.≈ x2 )" := (λ x1, bi_similar x1 x2)
( only parsing
) : bi_scope.

Class BiSimilarAt PROP Y X1 X2 :=
  bi_similar_at : Y → X1 → X2 → PROP.
Notation "x1 ≈{ y }≈ x2" := (bi_similar_at y x1 x2)
( at level 70,
  no associativity,
  format "x1  ≈{ y }≈  x2"
) : bi_scope.
Notation "(≈{ y }≈)" := (bi_similar_at y)
( only parsing
) : bi_scope.
Notation "( x1 ≈{ y }≈.)" := (bi_similar_at y x1)
( only parsing
) : bi_scope.
Notation "(.≈{ y }≈ x2 )" := (λ x1, bi_similar_at y x1 x2)
( only parsing
) : bi_scope.

Class BiTie PROP X1 X2 :=
  bi_tie : X1 → X2 → PROP.
Infix "⋈" := bi_tie
( at level 70,
  no associativity
) : bi_scope.
Notation "(⋈)" := bi_tie
( only parsing
) : bi_scope.
Notation "( x1 ⋈.)" := (bi_tie x1)
( only parsing
) : bi_scope.
Notation "(.⋈ x2 )" := (λ x1, bi_tie x1 x2)
( only parsing
) : bi_scope.

Class BiTieAt PROP Y X1 X2 :=
  bi_tie_at : Y → X1 → X2 → PROP.
Notation "x1 ⋈{ y }⋈ x2" := (bi_tie_at y x1 x2)
( at level 70,
  no associativity,
  format "x1  ⋈{ y }⋈  x2"
) : bi_scope.
Notation "(⋈{ y }⋈)" := (bi_tie_at y)
( only parsing
) : bi_scope.
Notation "( x1 ⋈{ y }⋈.)" := (bi_tie_at y x1)
( only parsing
) : bi_scope.
Notation "(.⋈{ y }⋈ x2 )" := (λ x1, bi_tie_at y x1 x2)
( only parsing
) : bi_scope.
