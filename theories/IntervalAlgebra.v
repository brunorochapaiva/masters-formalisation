Require Import Lists.List.
Require Import AlgebraRelations.

Import ListNotations.

Record IntervalStructure :=
  { interval       : Set
  ; interpretation : rel_basic -> interval -> interval -> Prop
  }.

Definition extended_interpretation (A : IntervalStructure)
  : rel_allen -> A.(interval) -> A.(interval) -> Prop :=
  fun rs x y => let extended_int : rel_single -> Prop := fun r =>
    match r with
    | basic r => A.(interpretation) r x y
    | e       => eq x y
    | dual r  => A.(interpretation) r y x
    end
    in fold_right or False (map extended_int rs).

Notation "|| A ||a" := (A.(interval)) (at level 200).

Notation "x -[[ rs | A ]]-> y" := (extended_interpretation A rs x y) (at level 100).

Record IntervalAxioms (A : IntervalStructure) :=
  { exhaustive : forall x y , x -[[ rel_full | A ]]-> y
  ; mutually_exclusive : forall r s , forall x y , ~ r = s -> (x -[[ [ r ] | A ]]-> y) -> ~ (x -[[ [ s ] | A ]]-> y)
  ; transitive_like : forall r s , forall x y z , (x -[[ [ r ] | A ]]-> y) -> (y -[[ [ s ] | A ]]-> z) -> (x -[[ rel_single_trans r s | A ]]-> y)
  }.

Record IntervalAlgebra :=
  { structure : IntervalStructure
  ; axioms    : IntervalAxioms structure
  }.

Definition Ua : IntervalAlgebra -> Set :=
  fun A => A.(structure).(interval).

Notation "| A |a" := (Ua A) (at level 200).

Notation "x -[ rs | A ]-> y" := (extended_interpretation A.(structure) rs x y) (at level 100).

Definition exh (A : IntervalAlgebra) (x y : | A |a) : x -[ rel_full | A ]-> y :=
  A.(axioms).(exhaustive A.(structure)) x y.

Definition mutex (A : IntervalAlgebra) (r s : rel_single) (x y : | A |a)
  : ~ r = s -> (x -[ [ r ] | A ]-> y) -> ~ (x -[ [ s ] | A ]-> y) :=
  A.(axioms).(mutually_exclusive A.(structure)) r s x y.

Definition transl (A : IntervalAlgebra) (r s : rel_single) (x y z : | A |a)
  : (x -[ [ r ] | A ]-> y) -> (y -[ [ s ] | A ]-> z) -> (x -[ rel_single_trans r s | A ]-> y) :=
  A.(axioms).(transitive_like A.(structure)) r s x y z.
