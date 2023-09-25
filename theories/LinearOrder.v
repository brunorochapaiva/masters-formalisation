Record LinearStructure :=
  { point   : Set
  ; lt      : point -> point -> Prop
  }.

Notation "|| L ||l" := (L.(point)) (at level 200).

Notation "x <[[ L ]] y" := (L.(lt) x y) (at level 100).

Record LinearAxioms (L : LinearStructure) :=
  { transitive    : forall x y z , (x <[[ L ]] y) -> (y <[[ L ]] z) -> (x <[[ L ]] z)
  ; antisymmetric : forall x y , (x <[[ L ]] y) -> ~ (y <[[ L ]] y)
  ; trichotomous  : forall x y , (x <[[ L ]] y) \/ x = y \/ (y <[[ L ]] x)
  }.

Record LinearOrder :=
  { structure : LinearStructure
  ; axioms    : LinearAxioms structure
  }.

Definition Ul : LinearOrder -> Set :=
  fun L => L.(structure).(point).

Notation "| L |l" := (Ul L) (at level 200).

Notation "x <[ L ] y" := (L.(structure).(lt) x y) (at level 100).

Definition trans (L : LinearOrder) (x y z : | L |l) : (x <[ L ] y) -> (y <[ L ] z) -> (x <[ L ] z) :=
  L.(axioms).(transitive L.(structure)) x y z.

Definition asymm (L : LinearOrder) (x y : | L |l) : (x <[ L ] y) -> ~ (y <[ L ] y) :=
  L.(axioms).(antisymmetric L.(structure)) x y.

Definition trich (L : LinearOrder) (x y : | L |l) : (x <[ L ] y) \/ x = y \/ (y <[ L ] x) :=
  L.(axioms).(trichotomous L.(structure)) x y.
