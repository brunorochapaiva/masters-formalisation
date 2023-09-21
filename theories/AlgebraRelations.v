Require Import Lists.List.
Require Import Structures.Orders.
Require Import Classes.RelationPairs.

Import ListNotations.

Inductive rel_basic : Set :=
| basic_b : rel_basic
| basic_m : rel_basic
| basic_o : rel_basic
| basic_s : rel_basic
| basic_f : rel_basic
| basic_d : rel_basic.

Inductive rel_single : Set :=
| basic : rel_basic -> rel_single
| dual  : rel_basic -> rel_single
| e     : rel_single.

Definition b : rel_single := basic basic_b.
Definition m : rel_single := basic basic_m.
Definition o : rel_single := basic basic_o.
Definition s : rel_single := basic basic_s.
Definition f : rel_single := basic basic_f.
Definition d : rel_single := basic basic_d.
Definition B : rel_single := dual basic_b.
Definition M : rel_single := dual basic_m.
Definition O : rel_single := dual basic_o.
Definition S : rel_single := dual basic_s.
Definition F : rel_single := dual basic_f.
Definition D : rel_single := dual basic_d.

Definition rel_allen : Set := list rel_single.

(* Only certain combinations appear, so to avoid errors we create a definition
   for each one
 *)

Definition rel_b      : rel_allen := [ b ].
Definition rel_B      : rel_allen := [ B ].
Definition rel_d      : rel_allen := [ d ].
Definition rel_D      : rel_allen := [ D ].
Definition rel_oFD    : rel_allen := [ o ; F ; D ].
Definition rel_osd    : rel_allen := [ o ; s ; d ].
Definition rel_OSD    : rel_allen := [ O ; S ; D ].
Definition rel_fdO    : rel_allen := [ f ; d ; O ].
Definition rel_bmoFD  : rel_allen := [ b ; m ; o ; F ; D ].
Definition rel_bmosd  : rel_allen := [ b ; m ; o ; s ; d ].
Definition rel_m      : rel_allen := [ m ].
Definition rel_BMOSD  : rel_allen := [ B ; M ; O ; S ; D ].
Definition rel_fdBMO  : rel_allen := [ f ; d ; B ; M ; O ].
Definition rel_M      : rel_allen := [ M ].
Definition rel_o      : rel_allen := [ o ].
Definition rel_O      : rel_allen := [ O ].
Definition rel_bmo    : rel_allen := [ b ; m ; o ].
Definition rel_BMO    : rel_allen := [ B ; M ; O ].
Definition rel_full   : rel_allen := [ b ; m ; o ; s ; f ; d ; e ; B ; M ; O ; S ; F ; D].
Definition rel_concur : rel_allen := [ o ; s ; f ; d ; e ; O ; S ; F ; D].
Definition rel_F      : rel_allen := [ F ].
Definition rel_feF    : rel_allen := [ f ; e ; F ].
Definition rel_seS    : rel_allen := [ s ; e ; S ].
Definition rel_s      : rel_allen := [ s ].
Definition rel_S      : rel_allen := [ S ].
Definition rel_f      : rel_allen := [ f ].
Definition rel_e      : rel_allen := [ e ].

Definition rel_single_trans (r q : rel_single) : rel_allen :=
  match r with
  | basic basic_b => match q with
    | basic basic_b => rel_b
    | basic basic_m => rel_b
    | basic basic_o => rel_b
    | basic basic_s => rel_b
    | basic basic_f => rel_bmosd
    | basic basic_d => rel_bmosd
    | e => [ b ]
    | dual basic_b => rel_full
    | dual basic_m => rel_bmosd
    | dual basic_o => rel_bmosd
    | dual basic_s => rel_b
    | dual basic_f => rel_b
    | dual basic_d => rel_b
    end
  | basic basic_m => match q with
    | basic basic_b => rel_b
    | basic basic_m => rel_b
    | basic basic_o => rel_b
    | basic basic_s => rel_m
    | basic basic_f => rel_osd
    | basic basic_d => rel_osd
    | e => [ m ]
    | dual basic_b => rel_BMOSD
    | dual basic_m => rel_feF
    | dual basic_o => rel_osd
    | dual basic_s => rel_m
    | dual basic_f => rel_b
    | dual basic_d => rel_b
    end
  | basic basic_o => match q with
    | basic basic_b => rel_b
    | basic basic_m => rel_b
    | basic basic_o => rel_bmo
    | basic basic_s => rel_o
    | basic basic_f => rel_osd
    | basic basic_d => rel_osd
    | e => [ o ]
    | dual basic_b => rel_BMOSD
    | dual basic_m => rel_OSD
    | dual basic_o => rel_concur
    | dual basic_s => rel_oFD
    | dual basic_f => rel_bmo
    | dual basic_d => rel_bmoFD
    end
  | basic basic_s => match q with
    | basic basic_b => rel_b
    | basic basic_m => rel_b
    | basic basic_o => rel_bmo
    | basic basic_s => rel_s
    | basic basic_f => rel_d
    | basic basic_d => rel_d
    | e => [ s ]
    | dual basic_b => rel_B
    | dual basic_m => rel_M
    | dual basic_o => rel_fdO
    | dual basic_s => rel_seS
    | dual basic_f => rel_bmo
    | dual basic_d => rel_bmoFD
    end
  | basic basic_f => match q with
    | basic basic_b => rel_b
    | basic basic_m => rel_m
    | basic basic_o => rel_osd
    | basic basic_s => rel_d
    | basic basic_f => rel_f
    | basic basic_d => rel_d
    | e => [ f ]
    | dual basic_b => rel_B
    | dual basic_m => rel_B
    | dual basic_o => rel_BMO
    | dual basic_s => rel_BMO
    | dual basic_f => rel_feF
    | dual basic_d => rel_BMOSD
    end
  | basic basic_d => match q with
    | basic basic_b => rel_b
    | basic basic_m => rel_b
    | basic basic_o => rel_bmosd
    | basic basic_s => rel_d
    | basic basic_f => rel_d
    | basic basic_d => rel_d
    | e => [ d ]
    | dual basic_b => rel_B
    | dual basic_m => rel_B
    | dual basic_o => rel_fdBMO
    | dual basic_s => rel_fdBMO
    | dual basic_f => rel_bmosd
    | dual basic_d => rel_full
    end
  | e => [ r ]
  | dual basic_b => match q with
    | basic basic_b => rel_full
    | basic basic_m => rel_fdBMO
    | basic basic_o => rel_fdBMO
    | basic basic_s => rel_fdBMO
    | basic basic_f => rel_B
    | basic basic_d => rel_fdBMO
    | e => [ B ]
    | dual basic_b => rel_B
    | dual basic_m => rel_B
    | dual basic_o => rel_B
    | dual basic_s => rel_B
    | dual basic_f => rel_B
    | dual basic_d => rel_B
    end
  | dual basic_m => match q with
    | basic basic_b => rel_bmoFD
    | basic basic_m => rel_seS
    | basic basic_o => rel_fdO
    | basic basic_s => rel_fdO
    | basic basic_f => rel_M
    | basic basic_d => rel_fdO
    | e => [ M ]
    | dual basic_b => rel_B
    | dual basic_m => rel_B
    | dual basic_o => rel_B
    | dual basic_s => rel_B
    | dual basic_f => rel_M
    | dual basic_d => rel_B
    end
  | dual basic_o => match q with
    | basic basic_b => rel_bmoFD
    | basic basic_m => rel_oFD
    | basic basic_o => rel_concur
    | basic basic_s => rel_fdO
    | basic basic_f => rel_O
    | basic basic_d => rel_fdO
    | e => [ O ]
    | dual basic_b => rel_B
    | dual basic_m => rel_B
    | dual basic_o => rel_BMO
    | dual basic_s => rel_BMO
    | dual basic_f => rel_OSD
    | dual basic_d => rel_BMOSD
    end
  | dual basic_s => match q with
    | basic basic_b => rel_bmoFD
    | basic basic_m => rel_oFD
    | basic basic_o => rel_oFD
    | basic basic_s => rel_seS
    | basic basic_f => rel_O
    | basic basic_d => rel_fdO
    | e => [ S ]
    | dual basic_b => rel_B
    | dual basic_m => rel_M
    | dual basic_o => rel_O
    | dual basic_s => rel_S
    | dual basic_f => rel_D
    | dual basic_d => rel_D
    end
  | dual basic_f => match q with
    | basic basic_b => rel_b
    | basic basic_m => rel_m
    | basic basic_o => rel_o
    | basic basic_s => rel_o
    | basic basic_f => rel_feF
    | basic basic_d => rel_osd
    | e => [ F ]
    | dual basic_b => rel_BMOSD
    | dual basic_m => rel_OSD
    | dual basic_o => rel_OSD
    | dual basic_s => rel_D
    | dual basic_f => rel_F
    | dual basic_d => rel_D
    end
  | dual basic_d => match q with
    | basic basic_b => rel_bmoFD
    | basic basic_m => rel_oFD
    | basic basic_o => rel_oFD
    | basic basic_s => rel_oFD
    | basic basic_f => rel_OSD
    | basic basic_d => rel_concur
    | e => [ D ]
    | dual basic_b => rel_BMOSD
    | dual basic_m => rel_OSD
    | dual basic_o => rel_OSD
    | dual basic_s => rel_D
    | dual basic_f => rel_D
    | dual basic_d => rel_D
    end
  end.
