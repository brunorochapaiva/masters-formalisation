Require Import Lists.List.

Import ListNotations.

Inductive rel_basic : Set :=
| b : rel_basic
| m : rel_basic
| o : rel_basic
| s : rel_basic
| f : rel_basic
| d : rel_basic
| e : rel_basic
| B : rel_basic
| M : rel_basic
| O : rel_basic
| S : rel_basic
| F : rel_basic
| D : rel_basic.


Definition rel_allen : Set := list rel_basic.

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

Definition rel_basic_trans (r q : rel_basic) : rel_allen :=
  match r with
  | b => match q with
    | b => rel_b
    | m => rel_b
    | o => rel_b
    | s => rel_b
    | f => rel_bmosd
    | d => rel_bmosd
    | e => [ b ]
    | B => rel_full
    | M => rel_bmosd
    | O => rel_bmosd
    | S => rel_b
    | F => rel_b
    | D => rel_b
    end
  | m => match q with
    | b => rel_b
    | m => rel_b
    | o => rel_b
    | s => rel_m
    | f => rel_osd
    | d => rel_osd
    | e => [ m ]
    | B => rel_BMOSD
    | M => rel_feF
    | O => rel_osd
    | S => rel_m
    | F => rel_b
    | D => rel_b
    end
  | o => match q with
    | b => rel_b
    | m => rel_b
    | o => rel_bmo
    | s => rel_o
    | f => rel_osd
    | d => rel_osd
    | e => [ o ]
    | B => rel_BMOSD
    | M => rel_OSD
    | O => rel_concur
    | S => rel_oFD
    | F => rel_bmo
    | D => rel_bmoFD
    end
  | s => match q with
    | b => rel_b
    | m => rel_b
    | o => rel_bmo
    | s => rel_s
    | f => rel_d
    | d => rel_d
    | e => [ s ]
    | B => rel_B
    | M => rel_M
    | O => rel_fdO
    | S => rel_seS
    | F => rel_bmo
    | D => rel_bmoFD
    end
  | f => match q with
    | b => rel_b
    | m => rel_m
    | o => rel_osd
    | s => rel_d
    | f => rel_f
    | d => rel_d
    | e => [ f ]
    | B => rel_B
    | M => rel_B
    | O => rel_BMO
    | S => rel_BMO
    | F => rel_feF
    | D => rel_BMOSD
    end
  | d => match q with
    | b => rel_b
    | m => rel_b
    | o => rel_bmosd
    | s => rel_d
    | f => rel_d
    | d => rel_d
    | e => [ d ]
    | B => rel_B
    | M => rel_B
    | O => rel_fdBMO
    | S => rel_fdBMO
    | F => rel_bmosd
    | D => rel_full
    end
  | e => [ r ]
  | B => match q with
    | b => rel_full
    | m => rel_fdBMO
    | o => rel_fdBMO
    | s => rel_fdBMO
    | f => rel_B
    | d => rel_fdBMO
    | e => [ B ]
    | B => rel_B
    | M => rel_B
    | O => rel_B
    | S => rel_B
    | F => rel_B
    | D => rel_B
    end
  | M => match q with
    | b => rel_bmoFD
    | m => rel_seS
    | o => rel_fdO
    | s => rel_fdO
    | f => rel_M
    | d => rel_fdO
    | e => [ M ]
    | B => rel_B
    | M => rel_B
    | O => rel_B
    | S => rel_B
    | F => rel_M
    | D => rel_B
    end
  | O => match q with
    | b => rel_bmoFD
    | m => rel_oFD
    | o => rel_concur
    | s => rel_fdO
    | f => rel_O
    | d => rel_fdO
    | e => [ O ]
    | B => rel_B
    | M => rel_B
    | O => rel_BMO
    | S => rel_BMO
    | F => rel_OSD
    | D => rel_BMOSD
    end
  | S => match q with
    | b => rel_bmoFD
    | m => rel_oFD
    | o => rel_oFD
    | s => rel_seS
    | f => rel_O
    | d => rel_fdO
    | e => [ S ]
    | B => rel_B
    | M => rel_M
    | O => rel_O
    | S => rel_S
    | F => rel_D
    | D => rel_D
    end
  | F => match q with
    | b => rel_b
    | m => rel_m
    | o => rel_o
    | s => rel_o
    | f => rel_feF
    | d => rel_osd
    | e => [ F ]
    | B => rel_BMOSD
    | M => rel_OSD
    | O => rel_OSD
    | S => rel_D
    | F => rel_F
    | D => rel_D
    end
  | D => match q with
    | b => rel_bmoFD
    | m => rel_oFD
    | o => rel_oFD
    | s => rel_oFD
    | f => rel_OSD
    | d => rel_concur
    | e => [ D ]
    | B => rel_BMOSD
    | M => rel_OSD
    | O => rel_OSD
    | S => rel_D
    | F => rel_D
    | D => rel_D
    end
  end.

Record interval_algebra : Type @{Set+1} := mk_interval_algebra
  { carrier : Set
  ; interpretation : rel_basic -> carrier -> carrier -> Prop
  }.

Definition interpret_rel_allen (A : interval_algebra) :
    rel_allen -> A.(carrier) -> A.(carrier) -> Prop :=
  fun rs x y => fold_right or False (map (fun r => A.(interpretation) r x y) rs).
