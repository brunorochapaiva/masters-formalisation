Require Import Lists.List.
Require Import AlgebraRelations.
Require Import IntervalAlgebra.
Require Import LinearOrder.

Import ListNotations.

Inductive Interval_interval (L : LinearOrder) :=
  | Int (x y : | L |l) : (x <[ L ] y) -> Interval_interval L.

Definition Interval_interpretation (L : LinearOrder) :=
  fun r I J =>
    match r, I, J with
    | basic_b , Int _ x1 x2 _ , Int _ y1 y2 _ => x2 <[ L ] y1
    | basic_m , Int _ x1 x2 _ , Int _ y1 y2 _ => x2 = y1
    | basic_o , Int _ x1 x2 _ , Int _ y1 y2 _ => (x1 <[ L ] y1) /\ (y1 <[ L ] x2) /\ (x2 <[ L ] y2)
    | basic_s , Int _ x1 x2 _ , Int _ y1 y2 _ => x1 = y1 /\ (x2 <[ L ] y2)
    | basic_f , Int _ x1 x2 _ , Int _ y1 y2 _ => (y1 <[ L ] x1) /\ x2 = y2
    | basic_d , Int _ x1 x2 _ , Int _ y1 y2 _ => (y1 <[ L ] x1) /\ (x2 <[ L ] y2)
    end.

Definition Interval_structure (L : LinearOrder) :=
  {| interval       := Interval_interval L
   ; interpretation := Interval_interpretation L
   |}.

Require Import Ltac.

Ltac select_relation r qs :=
  match (eval compute in qs) with
  | nil         => idtac "could not find relation in given list"
  | cons ?q ?qs =>
    match (eval compute in (eq_rel_single r q)) with
      | true  => left
      | false => (right; select_relation r qs)
    end
  end;
  cbn.

Ltac trich_with_all_in L x ys :=
  match (eval compute in ys) with
  | nil         => idtac
  | cons ?y ?ys => (destruct (trich L x y) as [ | [ | ] ]; trich_with_all_in L x ys)
  end.

Ltac trich_all_helper L xs ys :=
  match (eval compute in xs) with
  | nil         => idtac
  | cons ?x ?xs => (trich_with_all_in L x ys; trich_all_helper L xs ys)
  end.

Ltac trich_all L xs := trich_all_helper L xs xs.

Ltac foo :=
  match goal with
  | |- _ -[[ ?rs | _ ]]-> _ =>
    let rec f := (fun qs => match (eval compute in qs) with
                         | nil         => idtac "done"
                         | cons ?r ?rs => idtac r; f rs
                         end)
    in f rs
  end.

Theorem Interval_exhaustive (L : LinearOrder) :
  forall x y , x -[[ rel_full | Interval_structure L ]]-> y.
Proof.
 intros I J.
 destruct I as [ x1 x2 x1_lt_x2 ].
 destruct J as [ y1 y2 y1_lt_y2 ].
 foo.

Qed.
