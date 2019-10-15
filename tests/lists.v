From Hammer Require Import Hammer.

Require Import List.

Hammer_version.
Hammer_objects.

Set Hammer CrushLimit 0.

Lemma lem_lst :
  forall {A} (x : A) l1 l2 (P : A -> Prop),
    In x (l1 ++ l2) -> (forall y, In y l1 -> P y) -> (forall y, In y l2 -> P y) ->
    P x.
Proof.
  hammer.
Qed.

Lemma lem_lst2 : forall {A} (y1 y2 y3 : A) l l' z, In z l \/ In z l' ->
                                                   In z (y1 :: y2 :: l ++ y3 :: l').
Proof.
  hammer.
Qed.

Lemma lem_lst3 : forall {A} (l : list A), length (tl l) <= length l.
Proof.
  hammer.
Qed.

Lemma lem_lst4 : forall {A} (l : list A), l <> nil -> length (tl l) < length l.
Proof.
  hammer.
Qed.

Lemma incl_app : forall (A : Type) (n l m : list A),
                   List.incl l n /\ List.incl m n -> List.incl (l ++ m) n.
Proof.
  hammer.
Qed.

Lemma incl_appl
     : forall (A : Type) (l m n : list A),
       List.incl l n -> List.incl l (n ++ m) /\ List.incl l (m ++ n) /\ List.incl l (l ++ l).
Proof.
  hammer.
Qed.
