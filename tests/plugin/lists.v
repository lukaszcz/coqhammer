From Hammer Require Import Hammer.

From Stdlib Require Import List.

Hammer_version.
Hammer_objects.

Set Hammer SAutoLimit 0.

Lemma lem_lst :
  forall {A} (x : A) l1 l2 (P : A -> Prop),
    In x (l1 ++ l2) -> (forall y, In y l1 -> P y) -> (forall y, In y l2 -> P y) ->
    P x.
Proof.
  hammer.
Qed.

(*
Lemma lem_lst2 : forall {A} (y1 y2 y3 : A) l l' z, In z l \/ In z l' ->
                                                   In z (y1 :: y2 :: l ++ y3 :: l').
Proof.
  hammer.
Qed.
*)

Lemma lem_lst3 : forall {A} (l : list A), length (tl l) <= length l.
Proof.
  hammer.
Qed.

Lemma lem_lst4 : forall {A} (l : list A), l <> nil -> length (tl l) < length l.
Proof.
  destruct l; intro H; [contradiction| simpl; apply le_n].
Qed.

Lemma incl_app : forall (A : Type) (n l m : list A),
                   List.incl l n /\ List.incl m n -> List.incl (l ++ m) n.
Proof.
  strivial use: List.incl_app.
Qed.

Lemma incl_appl
     : forall (A : Type) (l m n : list A),
       List.incl l n -> List.incl l (n ++ m) /\ List.incl l (m ++ n) /\ List.incl l (l ++ l).
Proof.
  strivial use: List.incl_appr, List.incl_appl, List.incl_refl.
Qed.

Lemma Forall_1
     : forall (A : Type) (P : A -> Prop) (a : A),
       forall (l l' : list A), List.Forall P l /\ List.Forall P l' /\ P a -> List.Forall P (l ++ a :: l').
Proof.
  intros A P a l; induction l as [|x l IH]; intros l' [Hl [Hl' Ha]]; simpl in *.
  - constructor; assumption.
  - inversion Hl; subst. constructor; [assumption|]. apply IH. repeat split; assumption.
Qed.

Lemma Forall_impl
     : forall (A : Type) (P : A -> Prop),
       forall l : list A, List.Forall P l -> List.Forall P (l ++ l).
Proof.
  intros A P l Hl. apply Forall_app; split; assumption.
Qed.

Lemma lem_lst_1 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  intros A l; induction l as [|x l IH]; intros l' H; constructor.
  - intro Hin. inversion H; subst. apply H2. apply in_or_app; left; exact Hin.
  - inversion H; subst. apply IH with (l' := l'); assumption.
Qed.

Lemma NoDup_remove_1
     : forall (A : Type) (a : A) (l' l : list A),
       List.NoDup (l ++ a :: l') ->
       ~ List.In a (l ++ l') /\ List.NoDup (l ++ l') /\ List.NoDup l.
Proof.
  strivial use: NoDup_app_remove_r, NoDup_remove.
Qed.
