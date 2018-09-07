From Hammer Require Import Hammer Reconstr.

Require Import List.

Lemma lem_lst :
  forall {A} (x : A) l1 l2 (P : A -> Prop),
    In x (l1 ++ l2) -> (forall y, In y l1 -> P y) -> (forall y, In y l2 -> P y) ->
    P x.
Proof.
  hammer_hook "list_lemmas" "list_lemmas.lem_lst".
  scrush.
Qed.

Lemma lem_lst2 : forall {A} (y1 y2 y3 : A) l l' z, In z l \/ In z l' ->
                                                   In z (y1 :: y2 :: l ++ y3 :: l').
Proof.
  hammer_hook "list_lemmas" "list_lemmas.lem_lst2".
  scrush.
Qed.

Lemma lem_lst3 : forall {A} (l : list A), length (tl l) <= length l.
Proof.
  hammer_hook "list_lemmas" "list_lemmas.lem_lst3".
  scrush.
Qed.

Lemma lem_lst4 : forall {A} (l : list A), l <> nil -> length (tl l) < length l.
Proof.
  hammer_hook "list_lemmas" "list_lemmas.lem_lst4".
  scrush.
Qed.

Lemma incl_app : forall (A : Type) (n l m : list A),
                   List.incl l n /\ List.incl m n -> List.incl (l ++ m) n.
Proof.
  hammer_hook "list_lemmas" "list_lemmas.incl_app".
  Reconstr.reasy (@Coq.Lists.List.incl_app) Reconstr.Empty.
Qed.

Lemma lem_lst_1 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  induction l'.
  - hammer_hook "list_lemmas" "list_lemmas.lem_lst_1.subgoal_1".
    scrush.
  - hammer_hook "list_lemmas" "list_lemmas.lem_lst_1.subgoal_2".
    Reconstr.reasy (@Coq.Lists.List.NoDup_remove) Reconstr.Empty.
Qed.

Lemma NoDup_remove_1
     : forall (A : Type) (a : A) (l' l : list A),
       List.NoDup (l ++ a :: l') ->
       ~ List.In a (l ++ l') /\ List.NoDup (l ++ l') /\ List.NoDup l.
Proof.
  hammer_hook "list_lemmas" "list_lemmas.NoDup_remove_1".
  Reconstr.reasy (@Coq.Lists.List.NoDup_remove_2, @Coq.Lists.List.NoDup_remove_1, @lem_lst_1) Reconstr.Empty.
Qed.

Lemma incl_appl
     : forall (A : Type) (l m n : list A),
       List.incl l n -> List.incl l (n ++ m) /\ List.incl l (m ++ n) /\ List.incl l (l ++ l).
Proof.
  hammer_hook "list_lemmas" "list_lemmas.incl_appl".
  Reconstr.reasy (@Coq.Lists.List.incl_appl, @Coq.Lists.List.incl_appr, @Coq.Lists.List.incl_refl) Reconstr.Empty.
Qed.

Lemma Forall_1
     : forall (A : Type) (P : A -> Prop) (a : A),
       forall (l l' : list A), List.Forall P l /\ List.Forall P l' /\ P a -> List.Forall P (l ++ a :: l').
Proof.
  induction l.
  - hammer_hook "list_lemmas" "list_lemmas.Forall_1.subgoal_1".
    sauto.
  - hammer_hook "list_lemmas" "list_lemmas.Forall_1.subgoal_2".
    sauto.
Qed.

Lemma Forall_impl
     : forall (A : Type) (P : A -> Prop),
       forall l : list A, List.Forall P l -> List.Forall P (l ++ l).
Proof.
  induction l.
  - hammer_hook "list_lemmas" "list_lemmas.Forall_impl.subgoal_1".
    sintuition.
  - hammer_hook "list_lemmas" "list_lemmas.Forall_impl.subgoal_2".
    intro H; inversion_clear H.
    Reconstr.reasy (@Coq.Lists.List.Forall_cons, @Forall_1) Reconstr.Empty.
Qed.
