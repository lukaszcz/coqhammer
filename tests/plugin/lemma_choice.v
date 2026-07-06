(* Tests for the hammer lemma choice mode: hammer [lemma1 lemma2 ...] *)

From Hammer Require Import Hammer.
From Stdlib Require Import Lists.List.
Import ListNotations.

(* Disable the sauto pre-phase so that the lemma choice path is
   actually exercised. *)
Set Hammer SAutoLimit 0.

Lemma lem_given : forall (A : Type) (l1 l2 : list A),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros.
  induction l1.
  - hammer [app_nil_r app_assoc].
  - hammer [app_nil_r app_assoc].
Qed.

(* Duplicated lemmas are accepted. *)
Lemma lem_duplicates : forall (A : Type) (l : list A), l ++ [] = l.
Proof.
  intros.
  hammer [app_nil_r app_nil_r].
Qed.

(* A local hypothesis may be given as a lemma. *)
Lemma lem_hyp : forall n : nat, n = 0 -> n + n = 0.
Proof.
  intros n H.
  hammer [H].
Qed.

(* A lemma excluded from the search results (here by the search
   blacklist) is still usable when given explicitly. *)
Add Search Blacklist "app_nil_r".
Lemma lem_blacklisted : forall (A : Type) (l : list A), rev (l ++ []) = rev l.
Proof.
  intros.
  hammer [app_nil_r].
Qed.
Remove Search Blacklist "app_nil_r".

(* An empty lemma list selects the definitions referenced by the goal
   or the hypotheses: here the ATPs need the definition of `mydouble`,
   which occurs only in the hypothesis. *)
Definition mydouble (n : nat) := n + n.

Lemma lem_empty : forall n m : nat, mydouble n = m -> n + n = m.
Proof.
  intros n m H.
  hammer [].
Qed.

(* A term which is not a global reference is reported cleanly. *)
Lemma lem_not_global : 1 + 1 = 2.
Proof.
  Fail hammer [(1 + 1)].
  reflexivity.
Qed.

(* The lemma choice also works with GSMode 0. *)
Set Hammer GSMode 0.

Lemma lem_gsmode0 : forall (A B : Type) (f : A -> B) (l : list A),
  length (map f l) = length l.
Proof.
  intros.
  hammer [length_map].
Qed.
