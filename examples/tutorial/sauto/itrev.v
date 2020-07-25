(* Tail-recursive reverse *)

From Hammer Require Import Tactics.
From Hammer Require Import Hints.
(* The Hints module provides the following rewrite hint databases:
   shints, slist, sbool, sarith, szarith. *)

Require List.
Import List.ListNotations.
Open Scope list_scope.

Fixpoint itrev {A} (l acc : list A) :=
  match l with
  | [] => acc
  | h :: t => itrev t (h :: acc)
  end.

Definition rev {A} (l : list A) := itrev l [].

Lemma lem_itrev {A} :
  forall l acc : list A, itrev l acc = itrev l [] ++ acc.
Proof.
  induction l as [| h t IH].
  - auto.
  - intro acc.
    simpl.
    rewrite IH.
    pattern (itrev t [h]).
    rewrite IH.
    rewrite <- List.app_assoc.
    reflexivity.
Qed.

Lemma lem_itrev' {A} :
  forall l acc : list A, itrev l acc = itrev l [] ++ acc.
Proof.
  (* induction l; sauto db: slist. *)
  induction l; ssimpl.
  (* Simplification tactics in the order of increasing strength and
     decreasing speed: "simp_hyps", "sintuition", "qsimpl",
     "ssimpl". *)
  (* The simplification tactics may change the context in an
     unpredictable manner and introduce automatically generated
     hypothesis names. *)
  rewrite IHl.
  (* rewrite IHl. *)
  pattern (itrev l [a]).
  rewrite IHl.
  sauto db: slist. (* The "slist" database contains "List.app_assoc" *)
  (* "sauto" is currently not very good at rewriting - it just tries
     to apply the "rewrite" tactic *)

  Restart.

  induction l as [|x l ?]; simpl.
  - sauto.
  - assert (itrev l [x] = itrev l [] ++ [x]) by sauto.
    sauto db: slist.
Qed.

Lemma lem_rev_app {A} :
  forall l1 l2 : list A, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  unfold rev.
  induction l1 as [| x l1 IH]; intro l2.
  - simpl.
    rewrite List.app_nil_r.
    reflexivity.
  - simpl.
    rewrite lem_itrev.
    rewrite IH.
    rewrite <- List.app_assoc.
    rewrite (lem_itrev l1 [x]).
    reflexivity.
Qed.

Lemma lem_rev_app' {A} :
  forall l1 l2 : list A, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1; sauto use: @lem_itrev db: slist unfold: rev.
Qed.

Lemma lem_rev_rev {A} : forall l : list A, rev (rev l) = l.
Proof.
  unfold rev.
  induction l as [| x l IH].
  - reflexivity.
  - simpl.
    rewrite (lem_itrev l [x]).
    generalize (lem_rev_app (itrev l []) [x]).
    unfold rev.
    intro H.
    rewrite H.
    rewrite IH.
    reflexivity.
Qed.

Lemma lem_rev_rev' {A} : forall l : list A, rev (rev l) = l.
Proof.
  (* induction l; sauto use: @lem_itrev, @lem_rev_app unfold: rev. *)
  (* induction l; sauto limit: 2000 use: @lem_itrev, @lem_rev_app unfold: rev. *)
  induction l as [|x l ?].
  - reflexivity.
  - sauto use: (lem_itrev l [x]), (lem_rev_app (itrev l []) [x]) unfold: rev.
Qed.

Lemma lem_rev_lst {A} : forall l : list A, rev l = List.rev l.
Proof.
  unfold rev.
  induction l as [|x l IH].
  - reflexivity.
  - simpl.
    rewrite lem_itrev.
    rewrite IH.
    reflexivity.
Qed.

Lemma lem_rev_lst' {A} : forall l : list A, rev l = List.rev l.
Proof.
  induction l; sauto use: @lem_itrev unfold: rev.
Qed.

Require Import Sorting.Permutation.

Lemma lem_itrev_perm {A} :
  forall l l' : list A, Permutation (itrev l l') (l ++ l').
Proof.
  induction l as [| x l IH]; simpl.
  - eauto using Permutation.
  - intro l'.
    enough (Permutation (l ++ (x :: l')) (x :: l ++ l')).
    { eauto using Permutation. }
    eauto using Permutation_middle, Permutation_sym.
Qed.

Lemma lem_itrev_perm' {A} :
  forall l l' : list A, Permutation (itrev l l') (l ++ l').
Proof.
  induction l; sauto use: Permutation_middle, Permutation_sym.
Qed.

Lemma lem_rev_perm {A} : forall l : list A, Permutation (rev l) l.
Proof.
  unfold rev.
  intro l.
  rewrite List.app_nil_end.
  apply lem_itrev_perm.
Qed.

Lemma lem_rev_perm' {A} : forall l : list A, Permutation (rev l) l.
Proof.
  sauto use: @lem_itrev_perm db: slist unfold: rev.
Qed.
