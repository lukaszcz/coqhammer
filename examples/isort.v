(************************************************************************************)
(* Insertion sort *)

From Hammer Require Import Tactics.

Require List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Arith.
Require Import Lia.

Require Import Sorting.Permutation.
Require Import Sorting.Sorted.

Inductive Sorted : list nat -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y l, Sorted (y :: l) -> x <= y ->
                           Sorted (x :: y :: l).

(* insert a number into a sorted list preserving the sortedness *)
Fixpoint insert (l : list nat) (x : nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: l else h :: insert t x
  end.

Fixpoint isort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert (isort t) h
  end.

Lemma lem_insert_sorted_hlp :
  forall l y z, y <= z -> Sorted (y :: l) -> Sorted (y :: insert l z).
Proof.
  intro l.
  induction l as [|a l IH].
  - intros x y H1 H2.
    simpl.
    auto using Sorted.
  - intros x y H1 H2.
    simpl.
    destruct (Nat.leb_spec y a) as [H|H].
    + repeat constructor; auto.
      inversion H2; auto.
    + inversion_clear H2.
      auto using Sorted with arith.
Qed.

Lemma lem_insert_sorted_hlp' :
  forall l y z, y <= z -> Sorted (y :: l) -> Sorted (y :: insert l z).
Proof.
  time (induction l; sauto db: arith).
  (* "db: db1, .., dbn" instructs "sauto" to use the given hint or
     rewriting databases *)
  Undo.
  time (induction l; sauto db: arith inv: Sorted ctrs: Sorted).
  (* "inv: ind1, .., indn" instructs "sauto" to try inversion (case
     reasoning) only on elements of the given inductive types *)
  (* "ctrs: ind1, .., indn" instructs "sauto" to try using
     constructors of only the given inductive types *)
  (* "-" stands for an empty list *)
  (* By default "sauto" does inversion on elements of and uses
     constructors of all possible inductive types *)
Qed.

Lemma lem_insert_sorted (l : list nat) (x : nat) :
  Sorted l -> Sorted (insert l x).
Proof.
  destruct l as [|y l].
  - simpl; auto using Sorted.
  - intro H.
    simpl.
    destruct (Nat.leb_spec x y);
      auto using Sorted, lem_insert_sorted_hlp with arith.
Qed.

Lemma lem_insert_sorted' (l : list nat) (x : nat) :
  Sorted l -> Sorted (insert l x).
Proof.
  (* sauto use: lem_insert_sorted_hlp db: arith. *)
  (* "use: lem1, .., lemn" adds the given lemmas to the context *)
  time (destruct l; sauto use: lem_insert_sorted_hlp db: arith).
  Undo.
  time (destruct l; sauto use: lem_insert_sorted_hlp inv: - ctrs: Sorted db: arith).
Qed.

Lemma lem_isort_sorted : forall l, Sorted (isort l).
Proof.
  induction l as [|x l IH].
  - auto using Sorted.
  - simpl.
    auto using lem_insert_sorted.
Qed.

Lemma lem_isort_sorted' : forall l, Sorted (isort l).
Proof.
  induction l; sauto use: lem_insert_sorted.
Qed.

Lemma lem_insert_perm : forall l x, Permutation (insert l x) (x :: l).
Proof.
  induction l as [|y l IH].
  - eauto using Permutation.
  - intro x.
    simpl.
    destruct (Nat.leb_spec x y) as [H|H];
      eauto using Permutation.
Qed.

Lemma lem_insert_perm' : forall l x, Permutation (insert l x) (x :: l).
Proof.
  induction l; sauto.
Qed.

Lemma lem_isort_perm : forall l, Permutation (isort l) l.
Proof.
  induction l as [|y l IH].
  - eauto using Permutation.
  - simpl.
    eauto using Permutation, lem_insert_perm.
Qed.

Lemma lem_isort_perm' : forall l, Permutation (isort l) l.
Proof.
  induction l; sauto use: lem_insert_perm.
Qed.
