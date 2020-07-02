From Hammer Require Import Tactics.
From Hammer Require Import Reflect. (* declares "is_true" as a coercion *)

Require List.
Open Scope list_scope.
Import List.ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Sorting.Permutation.
Require Import Program.

Class DecTotalOrder (A : Type) := {
  leb : A -> A -> bool;
  leb_total_dec : forall x y, {leb x y}+{leb y x};
  leb_antisym : forall x y, leb x y -> leb y x -> x = y;
  leb_trans : forall x y z, leb x y -> leb y z -> leb x z }.

Arguments leb {A _}.
Arguments leb_total_dec {A _}.
Arguments leb_antisym {A _}.
Arguments leb_trans {A _}.

Instance dto_nat : DecTotalOrder nat.
Proof.
  apply Build_DecTotalOrder with (leb := Nat.leb);
    induction x; sauto.
Defined.

Inductive Sorted {A} {dto : DecTotalOrder A} : list A -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y l, Sorted (y :: l) -> leb x y ->
                           Sorted (x :: y :: l).

Lemma lem_sorted_tail {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) -> Sorted l.
Proof.
  inversion 1; sauto.
Qed.

(* Defining "LeLst x" as "List.forall (leb x)" would harm the
   performance of "sauto". It is better to define "LeLst"
   separately. *)
Inductive LeLst {A} {dto : DecTotalOrder A} : A -> list A -> Prop :=
| LeLst_0 : forall x, LeLst x []
| LeLst_1 : forall x y l, leb x y -> LeLst x l -> LeLst x (y :: l).

Lemma lem_lelst_trans {A} {dto : DecTotalOrder A} :
  forall l y, LeLst y l -> forall x, leb x y -> LeLst x l.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_lelst_sorted {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  induction l; sauto use: lem_lelst_trans inv: Sorted, LeLst ctrs: Sorted. (* 0.4s *)
Qed.

Lemma lem_lelst_perm {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation l1 l2 -> forall x, LeLst x l1 -> LeLst x l2.
Proof.
  induction 1; sauto inv: LeLst ctrs: LeLst.
Qed.

Lemma lem_lelst_perm_rev {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation l1 l2 -> forall x, LeLst x l2 -> LeLst x l1.
Proof.
  induction 1; sauto inv: LeLst ctrs: LeLst.
Qed.

Lemma lem_lelst_concat {A} {dto : DecTotalOrder A} :
  forall l1 x, LeLst x l1 -> forall l2, LeLst x l2 -> LeLst x (l1 ++ l2).
Proof.
  induction 1; sauto.
Qed.

Hint Resolve lem_lelst_trans lem_lelst_perm lem_lelst_perm_rev lem_lelst_concat : lelst.

Lemma lem_sorted_concat_1 {A} {dto : DecTotalOrder A} :
  forall (l1 : list A) x, Sorted (x :: l1) -> forall l2 y,
      leb x y -> Sorted (y :: l2) -> forall l,
        Permutation l (l1 ++ y :: l2) -> Sorted l ->
        Sorted (x :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Lemma lem_sorted_concat_2 {A} {dto : DecTotalOrder A} :
  forall (l1 : list A) x, Sorted (x :: l1) -> forall l2 y,
      leb y x -> Sorted (y :: l2) -> forall l,
        Permutation l (x :: l1 ++ l2) -> Sorted l ->
        Sorted (y :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Program Fixpoint merge {A} {dto : DecTotalOrder A} (l1 l2 : {l : list A | Sorted l})
        {measure (List.length l1 + List.length l2)} :
  {l : list A | Sorted l /\ Permutation l (l1 ++ l2)} :=
  match l1 with
  | [] => l2
  | h1 :: t1 =>
    match l2 with
    | [] => l1
    | h2 :: t2 =>
      if leb_total_dec h1 h2 then
        h1 :: merge t1 l2
      else
        h2 :: merge l1 t2
    end
  end.
Next Obligation.
  sauto db: list.
Qed.
Next Obligation.
  eauto using lem_sorted_tail.
Qed.
Next Obligation.
  sauto use: lem_sorted_concat_1.
Qed.
Next Obligation.
  eauto using lem_sorted_tail.
Qed.
Next Obligation.
  simpl; lia.
Qed.
Next Obligation.
  split.
  - sauto use: lem_sorted_concat_2.
  - (* sauto use: List.app_comm_cons, Permutation_cons_app. *)
    rewrite List.app_comm_cons.
    apply Permutation_cons_app.
    sauto.
Qed.

Program Fixpoint split {A} (l : list A) {measure (length l)} :
  { (l1, l2) : list A * list A |
    length l1 + length l2 = length l /\
    length l1 <= length l2 + 1 /\ length l2 <= length l1 + 1 /\
    Permutation l (l1 ++ l2) } :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t =>
    match split t with
    | (l1, l2) => (x :: l1, y :: l2)
    end
  end.
Solve Obligations with sauto use: Permutation_cons_app.

Compute ` (split [1; 2; 3; 4; 5; 6; 7; 8; 9]).

Lemma lem_split {A} : forall l : list A,
    2 <= List.length l ->
    forall l1 l2, (l1, l2) = ` (split l) ->
    List.length l1 < List.length l /\
    List.length l2 < List.length l.
Proof.
  sauto.
Qed.

Ltac use_lem_split :=
  match goal with
  | [ H: (?l1, ?l2) = ` (split ?l) |- _ ] =>
    let Hl := fresh "H" in
    assert (Hl: 2 <= length l);
    [ destruct l as [|? [| ? ?]]; simpl |
      generalize (lem_split l Hl l1 l2) ];
    sauto red: off inv: - ctrs: -
  end.
(* Sometimes "sauto" performs too much reduction. *)
(* "red: off" prevents "sauto" from performing reduction. *)
(* "ered: off" prevents "sauto" from performing reduction eagerly (it
   then still tries to perform reduction with backtracting). *)

Obligation Tactic := idtac.

Program Fixpoint mergesort {A} {dto : DecTotalOrder A} (l : list A)
        {measure (List.length l)} : {l' : list A | Sorted l' /\ Permutation l' l} :=
  match l with
  | [] => []
  | [x] => [x]
  | _ =>
    match split l with
    | (l1, l2) => merge (mergesort l1) (mergesort l2)
    end
  end.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl; use_lem_split.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl; use_lem_split.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  split.
  - sauto.
  - time sauto use: Permutation_app, Permutation_sym, perm_trans inv: - ctrs: -.
    Undo.
    time qauto use: Permutation_app, Permutation_sym, perm_trans.
    (* "qauto" is "sauto" with various options which make it much
       weaker but typically much faster when it can solve the goal *)
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl.
Defined.

Compute ` (mergesort [2; 7; 3; 1; 4; 6; 5; 8; 0; 8]).
