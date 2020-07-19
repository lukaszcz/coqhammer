From Hammer Require Import Tactics.
From Hammer Require Import Reflect.

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
  sauto.
Qed.

(* "LeLst x l" holds if "x" is smaller or equal to all elements in "l" *)
Definition LeLst {A} {dto : DecTotalOrder A} (x : A) :=
  List.Forall (leb x).

Lemma lem_lelst_trans {A} {dto : DecTotalOrder A} :
  forall l y, LeLst y l -> forall x, leb x y -> LeLst x l.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_lelst_sorted {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  (* induction l; sintuition. *)
  (* simplification tactics: sintuition, qsimpl, ssimpl *)
  (* induction l; qsimpl. *)
  (* From "Sorted (a :: l)" it follows that "LeLst a l" by "H1". *)
  (* Because "leb x l", "LeLst x (a :: l)" follows from "LeLst a l" by
     lemma "lem_lelst_trans" *)
  (* time (induction l; sauto use: lem_lelst_trans). *)
  (* induction l; sauto use: lem_lelst_trans inv: Sorted, List.Forall. *)
  (* induction l; sauto use: lem_lelst_trans inv: Sorted. *)
  (* induction l; sauto use: lem_lelst_trans inv: List.Forall.*)
  time (induction l;
        sauto use: lem_lelst_trans inv: Sorted, List.Forall ctrs: Sorted).
  Undo.
  time (induction l;
        sauto lazy: on use: lem_lelst_trans
          inv: Sorted, List.Forall ctrs: Sorted).
  (* "lazy: on" turns off all eager heuristics. This may improve
     performance, but may also make "sauto" fail to solve the goal *)
Qed.

Lemma lem_lelst_perm_rev {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation l1 l2 -> forall x, LeLst x l2 -> LeLst x l1.
Proof.
  (* induction 1; sauto. *)
  induction 1; sauto inv: List.Forall ctrs: List.Forall.
Qed.

Lemma lem_lelst_app {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, LeLst x l1 -> LeLst x l2 -> LeLst x (l1 ++ l2).
Proof.
  induction 1; sauto.
Qed.

Hint Resolve lem_lelst_trans lem_lelst_perm_rev lem_lelst_app : lelst.

Lemma lem_sorted_concat_1 {A} {dto : DecTotalOrder A} :
  forall (l l1 l2 : list A) x y,
    Permutation l (l1 ++ y :: l2) -> Sorted (x :: l1) -> leb x y ->
    Sorted (y :: l2) -> Sorted l -> Sorted (x :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  (* sauto db: lelst inv: -. *)
  split.
  simp_hyps.
  eapply lem_lelst_perm_rev; [eassumption|].
  apply lem_lelst_app; [assumption|].
  constructor; [assumption|].
  Check lem_lelst_trans.
  eauto using lem_lelst_trans.
  eapply lem_lelst_trans; eassumption.

  (* Here, "sauto" needs to apply a constructor of "List.Forall",
     which works on a goal with head "LeLst", but then creates a goal
     with head "List.Forall" which does not resolve with the
     "lem_lelst_trans" lemma according to how "eauto" performs
     resolution *)

  Restart.

  intros.
  rewrite lem_lelst_sorted in *.
  sauto use: lem_lelst_trans, lem_lelst_perm_rev, lem_lelst_app inv: -.
  (* "use:" adds the given lemmas to the context, while for lemmas
     from a hint database only actions associated with the hints are
     performed in exactly the same way as by "eauto" *)
Qed.

Lemma lem_lelst_nil {A} {dto : DecTotalOrder A} : forall x, LeLst x [].
Proof.
  sauto.
Qed.

Lemma lem_lelst_cons {A} {dto : DecTotalOrder A} :
  forall x y l, LeLst x l -> leb x y -> LeLst x (y :: l).
Proof.
  sauto.
Qed.

Hint Resolve lem_lelst_nil lem_lelst_cons : lelst.

Lemma lem_sorted_concat_2 {A} {dto : DecTotalOrder A} :
  forall (l l1 l2 : list A) x y,
    Permutation l (x :: l1 ++ l2) -> Sorted (x :: l1) -> leb y x ->
    Sorted (y :: l2) -> Sorted l -> Sorted (y :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Program Fixpoint merge {A} {dto : DecTotalOrder A}
  (l1 l2 : {l | Sorted l}) {measure (List.length l1 + List.length l2)} :
  {l | Sorted l /\ Permutation l (l1 ++ l2)} :=
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
  (* What happened here? *)
  Undo.
  simpl_sigma.
  (* Heuristic simplifications for sigma types are performed by
     default (controlled by the "sig:" option) *)
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
    simpl_sigma.
    rewrite List.app_comm_cons.
    apply Permutation_cons_app.
    intuition. (* at this point "sauto" would of course also solve the
                  goal *)
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
    hauto
  end.

Obligation Tactic := idtac.

Program Fixpoint mergesort {A} {dto : DecTotalOrder A} (l : list A)
  {measure (List.length l)} : {l' | Sorted l' /\ Permutation l' l} :=
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
  (* sauto. *)
  program_simpl.
  (* sauto use: @lem_split. *)
  use_lem_split.
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
  - time hauto use: Permutation_app, Permutation_sym, perm_trans.
    Undo.
    time qauto use: Permutation_app, Permutation_sym, perm_trans.
    (* "qauto" is "sauto" with various options which make it much
       weaker but typically much faster *)
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl.
Defined.

Compute ` (mergesort [2; 7; 3; 1; 4; 6; 5; 8; 0; 8]).
