From Hammer Require Import Tactics Reflect.

Require List.
Open Scope list_scope.
Import List.ListNotations.

Class DecTotalOrder (A : Type) := {
  leb : A -> A -> bool;
  leb_total_dec : forall x y, {leb x y}+{leb y x};
  leb_antisym : forall x y, leb x y -> leb y x -> x = y;
  leb_trans : forall x y z, leb x y -> leb y z -> leb x z }.

Arguments leb {A _}.
Arguments leb_total_dec {A _}.
Arguments leb_antisym {A _}.
Arguments leb_trans {A _}.

Definition eq_dec {A} {dto : DecTotalOrder A} : forall x y : A, {x = y}+{x <> y}.
  intros x y.
  sdestruct (leb x y).
  (* The "sdestruct" tactic from the Tactics module destructs boolean
     terms in the "right" way *)
  (* "sauto" tries to invert/destruct only the hypotheses - it will
     not normally try to eliminate composite terms unless they occur
     as discriminees in match expressions *)
  - sdestruct (leb y x).
    + auto using leb_antisym.
    + (* firstorder. *)
      (* easy. *)
      (* eauto. *)
      (* right. intro. subst. contradiction. *)
      sauto.
      (* This is a simple proof, but standard Coq automation tactics
         can't find it because requires a combination of proof search
         with equality reasoning. *)
  - sdestruct (leb y x).
    + sauto.
    + destruct (leb_total_dec x y); auto.
Defined.

Require Import Recdef. (* for Function *)

Function lexb {A} {dto : DecTotalOrder A} (l1 l2 : list A) : bool :=
  match l1 with
  | [] => true
  | x :: l1' =>
    match l2 with
    | [] => false
    | y :: l2' =>
      if eq_dec x y then
        lexb l1' l2'
      else
        leb x y
    end
  end.

Instance dto_list {A} {dto_a : DecTotalOrder A} : DecTotalOrder (list A).
Proof.
  apply Build_DecTotalOrder with (leb := lexb).
  - induction x; sauto.
  - intros x y.
    functional induction (lexb x y).
    + (* sauto. *)
      sauto inv: list.
    + sauto.
    + sauto.
    + (* sauto. *)
      (* ssimpl inv: -. *)
      sauto inv: - use: leb_antisym.
  - intros x y.
    functional induction (lexb x y); sauto.
Defined.

Instance dto_nat : DecTotalOrder nat.
Proof.
  apply Build_DecTotalOrder with (leb := Nat.leb);
    induction x; sauto.
Defined.

Compute leb [1; 2; 3] [1; 4; 5; 6].
Compute leb [1; 2; 3] [1].
Compute leb 2 3.
Compute leb 3 2.
