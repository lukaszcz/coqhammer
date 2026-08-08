From Hammer Require Import Hammer.
From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.
Import ListNotations.

Lemma stdlib_nat_add_0_r : forall n : nat, n + 0 = n.
Proof.
  hammer_hook "stdlib-regression" "stdlib_nat_add_0_r".
  apply Nat.add_0_r.
Qed.

Lemma stdlib_list_map_cons :
  forall (A B : Type) (f : A -> B) (x : A) (xs : list A),
    map f (x :: xs) = f x :: map f xs.
Proof.
  hammer_hook "stdlib-regression" "stdlib_list_map_cons".
  reflexivity.
Qed.

Lemma stdlib_bool_negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
  hammer_hook "stdlib-regression" "stdlib_bool_negb_involutive".
  destruct b; reflexivity.
Qed.
