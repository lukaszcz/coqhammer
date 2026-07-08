(* ATP-level consistency canaries for the extraction-factored translation plan.
   Each goal is dumped with Hammer_dump; check-consistency.sh replaces the
   conjecture by $false and asks ATPs to ensure the selected axiom set is not
   already inconsistent. *)

From Hammer Require Import Hammer.

From Stdlib Require Import Arith.PeanoNat.

Require Import extraction_deptypes.

Set Hammer SAutoLimit 0.
Set Hammer Predictions 1024.

Goal forall a b p, b <> 0 -> a < b -> idiv a b p = 0.
  Hammer_dump "consistency-idiv.p".
Abort.

Goal forall x y z p, proj1_sig (h x y z p) = z.
  Hammer_dump "consistency-h.p".
Abort.

Goal forall (P : nat -> Set) a (e1 e2 : a = a) (x : P a),
    eq_rect a P (eq_rect a P x a e1) a e2 = x.
  Hammer_dump "consistency-eq-rect.p".
Abort.

Goal 2 + 2 = 4.
  Hammer_dump "consistency-nat-add.p".
Abort.
