(* ATP-level consistency canaries for the extraction-factored translation plan.
   Each goal is dumped with Hammer_dump; check-consistency.sh replaces the
   conjecture by $false and asks ATPs to ensure the selected axiom set is not
   already inconsistent. *)

From Hammer Require Import Hammer.

From Stdlib Require Import Arith.PeanoNat Strings.String.

Require Import extraction_deptypes.

Open Scope string_scope.

Set Hammer SAutoLimit 0.
Set Hammer Predictions 1024.

Goal forall a b p, b <> 0 -> a < b -> idiv a b p = 0.
  hammer_dump "consistency-idiv.p".
Abort.

Goal forall b Hb a, b <> 0 -> a < b -> idiv2 b Hb a = 0.
  hammer_dump "consistency-idiv2.p".
Abort.

Goal forall x y z p, proj1_sig (h x y z p) = z.
  hammer_dump "consistency-h.p".
Abort.

Goal forall (P : nat -> Set) a (e : a = a) x, tr P a a e x = x.
  hammer_dump "transport-tr-refl.p".
Abort.

Goal forall (P : nat -> Set) a (e1 e2 : a = a) (x : P a),
    eq_rect a P (eq_rect a P x a e1) a e2 = x.
  hammer_dump "consistency-eq-rect.p".
Abort.

Goal 2 + 2 = 4.
  hammer_dump "consistency-nat-add.p".
Abort.
