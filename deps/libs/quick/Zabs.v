From Hammer Require Import Hammer.















Require Import Arith_base.
Require Import BinPos.
Require Import BinInt.
Require Import Zcompare.
Require Import Zorder.
Require Import Znat.
Require Import ZArith_dec.

Local Open Scope Z_scope.




Lemma Zabs_ind :
forall (P:Z -> Prop) (n:Z),
(n >= 0 -> P n) -> (n <= 0 -> P (- n)) -> P (Z.abs n).
Proof. hammer_hook "Zabs" "Zabs.Zabs_ind".
intros. apply Z.abs_case_strong; Z.swap_greater; trivial.
intros x y Hx; now subst.
Qed.

Theorem Zabs_intro : forall P (n:Z), P (- n) -> P n -> P (Z.abs n).
Proof. hammer_hook "Zabs" "Zabs.Zabs_intro".
now destruct n.
Qed.

Definition Zabs_dec : forall x:Z, {x = Z.abs x} + {x = - Z.abs x}.
Proof. hammer_hook "Zabs" "Zabs.Zabs_dec".
destruct x; auto.
Defined.

Lemma Zabs_spec x :
0 <= x /\ Z.abs x = x \/
0 > x /\ Z.abs x = -x.
Proof. hammer_hook "Zabs" "Zabs.Zabs_spec".
Z.swap_greater. apply Z.abs_spec.
Qed.



Lemma Zsgn_spec x :
0 < x /\ Z.sgn x = 1 \/
0 = x /\ Z.sgn x = 0 \/
0 > x /\ Z.sgn x = -1.
Proof. hammer_hook "Zabs" "Zabs.Zsgn_spec".
intros. Z.swap_greater. apply Z.sgn_spec.
Qed.



Lemma Zabs_nat_le n m : 0 <= n <= m -> (Z.abs_nat n <= Z.abs_nat m)%nat.
Proof. hammer_hook "Zabs" "Zabs.Zabs_nat_le".
intros (H,H'). apply Zabs2Nat.inj_le; trivial. now transitivity n.
Qed.

Lemma Zabs_nat_lt n m : 0 <= n < m -> (Z.abs_nat n < Z.abs_nat m)%nat.
Proof. hammer_hook "Zabs" "Zabs.Zabs_nat_lt".
intros (H,H'). apply Zabs2Nat.inj_lt; trivial.
transitivity n; trivial. now apply Z.lt_le_incl.
Qed.
