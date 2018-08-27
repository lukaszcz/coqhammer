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
Proof. try hammer_hook "Zabs" "Zabs.Zabs_ind". Undo.
intros. apply Z.abs_case_strong; Z.swap_greater; trivial.
intros x y Hx; now subst.
Qed.

Theorem Zabs_intro : forall P (n:Z), P (- n) -> P n -> P (Z.abs n).
Proof. try hammer_hook "Zabs" "Zabs.Zabs_intro". Undo.
now destruct n.
Qed.

Definition Zabs_dec : forall x:Z, {x = Z.abs x} + {x = - Z.abs x}.
Proof. try hammer_hook "Zabs" "Zabs.Zabs_dec". Undo.
destruct x; auto.
Defined.

Lemma Zabs_spec x :
0 <= x /\ Z.abs x = x \/
0 > x /\ Z.abs x = -x.
Proof. try hammer_hook "Zabs" "Zabs.Zabs_spec". Undo.
Z.swap_greater. apply Z.abs_spec.
Qed.



Lemma Zsgn_spec x :
0 < x /\ Z.sgn x = 1 \/
0 = x /\ Z.sgn x = 0 \/
0 > x /\ Z.sgn x = -1.
Proof. try hammer_hook "Zabs" "Zabs.Zsgn_spec". Undo.
intros. Z.swap_greater. apply Z.sgn_spec.
Qed.



Lemma Zabs_nat_le n m : 0 <= n <= m -> (Z.abs_nat n <= Z.abs_nat m)%nat.
Proof. try hammer_hook "Zabs" "Zabs.Zabs_nat_le". Undo.
intros (H,H'). apply Zabs2Nat.inj_le; trivial. now transitivity n.
Qed.

Lemma Zabs_nat_lt n m : 0 <= n < m -> (Z.abs_nat n < Z.abs_nat m)%nat.
Proof. try hammer_hook "Zabs" "Zabs.Zabs_nat_lt". Undo.
intros (H,H'). apply Zabs2Nat.inj_lt; trivial.
transitivity n; trivial. now apply Z.lt_le_incl.
Qed.
