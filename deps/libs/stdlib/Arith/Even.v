From Hammer Require Import Hammer.













Require Import PeanoNat.

Local Open Scope nat_scope.

Implicit Types m n : nat.




Inductive even : nat -> Prop :=
| even_O : even 0
| even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
odd_S : forall n, even n -> odd (S n).

Hint Constructors even: arith.
Hint Constructors odd: arith.



Lemma even_equiv : forall n, even n <-> Nat.Even n.
Proof. hammer_hook "Even" "Even.even_equiv".  
fix 1.
destruct n as [|[|n]]; simpl.
- split; [now exists 0 | constructor].
- split.
+ inversion_clear 1. inversion_clear H0.
+ now rewrite <- Nat.even_spec.
- rewrite Nat.Even_succ_succ, <- even_equiv.
split.
+ inversion_clear 1. now inversion_clear H0.
+ now do 2 constructor.
Qed.

Lemma odd_equiv : forall n, odd n <-> Nat.Odd n.
Proof. hammer_hook "Even" "Even.odd_equiv".  
fix 1.
destruct n as [|[|n]]; simpl.
- split.
+ inversion_clear 1.
+ now rewrite <- Nat.odd_spec.
- split; [ now exists 0 | do 2 constructor ].
- rewrite Nat.Odd_succ_succ, <- odd_equiv.
split.
+ inversion_clear 1. now inversion_clear H0.
+ now do 2 constructor.
Qed.



Lemma even_or_odd n : even n \/ odd n.
Proof. hammer_hook "Even" "Even.even_or_odd".  
induction n.
- auto with arith.
- elim IHn; auto with arith.
Qed.

Lemma even_odd_dec n : {even n} + {odd n}.
Proof. hammer_hook "Even" "Even.even_odd_dec".  
induction n.
- auto with arith.
- elim IHn; auto with arith.
Defined.

Lemma not_even_and_odd n : even n -> odd n -> False.
Proof. hammer_hook "Even" "Even.not_even_and_odd".  
induction n.
- intros Ev Od. inversion Od.
- intros Ev Od. inversion Ev. inversion Od. auto with arith.
Qed.




Ltac parity2bool :=
rewrite ?even_equiv, ?odd_equiv, <- ?Nat.even_spec, <- ?Nat.odd_spec.

Ltac parity_binop_spec :=
rewrite ?Nat.even_add, ?Nat.odd_add, ?Nat.even_mul, ?Nat.odd_mul.

Ltac parity_binop :=
parity2bool; parity_binop_spec; unfold Nat.odd;
do 2 destruct Nat.even; simpl; tauto.


Lemma even_plus_split n m :
even (n + m) -> even n /\ even m \/ odd n /\ odd m.
Proof. hammer_hook "Even" "Even.even_plus_split".   parity_binop. Qed.

Lemma odd_plus_split n m :
odd (n + m) -> odd n /\ even m \/ even n /\ odd m.
Proof. hammer_hook "Even" "Even.odd_plus_split".   parity_binop. Qed.

Lemma even_even_plus n m : even n -> even m -> even (n + m).
Proof. hammer_hook "Even" "Even.even_even_plus".   parity_binop. Qed.

Lemma odd_plus_l n m : odd n -> even m -> odd (n + m).
Proof. hammer_hook "Even" "Even.odd_plus_l".   parity_binop. Qed.

Lemma odd_plus_r n m : even n -> odd m -> odd (n + m).
Proof. hammer_hook "Even" "Even.odd_plus_r".   parity_binop. Qed.

Lemma odd_even_plus n m : odd n -> odd m -> even (n + m).
Proof. hammer_hook "Even" "Even.odd_even_plus".   parity_binop. Qed.

Lemma even_plus_aux n m :
(odd (n + m) <-> odd n /\ even m \/ even n /\ odd m) /\
(even (n + m) <-> even n /\ even m \/ odd n /\ odd m).
Proof. hammer_hook "Even" "Even.even_plus_aux".   parity_binop. Qed.

Lemma even_plus_even_inv_r n m : even (n + m) -> even n -> even m.
Proof. hammer_hook "Even" "Even.even_plus_even_inv_r".   parity_binop. Qed.

Lemma even_plus_even_inv_l n m : even (n + m) -> even m -> even n.
Proof. hammer_hook "Even" "Even.even_plus_even_inv_l".   parity_binop. Qed.

Lemma even_plus_odd_inv_r n m : even (n + m) -> odd n -> odd m.
Proof. hammer_hook "Even" "Even.even_plus_odd_inv_r".   parity_binop. Qed.

Lemma even_plus_odd_inv_l n m : even (n + m) -> odd m -> odd n.
Proof. hammer_hook "Even" "Even.even_plus_odd_inv_l".   parity_binop. Qed.

Lemma odd_plus_even_inv_l n m : odd (n + m) -> odd m -> even n.
Proof. hammer_hook "Even" "Even.odd_plus_even_inv_l".   parity_binop. Qed.

Lemma odd_plus_even_inv_r n m : odd (n + m) -> odd n -> even m.
Proof. hammer_hook "Even" "Even.odd_plus_even_inv_r".   parity_binop. Qed.

Lemma odd_plus_odd_inv_l n m : odd (n + m) -> even m -> odd n.
Proof. hammer_hook "Even" "Even.odd_plus_odd_inv_l".   parity_binop. Qed.

Lemma odd_plus_odd_inv_r n m : odd (n + m) -> even n -> odd m.
Proof. hammer_hook "Even" "Even.odd_plus_odd_inv_r".   parity_binop. Qed.




Lemma even_mult_aux n m :
(odd (n * m) <-> odd n /\ odd m) /\ (even (n * m) <-> even n \/ even m).
Proof. hammer_hook "Even" "Even.even_mult_aux".   parity_binop. Qed.

Lemma even_mult_l n m : even n -> even (n * m).
Proof. hammer_hook "Even" "Even.even_mult_l".   parity_binop. Qed.

Lemma even_mult_r n m : even m -> even (n * m).
Proof. hammer_hook "Even" "Even.even_mult_r".   parity_binop. Qed.

Lemma even_mult_inv_r n m : even (n * m) -> odd n -> even m.
Proof. hammer_hook "Even" "Even.even_mult_inv_r".   parity_binop. Qed.

Lemma even_mult_inv_l n m : even (n * m) -> odd m -> even n.
Proof. hammer_hook "Even" "Even.even_mult_inv_l".   parity_binop. Qed.

Lemma odd_mult n m : odd n -> odd m -> odd (n * m).
Proof. hammer_hook "Even" "Even.odd_mult".   parity_binop. Qed.

Lemma odd_mult_inv_l n m : odd (n * m) -> odd n.
Proof. hammer_hook "Even" "Even.odd_mult_inv_l".   parity_binop. Qed.

Lemma odd_mult_inv_r n m : odd (n * m) -> odd m.
Proof. hammer_hook "Even" "Even.odd_mult_inv_r".   parity_binop. Qed.

Hint Resolve
even_even_plus odd_even_plus odd_plus_l odd_plus_r
even_mult_l even_mult_r even_mult_l even_mult_r odd_mult : arith.
