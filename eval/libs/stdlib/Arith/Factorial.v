From Hammer Require Import Hammer.









Require Import PeanoNat Plus Mult Lt.
Local Open Scope nat_scope.



Fixpoint fact (n:nat) : nat :=
match n with
| O => 1
| S n => S n * fact n
end.

Arguments fact n%nat.

Lemma lt_O_fact n : 0 < fact n.
Proof. hammer_hook "Factorial" "Factorial.lt_O_fact". Restart. 
induction n; simpl; auto with arith.
Qed.

Lemma fact_neq_0 n : fact n <> 0.
Proof. hammer_hook "Factorial" "Factorial.fact_neq_0". Restart. 
apply Nat.neq_0_lt_0, lt_O_fact.
Qed.

Lemma fact_le n m : n <= m -> fact n <= fact m.
Proof. hammer_hook "Factorial" "Factorial.fact_le". Restart. 
induction 1.
- apply le_n.
- simpl. transitivity (fact m). trivial. apply Nat.le_add_r.
Qed.
