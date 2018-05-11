From Hammer Require Import Hammer.









Require Import PeanoNat.
Local Open Scope nat_scope.





Fixpoint eq_nat n m : Prop :=
match n, m with
| O, O => True
| O, S _ => False
| S _, O => False
| S n1, S m1 => eq_nat n1 m1
end.

Theorem eq_nat_refl n : eq_nat n n.
Proof. try hammer_hook "EqNat" "EqNat.eq_nat_refl".  
induction n; simpl; auto.
Qed.
Hint Resolve eq_nat_refl: arith.



Theorem eq_nat_is_eq n m : eq_nat n m <-> n = m.
Proof. try hammer_hook "EqNat" "EqNat.eq_nat_is_eq".  
split.
- revert m; induction n; destruct m; simpl; contradiction || auto.
- intros <-; apply eq_nat_refl.
Qed.

Lemma eq_eq_nat n m : n = m -> eq_nat n m.
Proof. try hammer_hook "EqNat" "EqNat.eq_eq_nat".  
apply eq_nat_is_eq.
Qed.

Lemma eq_nat_eq n m : eq_nat n m -> n = m.
Proof. try hammer_hook "EqNat" "EqNat.eq_nat_eq".  
apply eq_nat_is_eq.
Qed.

Hint Immediate eq_eq_nat eq_nat_eq: arith.

Theorem eq_nat_elim :
forall n (P:nat -> Prop), P n -> forall m, eq_nat n m -> P m.
Proof. try hammer_hook "EqNat" "EqNat.eq_nat_elim".  
intros; replace m with n; auto with arith.
Qed.

Theorem eq_nat_decide : forall n m, {eq_nat n m} + {~ eq_nat n m}.
Proof. try hammer_hook "EqNat" "EqNat.eq_nat_decide".  
induction n; destruct m; simpl.
- left; trivial.
- right; intro; trivial.
- right; intro; trivial.
- apply IHn.
Defined.




Notation beq_nat := Nat.eqb (compat "8.4").

Notation beq_nat_true_iff := Nat.eqb_eq (compat "8.4").
Notation beq_nat_false_iff := Nat.eqb_neq (compat "8.4").

Lemma beq_nat_refl n : true = (n =? n).
Proof. try hammer_hook "EqNat" "EqNat.beq_nat_refl".  
symmetry. apply Nat.eqb_refl.
Qed.

Lemma beq_nat_true n m : (n =? m) = true -> n=m.
Proof. try hammer_hook "EqNat" "EqNat.beq_nat_true".  
apply Nat.eqb_eq.
Qed.

Lemma beq_nat_false n m : (n =? m) = false -> n<>m.
Proof. try hammer_hook "EqNat" "EqNat.beq_nat_false".  
apply Nat.eqb_neq.
Qed.



Definition beq_nat_eq : forall n m, true = (n =? m) -> n = m.
Proof. try hammer_hook "EqNat" "EqNat.beq_nat_eq".  
induction n; destruct m; simpl.
- reflexivity.
- discriminate.
- discriminate.
- intros H. case (IHn _ H). reflexivity.
Defined.
