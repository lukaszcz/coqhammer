From Hammer Require Import Hammer.









Require Import Le Lt Gt Decidable PeanoNat.

Local Open Scope nat_scope.

Implicit Types m n x y : nat.

Definition zerop n : {n = 0} + {0 < n}.
Proof. hammer_hook "Compare_dec" "Compare_dec.zerop". Restart. 
destruct n; auto with arith.
Defined.

Definition lt_eq_lt_dec n m : {n < m} + {n = m} + {m < n}.
Proof. hammer_hook "Compare_dec" "Compare_dec.lt_eq_lt_dec". Restart. 
induction n in m |- *; destruct m; auto with arith.
destruct (IHn m) as [H|H]; auto with arith.
destruct H; auto with arith.
Defined.

Definition gt_eq_gt_dec n m : {m > n} + {n = m} + {n > m}.
Proof. hammer_hook "Compare_dec" "Compare_dec.gt_eq_gt_dec". Restart. 
now apply lt_eq_lt_dec.
Defined.

Definition le_lt_dec n m : {n <= m} + {m < n}.
Proof. hammer_hook "Compare_dec" "Compare_dec.le_lt_dec". Restart. 
induction n in m |- *.
- left; auto with arith.
- destruct m.
+ right; auto with arith.
+ elim (IHn m); [left|right]; auto with arith.
Defined.

Definition le_le_S_dec n m : {n <= m} + {S m <= n}.
Proof. hammer_hook "Compare_dec" "Compare_dec.le_le_S_dec". Restart. 
exact (le_lt_dec n m).
Defined.

Definition le_ge_dec n m : {n <= m} + {n >= m}.
Proof. hammer_hook "Compare_dec" "Compare_dec.le_ge_dec". Restart. 
elim (le_lt_dec n m); auto with arith.
Defined.

Definition le_gt_dec n m : {n <= m} + {n > m}.
Proof. hammer_hook "Compare_dec" "Compare_dec.le_gt_dec". Restart. 
exact (le_lt_dec n m).
Defined.

Definition le_lt_eq_dec n m : n <= m -> {n < m} + {n = m}.
Proof. hammer_hook "Compare_dec" "Compare_dec.le_lt_eq_dec". Restart. 
intros; destruct (lt_eq_lt_dec n m); auto with arith.
intros; absurd (m < n); auto with arith.
Defined.

Theorem le_dec n m : {n <= m} + {~ n <= m}.
Proof. hammer_hook "Compare_dec" "Compare_dec.le_dec". Restart. 
destruct (le_gt_dec n m).
- now left.
- right. now apply gt_not_le.
Defined.

Theorem lt_dec n m : {n < m} + {~ n < m}.
Proof. hammer_hook "Compare_dec" "Compare_dec.lt_dec". Restart. 
apply le_dec.
Defined.

Theorem gt_dec n m : {n > m} + {~ n > m}.
Proof. hammer_hook "Compare_dec" "Compare_dec.gt_dec". Restart. 
apply lt_dec.
Defined.

Theorem ge_dec n m : {n >= m} + {~ n >= m}.
Proof. hammer_hook "Compare_dec" "Compare_dec.ge_dec". Restart. 
apply le_dec.
Defined.



Theorem dec_le n m : decidable (n <= m).
Proof. hammer_hook "Compare_dec" "Compare_dec.dec_le". Restart. 
apply Nat.le_decidable.
Qed.

Theorem dec_lt n m : decidable (n < m).
Proof. hammer_hook "Compare_dec" "Compare_dec.dec_lt". Restart. 
apply Nat.lt_decidable.
Qed.

Theorem dec_gt n m : decidable (n > m).
Proof. hammer_hook "Compare_dec" "Compare_dec.dec_gt". Restart. 
apply Nat.lt_decidable.
Qed.

Theorem dec_ge n m : decidable (n >= m).
Proof. hammer_hook "Compare_dec" "Compare_dec.dec_ge". Restart. 
apply Nat.le_decidable.
Qed.

Theorem not_eq n m : n <> m -> n < m \/ m < n.
Proof. hammer_hook "Compare_dec" "Compare_dec.not_eq". Restart. 
apply Nat.lt_gt_cases.
Qed.

Theorem not_le n m : ~ n <= m -> n > m.
Proof. hammer_hook "Compare_dec" "Compare_dec.not_le". Restart. 
apply Nat.nle_gt.
Qed.

Theorem not_gt n m : ~ n > m -> n <= m.
Proof. hammer_hook "Compare_dec" "Compare_dec.not_gt". Restart. 
apply Nat.nlt_ge.
Qed.

Theorem not_ge n m : ~ n >= m -> n < m.
Proof. hammer_hook "Compare_dec" "Compare_dec.not_ge". Restart. 
apply Nat.nle_gt.
Qed.

Theorem not_lt n m : ~ n < m -> n >= m.
Proof. hammer_hook "Compare_dec" "Compare_dec.not_lt". Restart. 
apply Nat.nlt_ge.
Qed.




Notation nat_compare := Nat.compare (compat "8.4").

Notation nat_compare_spec := Nat.compare_spec (compat "8.4").
Notation nat_compare_eq_iff := Nat.compare_eq_iff (compat "8.4").
Notation nat_compare_S := Nat.compare_succ (compat "8.4").

Lemma nat_compare_lt n m : n<m <-> (n ?= m) = Lt.
Proof. hammer_hook "Compare_dec" "Compare_dec.nat_compare_lt". Restart. 
symmetry. apply Nat.compare_lt_iff.
Qed.

Lemma nat_compare_gt n m : n>m <-> (n ?= m) = Gt.
Proof. hammer_hook "Compare_dec" "Compare_dec.nat_compare_gt". Restart. 
symmetry. apply Nat.compare_gt_iff.
Qed.

Lemma nat_compare_le n m : n<=m <-> (n ?= m) <> Gt.
Proof. hammer_hook "Compare_dec" "Compare_dec.nat_compare_le". Restart. 
symmetry. apply Nat.compare_le_iff.
Qed.

Lemma nat_compare_ge n m : n>=m <-> (n ?= m) <> Lt.
Proof. hammer_hook "Compare_dec" "Compare_dec.nat_compare_ge". Restart. 
symmetry. apply Nat.compare_ge_iff.
Qed.



Lemma nat_compare_eq n m : (n ?= m) = Eq -> n = m.
Proof. hammer_hook "Compare_dec" "Compare_dec.nat_compare_eq". Restart. 
apply Nat.compare_eq_iff.
Qed.

Lemma nat_compare_Lt_lt n m : (n ?= m) = Lt -> n<m.
Proof. hammer_hook "Compare_dec" "Compare_dec.nat_compare_Lt_lt". Restart. 
apply Nat.compare_lt_iff.
Qed.

Lemma nat_compare_Gt_gt n m : (n ?= m) = Gt -> n>m.
Proof. hammer_hook "Compare_dec" "Compare_dec.nat_compare_Gt_gt". Restart. 
apply Nat.compare_gt_iff.
Qed.



Definition nat_compare_alt (n m:nat) :=
match lt_eq_lt_dec n m with
| inleft (left _) => Lt
| inleft (right _) => Eq
| inright _ => Gt
end.

Lemma nat_compare_equiv n m : (n ?= m) = nat_compare_alt n m.
Proof. hammer_hook "Compare_dec" "Compare_dec.nat_compare_equiv". Restart. 
unfold nat_compare_alt; destruct lt_eq_lt_dec as [[|]|].
- now apply Nat.compare_lt_iff.
- now apply Nat.compare_eq_iff.
- now apply Nat.compare_gt_iff.
Qed.



Notation leb := Nat.leb (compat "8.4").

Notation leb_iff := Nat.leb_le (compat "8.4").

Lemma leb_iff_conv m n : (n <=? m) = false <-> m < n.
Proof. hammer_hook "Compare_dec" "Compare_dec.leb_iff_conv". Restart. 
rewrite Nat.leb_nle. apply Nat.nle_gt.
Qed.

Lemma leb_correct m n : m <= n -> (m <=? n) = true.
Proof. hammer_hook "Compare_dec" "Compare_dec.leb_correct". Restart. 
apply Nat.leb_le.
Qed.

Lemma leb_complete m n : (m <=? n) = true -> m <= n.
Proof. hammer_hook "Compare_dec" "Compare_dec.leb_complete". Restart. 
apply Nat.leb_le.
Qed.

Lemma leb_correct_conv m n : m < n -> (n <=? m) = false.
Proof. hammer_hook "Compare_dec" "Compare_dec.leb_correct_conv". Restart. 
apply leb_iff_conv.
Qed.

Lemma leb_complete_conv m n : (n <=? m) = false -> m < n.
Proof. hammer_hook "Compare_dec" "Compare_dec.leb_complete_conv". Restart. 
apply leb_iff_conv.
Qed.

Lemma leb_compare n m : (n <=? m) = true <-> (n ?= m) <> Gt.
Proof. hammer_hook "Compare_dec" "Compare_dec.leb_compare". Restart. 
rewrite Nat.compare_le_iff. apply Nat.leb_le.
Qed.
