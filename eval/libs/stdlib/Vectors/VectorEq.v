From Hammer Require Import Hammer.











Require Import VectorDef.
Require Import VectorSpec.
Import VectorNotations.

Section BEQ.

Variables (A: Type) (A_beq: A -> A -> bool).
Hypothesis A_eqb_eq: forall x y, A_beq x y = true <-> x = y.

Definition eqb:
forall {m n} (v1: t A m) (v2: t A n), bool :=
fix fix_beq {m n} v1 v2 :=
match v1, v2 with
|[], [] => true
|_ :: _, [] |[], _ :: _ => false
|h1 :: t1, h2 :: t2 => A_beq h1 h2 && fix_beq t1 t2
end%bool.

Lemma eqb_nat_eq: forall m n (v1: t A m) (v2: t A n)
(Hbeq: eqb v1 v2 = true), m = n.
Proof. hammer_hook "VectorEq" "VectorEq.eqb_nat_eq". Restart. 
intros m n v1; revert n.
induction v1; destruct v2;
[now constructor | discriminate | discriminate | simpl].
intros Hbeq; apply andb_prop in Hbeq; destruct Hbeq.
f_equal; eauto.
Qed.

Lemma eqb_eq: forall n (v1: t A n) (v2: t A n),
eqb v1 v2 = true <-> v1 = v2.
Proof. hammer_hook "VectorEq" "VectorEq.eqb_eq". Restart. 
refine (@rect2 _ _ _ _ _); [now constructor | simpl].
intros ? ? ? Hrec h1 h2; destruct Hrec; destruct (A_eqb_eq h1 h2); split.
+ intros Hbeq. apply andb_prop in Hbeq; destruct Hbeq.
f_equal; now auto.
+ intros Heq. destruct (cons_inj Heq). apply andb_true_intro.
split; now auto.
Qed.

Definition eq_dec n (v1 v2: t A n): {v1 = v2} + {v1 <> v2}.
Proof. hammer_hook "VectorEq" "VectorEq.eq_dec". Restart. 
case_eq (eqb v1 v2); intros.
+ left; now apply eqb_eq.
+ right. intros Heq. apply <- eqb_eq in Heq. congruence.
Defined.

End BEQ.

Section CAST.

Definition cast: forall {A m} (v: t A m) {n}, m = n -> t A n.
Proof. hammer_hook "VectorEq" "VectorEq.cast". Restart. 
refine (fix cast {A m} (v: t A m) {struct v} :=
match v in t _ m' return forall n, m' = n -> t A n with
|[] => fun n => match n with
| 0 => fun _ => []
| S _ => fun H => False_rect _ _
end
|h :: w => fun n => match n with
| 0 => fun H => False_rect _ _
| S n' => fun H => h :: (cast w n' (f_equal pred H))
end
end); discriminate.
Defined.

End CAST.
