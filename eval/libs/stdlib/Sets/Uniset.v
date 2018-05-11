From Hammer Require Import Hammer.














Require Import Bool.

Set Implicit Arguments.

Section defs.

Variable A : Set.
Variable eqA : A -> A -> Prop.
Hypothesis eqA_dec : forall x y:A, {eqA x y} + {~ eqA x y}.

Inductive uniset : Set :=
Charac : (A -> bool) -> uniset.

Definition charac (s:uniset) (a:A) : bool := let (f) := s in f a.

Definition Emptyset := Charac (fun a:A => false).

Definition Fullset := Charac (fun a:A => true).

Definition Singleton (a:A) :=
Charac
(fun a':A =>
match eqA_dec a a' with
| left h => true
| right h => false
end).

Definition In (s:uniset) (a:A) : Prop := charac s a = true.
Hint Unfold In.


Definition incl (s1 s2:uniset) := forall a:A, leb (charac s1 a) (charac s2 a).
Hint Unfold incl.


Definition seq (s1 s2:uniset) := forall a:A, charac s1 a = charac s2 a.
Hint Unfold seq.

Lemma leb_refl : forall b:bool, leb b b.
Proof. try hammer_hook "Uniset" "Uniset.leb_refl".  
destruct b; simpl; auto.
Qed.
Hint Resolve leb_refl.

Lemma incl_left : forall s1 s2:uniset, seq s1 s2 -> incl s1 s2.
Proof. try hammer_hook "Uniset" "Uniset.incl_left".  
unfold incl; intros s1 s2 E a; elim (E a); auto.
Qed.

Lemma incl_right : forall s1 s2:uniset, seq s1 s2 -> incl s2 s1.
Proof. try hammer_hook "Uniset" "Uniset.incl_right".  
unfold incl; intros s1 s2 E a; elim (E a); auto.
Qed.

Lemma seq_refl : forall x:uniset, seq x x.
Proof. try hammer_hook "Uniset" "Uniset.seq_refl".  
destruct x; unfold seq; auto.
Qed.
Hint Resolve seq_refl.

Lemma seq_trans : forall x y z:uniset, seq x y -> seq y z -> seq x z.
Proof. try hammer_hook "Uniset" "Uniset.seq_trans".  
unfold seq.
destruct x; destruct y; destruct z; simpl; intros.
rewrite H; auto.
Qed.

Lemma seq_sym : forall x y:uniset, seq x y -> seq y x.
Proof. try hammer_hook "Uniset" "Uniset.seq_sym".  
unfold seq.
destruct x; destruct y; simpl; auto.
Qed.


Definition union (m1 m2:uniset) :=
Charac (fun a:A => orb (charac m1 a) (charac m2 a)).

Lemma union_empty_left : forall x:uniset, seq x (union Emptyset x).
Proof. try hammer_hook "Uniset" "Uniset.union_empty_left".  
unfold seq; unfold union; simpl; auto.
Qed.
Hint Resolve union_empty_left.

Lemma union_empty_right : forall x:uniset, seq x (union x Emptyset).
Proof. try hammer_hook "Uniset" "Uniset.union_empty_right".  
unfold seq; unfold union; simpl.
intros x a; rewrite (orb_b_false (charac x a)); auto.
Qed.
Hint Resolve union_empty_right.

Lemma union_comm : forall x y:uniset, seq (union x y) (union y x).
Proof. try hammer_hook "Uniset" "Uniset.union_comm".  
unfold seq; unfold charac; unfold union.
destruct x; destruct y; auto with bool.
Qed.
Hint Resolve union_comm.

Lemma union_ass :
forall x y z:uniset, seq (union (union x y) z) (union x (union y z)).
Proof. try hammer_hook "Uniset" "Uniset.union_ass".  
unfold seq; unfold union; unfold charac.
destruct x; destruct y; destruct z; auto with bool.
Qed.
Hint Resolve union_ass.

Lemma seq_left : forall x y z:uniset, seq x y -> seq (union x z) (union y z).
Proof. try hammer_hook "Uniset" "Uniset.seq_left".  
unfold seq; unfold union; unfold charac.
destruct x; destruct y; destruct z.
intros; elim H; auto.
Qed.
Hint Resolve seq_left.

Lemma seq_right : forall x y z:uniset, seq x y -> seq (union z x) (union z y).
Proof. try hammer_hook "Uniset" "Uniset.seq_right".  
unfold seq; unfold union; unfold charac.
destruct x; destruct y; destruct z.
intros; elim H; auto.
Qed.
Hint Resolve seq_right.






Require Import Permut.

Lemma union_rotate :
forall x y z:uniset, seq (union x (union y z)) (union z (union x y)).
Proof. try hammer_hook "Uniset" "Uniset.union_rotate".  
intros; apply (op_rotate uniset union seq); auto.
exact seq_trans.
Qed.

Lemma seq_congr :
forall x y z t:uniset, seq x y -> seq z t -> seq (union x z) (union y t).
Proof. try hammer_hook "Uniset" "Uniset.seq_congr".  
intros; apply (cong_congr uniset union seq); auto.
exact seq_trans.
Qed.

Lemma union_perm_left :
forall x y z:uniset, seq (union x (union y z)) (union y (union x z)).
Proof. try hammer_hook "Uniset" "Uniset.union_perm_left".  
intros; apply (perm_left uniset union seq); auto.
exact seq_trans.
Qed.

Lemma uniset_twist1 :
forall x y z t:uniset,
seq (union x (union (union y z) t)) (union (union y (union x t)) z).
Proof. try hammer_hook "Uniset" "Uniset.uniset_twist1".  
intros; apply (twist uniset union seq); auto.
exact seq_trans.
Qed.

Lemma uniset_twist2 :
forall x y z t:uniset,
seq (union x (union (union y z) t)) (union (union y (union x z)) t).
Proof. try hammer_hook "Uniset" "Uniset.uniset_twist2".  
intros; apply seq_trans with (union (union x (union y z)) t).
apply seq_sym; apply union_ass.
apply seq_left; apply union_perm_left.
Qed.



Lemma treesort_twist1 :
forall x y z t u:uniset,
seq u (union y z) ->
seq (union x (union u t)) (union (union y (union x t)) z).
Proof. try hammer_hook "Uniset" "Uniset.treesort_twist1".  
intros; apply seq_trans with (union x (union (union y z) t)).
apply seq_right; apply seq_left; trivial.
apply uniset_twist1.
Qed.

Lemma treesort_twist2 :
forall x y z t u:uniset,
seq u (union y z) ->
seq (union x (union u t)) (union (union y (union x z)) t).
Proof. try hammer_hook "Uniset" "Uniset.treesort_twist2".  
intros; apply seq_trans with (union x (union (union y z) t)).
apply seq_right; apply seq_left; trivial.
apply uniset_twist2.
Qed.




End defs.

Unset Implicit Arguments.
