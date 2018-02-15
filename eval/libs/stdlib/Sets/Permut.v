From Hammer Require Import Hammer.













Section Axiomatisation.

Variable U : Type.
Variable op : U -> U -> U.
Variable cong : U -> U -> Prop.

Hypothesis op_comm : forall x y:U, cong (op x y) (op y x).
Hypothesis op_ass : forall x y z:U, cong (op (op x y) z) (op x (op y z)).

Hypothesis cong_left : forall x y z:U, cong x y -> cong (op x z) (op y z).
Hypothesis cong_right : forall x y z:U, cong x y -> cong (op z x) (op z y).
Hypothesis cong_trans : forall x y z:U, cong x y -> cong y z -> cong x z.
Hypothesis cong_sym : forall x y:U, cong x y -> cong y x.



Lemma cong_congr :
forall x y z t:U, cong x y -> cong z t -> cong (op x z) (op y t).
Proof. hammer_hook "Permut" "Permut.cong_congr". Restart. 
intros; apply cong_trans with (op y z).
apply cong_left; trivial.
apply cong_right; trivial.
Qed.

Lemma comm_right : forall x y z:U, cong (op x (op y z)) (op x (op z y)).
Proof. hammer_hook "Permut" "Permut.comm_right". Restart. 
intros; apply cong_right; apply op_comm.
Qed.

Lemma comm_left : forall x y z:U, cong (op (op x y) z) (op (op y x) z).
Proof. hammer_hook "Permut" "Permut.comm_left". Restart. 
intros; apply cong_left; apply op_comm.
Qed.

Lemma perm_right : forall x y z:U, cong (op (op x y) z) (op (op x z) y).
Proof. hammer_hook "Permut" "Permut.perm_right". Restart. 
intros.
apply cong_trans with (op x (op y z)).
apply op_ass.
apply cong_trans with (op x (op z y)).
apply cong_right; apply op_comm.
apply cong_sym; apply op_ass.
Qed.

Lemma perm_left : forall x y z:U, cong (op x (op y z)) (op y (op x z)).
Proof. hammer_hook "Permut" "Permut.perm_left". Restart. 
intros.
apply cong_trans with (op (op x y) z).
apply cong_sym; apply op_ass.
apply cong_trans with (op (op y x) z).
apply cong_left; apply op_comm.
apply op_ass.
Qed.

Lemma op_rotate : forall x y z t:U, cong (op x (op y z)) (op z (op x y)).
Proof. hammer_hook "Permut" "Permut.op_rotate". Restart. 
intros; apply cong_trans with (op (op x y) z).
apply cong_sym; apply op_ass.
apply op_comm.
Qed.


Lemma twist :
forall x y z t:U, cong (op x (op (op y z) t)) (op (op y (op x t)) z).
Proof. hammer_hook "Permut" "Permut.twist". Restart. 
intros.
apply cong_trans with (op x (op (op y t) z)).
apply cong_right; apply perm_right.
apply cong_trans with (op (op x (op y t)) z).
apply cong_sym; apply op_ass.
apply cong_left; apply perm_left.
Qed.

End Axiomatisation.
