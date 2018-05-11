From Hammer Require Import Hammer.









Require Export ZArith.
Require Export ZArithRing.
Require Export Morphisms Setoid Bool.





Record Q : Set := Qmake {Qnum : Z; Qden : positive}.

Delimit Scope Q_scope with Q.
Bind Scope Q_scope with Q.
Arguments Qmake _%Z _%positive.
Open Scope Q_scope.
Ltac simpl_mult := rewrite ?Pos2Z.inj_mul.



Notation "a # b" := (Qmake a b) (at level 55, no associativity) : Q_scope.

Definition inject_Z (x : Z) := Qmake x 1.
Arguments inject_Z x%Z.

Notation QDen p := (Zpos (Qden p)).
Notation " 0 " := (0#1) : Q_scope.
Notation " 1 " := (1#1) : Q_scope.

Definition Qeq (p q : Q) := (Qnum p * QDen q)%Z = (Qnum q * QDen p)%Z.
Definition Qle (x y : Q) := (Qnum x * QDen y <= Qnum y * QDen x)%Z.
Definition Qlt (x y : Q) := (Qnum x * QDen y < Qnum y * QDen x)%Z.
Notation Qgt a b := (Qlt b a) (only parsing).
Notation Qge a b := (Qle b a) (only parsing).

Infix "==" := Qeq (at level 70, no associativity) : Q_scope.
Infix "<" := Qlt : Q_scope.
Infix "<=" := Qle : Q_scope.
Notation "x > y" := (Qlt y x)(only parsing) : Q_scope.
Notation "x >= y" := (Qle y x)(only parsing) : Q_scope.
Notation "x <= y <= z" := (x<=y/\y<=z) : Q_scope.



Lemma inject_Z_injective (a b: Z): inject_Z a == inject_Z b <-> a = b.
Proof. try hammer_hook "QArith_base" "QArith_base.inject_Z_injective".  
unfold Qeq. simpl. omega.
Qed.



Definition Qcompare (p q : Q) := (Qnum p * QDen q ?= Qnum q * QDen p)%Z.
Notation "p ?= q" := (Qcompare p q) : Q_scope.

Lemma Qeq_alt p q : (p == q) <-> (p ?= q) = Eq.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeq_alt".  
symmetry. apply Z.compare_eq_iff.
Qed.

Lemma Qlt_alt p q : (p<q) <-> (p?=q = Lt).
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_alt".  
reflexivity.
Qed.

Lemma Qgt_alt p q : (p>q) <-> (p?=q = Gt).
Proof. try hammer_hook "QArith_base" "QArith_base.Qgt_alt".  
symmetry. apply Z.gt_lt_iff.
Qed.

Lemma Qle_alt p q : (p<=q) <-> (p?=q <> Gt).
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_alt".  
reflexivity.
Qed.

Lemma Qge_alt p q : (p>=q) <-> (p?=q <> Lt).
Proof. try hammer_hook "QArith_base" "QArith_base.Qge_alt".  
symmetry. apply Z.ge_le_iff.
Qed.

Hint Unfold Qeq Qlt Qle : qarith.
Hint Extern 5 (?X1 <> ?X2) => intro; discriminate: qarith.

Lemma Qcompare_antisym x y : CompOpp (x ?= y) = (y ?= x).
Proof. try hammer_hook "QArith_base" "QArith_base.Qcompare_antisym".  
symmetry. apply Z.compare_antisym.
Qed.

Lemma Qcompare_spec x y : CompareSpec (x==y) (x<y) (y<x) (x ?= y).
Proof. try hammer_hook "QArith_base" "QArith_base.Qcompare_spec".  
unfold Qeq, Qlt, Qcompare. case Z.compare_spec; now constructor.
Qed.



Theorem Qeq_refl x : x == x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeq_refl".  
auto with qarith.
Qed.

Theorem Qeq_sym x y : x == y -> y == x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeq_sym".  
auto with qarith.
Qed.

Theorem Qeq_trans x y z : x == y -> y == z -> x == z.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeq_trans".  
unfold Qeq; intros XY YZ.
apply Z.mul_reg_r with (QDen y); [auto with qarith|].
now rewrite Z.mul_shuffle0, XY, Z.mul_shuffle0, YZ, Z.mul_shuffle0.
Qed.

Hint Immediate Qeq_sym : qarith.
Hint Resolve Qeq_refl Qeq_trans : qarith.



Instance Q_Setoid : Equivalence Qeq.
Proof. try hammer_hook "QArith_base" "QArith_base.Q_Setoid".   split; red; eauto with qarith. Qed.



Theorem Qeq_dec x y : {x==y} + {~ x==y}.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeq_dec".  
apply Z.eq_dec.
Defined.

Definition Qeq_bool x y :=
(Zeq_bool (Qnum x * QDen y) (Qnum y * QDen x))%Z.

Definition Qle_bool x y :=
(Z.leb (Qnum x * QDen y) (Qnum y * QDen x))%Z.

Lemma Qeq_bool_iff x y : Qeq_bool x y = true <-> x == y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeq_bool_iff".  
symmetry; apply Zeq_is_eq_bool.
Qed.

Lemma Qeq_bool_eq x y : Qeq_bool x y = true -> x == y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeq_bool_eq".  
apply Qeq_bool_iff.
Qed.

Lemma Qeq_eq_bool x y : x == y -> Qeq_bool x y = true.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeq_eq_bool".  
apply Qeq_bool_iff.
Qed.

Lemma Qeq_bool_neq x y : Qeq_bool x y = false -> ~ x == y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeq_bool_neq".  
rewrite <- Qeq_bool_iff. now intros ->.
Qed.

Lemma Qle_bool_iff x y : Qle_bool x y = true <-> x <= y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_bool_iff".  
symmetry; apply Zle_is_le_bool.
Qed.

Lemma Qle_bool_imp_le x y : Qle_bool x y = true -> x <= y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_bool_imp_le".  
apply Qle_bool_iff.
Qed.

Theorem Qnot_eq_sym x y : ~x == y -> ~y == x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qnot_eq_sym".  
auto with qarith.
Qed.

Hint Resolve Qnot_eq_sym : qarith.





Definition Qplus (x y : Q) :=
(Qnum x * QDen y + Qnum y * QDen x) # (Qden x * Qden y).

Definition Qmult (x y : Q) := (Qnum x * Qnum y) # (Qden x * Qden y).

Definition Qopp (x : Q) := (- Qnum x) # (Qden x).

Definition Qminus (x y : Q) := Qplus x (Qopp y).

Definition Qinv (x : Q) :=
match Qnum x with
| Z0 => 0
| Zpos p => (QDen x)#p
| Zneg p => (Zneg (Qden x))#p
end.

Definition Qdiv (x y : Q) := Qmult x (Qinv y).

Infix "+" := Qplus : Q_scope.
Notation "- x" := (Qopp x) : Q_scope.
Infix "-" := Qminus : Q_scope.
Infix "*" := Qmult : Q_scope.
Notation "/ x" := (Qinv x) : Q_scope.
Infix "/" := Qdiv : Q_scope.



Notation " ' x " := (Zpos x) (at level 20, no associativity) : Z_scope.

Lemma Qmake_Qdiv a b : a#b==inject_Z a/inject_Z ('b).
Proof. try hammer_hook "QArith_base" "QArith_base.Qmake_Qdiv".  
unfold Qeq. simpl. ring.
Qed.



Instance Qplus_comp : Proper (Qeq==>Qeq==>Qeq) Qplus.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_comp".  
unfold Qeq, Qplus; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
simpl_mult; ring_simplify.
replace (p1 * 'r2 * 'q2) with (p1 * 'q2 * 'r2) by ring.
rewrite H.
replace (r1 * 'p2 * 'q2 * 's2) with (r1 * 's2 * 'p2 * 'q2) by ring.
rewrite H0.
ring.
Close Scope Z_scope.
Qed.

Instance Qopp_comp : Proper (Qeq==>Qeq) Qopp.
Proof. try hammer_hook "QArith_base" "QArith_base.Qopp_comp".  
unfold Qeq, Qopp; simpl.
Open Scope Z_scope.
intros x y H; simpl.
replace (- Qnum x * ' Qden y) with (- (Qnum x * ' Qden y)) by ring.
rewrite H;  ring.
Close Scope Z_scope.
Qed.

Instance Qminus_comp : Proper (Qeq==>Qeq==>Qeq) Qminus.
Proof. try hammer_hook "QArith_base" "QArith_base.Qminus_comp".  
intros x x' Hx y y' Hy.
unfold Qminus. rewrite Hx, Hy; auto with qarith.
Qed.

Instance Qmult_comp : Proper (Qeq==>Qeq==>Qeq) Qmult.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_comp".  
unfold Qeq; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) H (r1, r2) (s1, s2) H0; simpl in *.
intros; simpl_mult; ring_simplify.
replace (q1 * s1 * 'p2) with (q1 * 'p2 * s1) by ring.
rewrite <- H.
replace (p1 * r1 * 'q2 * 's2) with (r1 * 's2 * p1 * 'q2) by ring.
rewrite H0.
ring.
Close Scope Z_scope.
Qed.

Instance Qinv_comp : Proper (Qeq==>Qeq) Qinv.
Proof. try hammer_hook "QArith_base" "QArith_base.Qinv_comp".  
unfold Qeq, Qinv; simpl.
Open Scope Z_scope.
intros (p1, p2) (q1, q2) EQ; simpl in *.
destruct q1; simpl in *.
- apply Z.mul_eq_0 in EQ. destruct EQ; now subst.
- destruct p1; simpl in *; try discriminate.
now rewrite Pos.mul_comm, <- EQ, Pos.mul_comm.
- destruct p1; simpl in *; try discriminate.
now rewrite Pos.mul_comm, <- EQ, Pos.mul_comm.
Close Scope Z_scope.
Qed.

Instance Qdiv_comp : Proper (Qeq==>Qeq==>Qeq) Qdiv.
Proof. try hammer_hook "QArith_base" "QArith_base.Qdiv_comp".  
intros x x' Hx y y' Hy; unfold Qdiv.
rewrite Hx, Hy; auto with qarith.
Qed.

Instance Qcompare_comp : Proper (Qeq==>Qeq==>eq) Qcompare.
Proof. try hammer_hook "QArith_base" "QArith_base.Qcompare_comp".  
unfold Qeq, Qcompare.
Open Scope Z_scope.
intros (p1,p2) (q1,q2) H (r1,r2) (s1,s2) H'; simpl in *.
rewrite <- (Zcompare_mult_compat (q2*s2) (p1*'r2)).
rewrite <- (Zcompare_mult_compat (p2*r2) (q1*'s2)).
change ('(q2*s2)) with ('q2 * 's2).
change ('(p2*r2)) with ('p2 * 'r2).
replace ('q2 * 's2 * (p1*'r2)) with ((p1*'q2)*'r2*'s2) by ring.
rewrite H.
replace ('q2 * 's2 * (r1*'p2)) with ((r1*'s2)*'q2*'p2) by ring.
rewrite H'.
f_equal; ring.
Close Scope Z_scope.
Qed.

Instance Qle_comp : Proper (Qeq==>Qeq==>iff) Qle.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_comp".  
intros p q H r s H'. rewrite 2 Qle_alt, H, H'; auto with *.
Qed.

Instance Qlt_compat : Proper (Qeq==>Qeq==>iff) Qlt.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_compat".  
intros p q H r s H'. rewrite 2 Qlt_alt, H, H'; auto with *.
Qed.

Instance Qeqb_comp : Proper (Qeq==>Qeq==>eq) Qeq_bool.
Proof. try hammer_hook "QArith_base" "QArith_base.Qeqb_comp".  
intros p q H r s H'; apply eq_true_iff_eq.
rewrite 2 Qeq_bool_iff, H, H'; split; auto with qarith.
Qed.

Instance Qleb_comp : Proper (Qeq==>Qeq==>eq) Qle_bool.
Proof. try hammer_hook "QArith_base" "QArith_base.Qleb_comp".  
intros p q H r s H'; apply eq_true_iff_eq.
rewrite 2 Qle_bool_iff, H, H'; split; auto with qarith.
Qed.




Lemma Q_apart_0_1 : ~ 1 == 0.
Proof. try hammer_hook "QArith_base" "QArith_base.Q_apart_0_1".  
unfold Qeq; auto with qarith.
Qed.





Theorem Qplus_assoc : forall x y z, x+(y+z)==(x+y)+z.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_assoc".  
intros (x1, x2) (y1, y2) (z1, z2).
unfold Qeq, Qplus; simpl; simpl_mult; ring.
Qed.



Lemma Qplus_0_l : forall x, 0+x == x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_0_l".  
intros (x1, x2); unfold Qeq, Qplus; simpl; ring.
Qed.

Lemma Qplus_0_r : forall x, x+0 == x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_0_r".  
intros (x1, x2); unfold Qeq, Qplus; simpl.
rewrite Pos.mul_comm; simpl; ring.
Qed.



Theorem Qplus_comm : forall x y, x+y == y+x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_comm".  
intros (x1, x2); unfold Qeq, Qplus; simpl.
intros; rewrite Pos.mul_comm; ring.
Qed.




Lemma Qopp_involutive : forall q, - -q == q.
Proof. try hammer_hook "QArith_base" "QArith_base.Qopp_involutive".  
red; simpl; intros; ring.
Qed.

Theorem Qplus_opp_r : forall q, q+(-q) == 0.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_opp_r".  
red; simpl; intro; ring.
Qed.



Lemma Qplus_inj_r (x y z: Q):
x + z == y + z <-> x == y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_inj_r".  
split; intro E.
rewrite <- (Qplus_0_r x), <- (Qplus_0_r y).
rewrite <- (Qplus_opp_r z); auto.
do 2 rewrite Qplus_assoc.
rewrite E. reflexivity.
rewrite E. reflexivity.
Qed.

Lemma Qplus_inj_l (x y z: Q):
z + x == z + y <-> x == y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_inj_l".  
rewrite (Qplus_comm z x), (Qplus_comm z y).
apply Qplus_inj_r.
Qed.






Theorem Qmult_assoc : forall n m p, n*(m*p)==(n*m)*p.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_assoc".  
intros; red; simpl; rewrite Pos.mul_assoc; ring.
Qed.



Lemma Qmult_0_l : forall x , 0*x == 0.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_0_l".  
intros; compute; reflexivity.
Qed.

Lemma Qmult_0_r : forall x , x*0 == 0.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_0_r".  
intros; red; simpl; ring.
Qed.



Lemma Qmult_1_l : forall n, 1*n == n.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_1_l".  
intro; red; simpl; destruct (Qnum n); auto.
Qed.

Theorem Qmult_1_r : forall n, n*1==n.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_1_r".  
intro; red; simpl.
rewrite Z.mul_1_r with (n := Qnum n).
rewrite Pos.mul_comm; simpl; trivial.
Qed.



Theorem Qmult_comm : forall x y, x*y==y*x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_comm".  
intros; red; simpl; rewrite Pos.mul_comm; ring.
Qed.



Theorem Qmult_plus_distr_r : forall x y z, x*(y+z)==(x*y)+(x*z).
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_plus_distr_r".  
intros (x1, x2) (y1, y2) (z1, z2).
unfold Qeq, Qmult, Qplus; simpl; simpl_mult; ring.
Qed.

Theorem Qmult_plus_distr_l : forall x y z, (x+y)*z==(x*z)+(y*z).
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_plus_distr_l".  
intros (x1, x2) (y1, y2) (z1, z2).
unfold Qeq, Qmult, Qplus; simpl; simpl_mult; ring.
Qed.



Theorem Qmult_integral : forall x y, x*y==0 -> x==0 \/ y==0.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_integral".  
intros (x1,x2) (y1,y2).
unfold Qeq, Qmult; simpl.
now rewrite <- Z.mul_eq_0, !Z.mul_1_r.
Qed.

Theorem Qmult_integral_l : forall x y, ~ x == 0 -> x*y == 0 -> y == 0.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_integral_l".  
intros (x1, x2) (y1, y2).
unfold Qeq, Qmult; simpl.
rewrite !Z.mul_1_r, Z.mul_eq_0. intuition.
Qed.




Lemma inject_Z_plus (x y: Z): inject_Z (x + y) = inject_Z x + inject_Z y.
Proof. try hammer_hook "QArith_base" "QArith_base.inject_Z_plus".  
unfold Qplus, inject_Z. simpl. f_equal. ring.
Qed.

Lemma inject_Z_mult (x y: Z): inject_Z (x * y) = inject_Z x * inject_Z y.
Proof. try hammer_hook "QArith_base" "QArith_base.inject_Z_mult".   reflexivity. Qed.

Lemma inject_Z_opp (x: Z): inject_Z (- x) = - inject_Z x.
Proof. try hammer_hook "QArith_base" "QArith_base.inject_Z_opp".   reflexivity. Qed.




Lemma Qinv_involutive : forall q, (/ / q) == q.
Proof. try hammer_hook "QArith_base" "QArith_base.Qinv_involutive".  
intros [[|n|n] d]; red; simpl; reflexivity.
Qed.

Theorem Qmult_inv_r : forall x, ~ x == 0 -> x*(/x) == 1.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_inv_r".  
intros (x1, x2); unfold Qeq, Qdiv, Qmult; case x1; simpl;
intros; simpl_mult; try ring.
elim H; auto.
Qed.

Lemma Qinv_mult_distr : forall p q, / (p * q) == /p * /q.
Proof. try hammer_hook "QArith_base" "QArith_base.Qinv_mult_distr".  
intros (x1,x2) (y1,y2); unfold Qeq, Qinv, Qmult; simpl.
destruct x1; simpl; auto;
destruct y1; simpl; auto.
Qed.

Theorem Qdiv_mult_l : forall x y, ~ y == 0 -> (x*y)/y == x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qdiv_mult_l".  
intros; unfold Qdiv.
rewrite <- (Qmult_assoc x y (Qinv y)).
rewrite (Qmult_inv_r y H).
apply Qmult_1_r.
Qed.

Theorem Qmult_div_r : forall x y, ~ y == 0 -> y*(x/y) == x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_div_r".  
intros; unfold Qdiv.
rewrite (Qmult_assoc y x (Qinv y)).
rewrite (Qmult_comm y x).
fold (Qdiv (Qmult x y) y).
apply Qdiv_mult_l; auto.
Qed.



Lemma Qmult_inj_r (x y z: Q): ~ z == 0 -> (x * z == y * z <-> x == y).
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_inj_r".  
intro z_ne_0.
split; intro E.
rewrite <- (Qmult_1_r x), <- (Qmult_1_r y).
rewrite <- (Qmult_inv_r z); auto.
do 2 rewrite Qmult_assoc.
rewrite E. reflexivity.
rewrite E. reflexivity.
Qed.

Lemma Qmult_inj_l (x y z: Q): ~ z == 0 -> (z * x == z * y <-> x == y).
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_inj_l".  
rewrite (Qmult_comm z x), (Qmult_comm z y).
apply Qmult_inj_r.
Qed.



Lemma Qle_refl x : x<=x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_refl".  
unfold Qle; auto with zarith.
Qed.

Lemma Qle_antisym x y : x<=y -> y<=x -> x==y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_antisym".  
unfold Qle, Qeq; auto with zarith.
Qed.

Lemma Qle_trans : forall x y z, x<=y -> y<=z -> x<=z.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_trans".  
unfold Qle; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
Open Scope Z_scope.
apply Z.mul_le_mono_pos_r with ('y2); [easy|].
apply Z.le_trans with (y1 * 'x2 * 'z2).
- rewrite Z.mul_shuffle0. now apply Z.mul_le_mono_pos_r.
- rewrite Z.mul_shuffle0, (Z.mul_shuffle0 z1).
now apply Z.mul_le_mono_pos_r.
Close Scope Z_scope.
Qed.

Hint Resolve Qle_trans : qarith.

Lemma Qlt_irrefl x : ~x<x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_irrefl".  
unfold Qlt. auto with zarith.
Qed.

Lemma Qlt_not_eq x y : x<y -> ~ x==y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_not_eq".  
unfold Qlt, Qeq; auto with zarith.
Qed.

Lemma Zle_Qle (x y: Z): (x <= y)%Z = (inject_Z x <= inject_Z y).
Proof. try hammer_hook "QArith_base" "QArith_base.Zle_Qle".  
unfold Qle. simpl. now rewrite !Z.mul_1_r.
Qed.

Lemma Zlt_Qlt (x y: Z): (x < y)%Z = (inject_Z x < inject_Z y).
Proof. try hammer_hook "QArith_base" "QArith_base.Zlt_Qlt".  
unfold Qlt. simpl. now rewrite !Z.mul_1_r.
Qed.




Lemma Qle_lteq x y : x<=y <-> x<y \/ x==y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_lteq".  
rewrite Qeq_alt, Qle_alt, Qlt_alt.
destruct (x ?= y); intuition; discriminate.
Qed.

Lemma Qlt_le_weak x y : x<y -> x<=y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_le_weak".  
unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qle_lt_trans : forall x y z, x<=y -> y<z -> x<z.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_lt_trans".  
unfold Qle, Qlt; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
Open Scope Z_scope.
apply Z.mul_lt_mono_pos_r with ('y2); [easy|].
apply Z.le_lt_trans with (y1 * 'x2 * 'z2).
- rewrite Z.mul_shuffle0. now apply Z.mul_le_mono_pos_r.
- rewrite Z.mul_shuffle0, (Z.mul_shuffle0 z1).
now apply Z.mul_lt_mono_pos_r.
Close Scope Z_scope.
Qed.

Lemma Qlt_le_trans : forall x y z, x<y -> y<=z -> x<z.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_le_trans".  
unfold Qle, Qlt; intros (x1, x2) (y1, y2) (z1, z2); simpl; intros.
Open Scope Z_scope.
apply Z.mul_lt_mono_pos_r with ('y2); [easy|].
apply Z.lt_le_trans with (y1 * 'x2 * 'z2).
- rewrite Z.mul_shuffle0. now apply Z.mul_lt_mono_pos_r.
- rewrite Z.mul_shuffle0, (Z.mul_shuffle0 z1).
now apply Z.mul_le_mono_pos_r.
Close Scope Z_scope.
Qed.

Lemma Qlt_trans : forall x y z, x<y -> y<z -> x<z.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_trans".  
intros.
apply Qle_lt_trans with y; auto.
apply Qlt_le_weak; auto.
Qed.



Lemma Qnot_lt_le : forall x y, ~ x<y -> y<=x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qnot_lt_le".  
unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qnot_le_lt : forall x y, ~ x<=y -> y<x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qnot_le_lt".  
unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qlt_not_le : forall x y, x<y -> ~ y<=x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_not_le".  
unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qle_not_lt : forall x y, x<=y -> ~ y<x.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_not_lt".  
unfold Qle, Qlt; auto with zarith.
Qed.

Lemma Qle_lt_or_eq : forall x y, x<=y -> x<y \/ x==y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_lt_or_eq".  
unfold Qle, Qlt, Qeq; intros; now apply Z.lt_eq_cases.
Qed.

Hint Resolve Qle_not_lt Qlt_not_le Qnot_le_lt Qnot_lt_le
Qlt_le_weak Qlt_not_eq Qle_antisym Qle_refl: qarith.



Lemma Q_dec : forall x y, {x<y} + {y<x} + {x==y}.
Proof. try hammer_hook "QArith_base" "QArith_base.Q_dec".  
unfold Qlt, Qle, Qeq; intros.
exact (Z_dec' (Qnum x * QDen y) (Qnum y * QDen x)).
Defined.

Lemma Qlt_le_dec : forall x y, {x<y} + {y<=x}.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_le_dec".  
unfold Qlt, Qle; intros.
exact (Z_lt_le_dec (Qnum x * QDen y) (Qnum y * QDen x)).
Defined.



Lemma Qopp_le_compat : forall p q, p<=q -> -q <= -p.
Proof. try hammer_hook "QArith_base" "QArith_base.Qopp_le_compat".  
intros (a1,a2) (b1,b2); unfold Qle, Qlt; simpl.
rewrite !Z.mul_opp_l. omega.
Qed.

Hint Resolve Qopp_le_compat : qarith.

Lemma Qle_minus_iff : forall p q, p <= q <-> 0 <= q+-p.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_minus_iff".  
intros (x1,x2) (y1,y2); unfold Qle; simpl.
rewrite Z.mul_opp_l. omega.
Qed.

Lemma Qlt_minus_iff : forall p q, p < q <-> 0 < q+-p.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_minus_iff".  
intros (x1,x2) (y1,y2); unfold Qlt; simpl.
rewrite Z.mul_opp_l. omega.
Qed.

Lemma Qplus_le_compat :
forall x y z t, x<=y -> z<=t -> x+z <= y+t.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_le_compat".  
unfold Qplus, Qle; intros (x1, x2) (y1, y2) (z1, z2) (t1, t2);
simpl; simpl_mult.
Open Scope Z_scope.
intros.
match goal with |- ?a <= ?b => ring_simplify a b end.
rewrite Z.add_comm.
apply Z.add_le_mono.
match goal with |- ?a <= ?b => ring_simplify z1 t1 ('z2) ('t2) a b end.
auto with zarith.
match goal with |- ?a <= ?b => ring_simplify x1 y1 ('x2) ('y2) a b end.
auto with zarith.
Close Scope Z_scope.
Qed.

Lemma Qplus_lt_le_compat :
forall x y z t, x<y -> z<=t -> x+z < y+t.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_lt_le_compat".  
unfold Qplus, Qle, Qlt; intros (x1, x2) (y1, y2) (z1, z2) (t1, t2);
simpl; simpl_mult.
Open Scope Z_scope.
intros.
match goal with |- ?a < ?b => ring_simplify a b end.
rewrite Z.add_comm.
apply Z.add_le_lt_mono.
match goal with |- ?a <= ?b => ring_simplify z1 t1 ('z2) ('t2) a b end.
auto with zarith.
match goal with |- ?a < ?b => ring_simplify x1 y1 ('x2) ('y2) a b end.
do 2 (apply Z.mul_lt_mono_pos_r;try easy).
Close Scope Z_scope.
Qed.

Lemma Qplus_le_l (x y z: Q): x + z <= y + z <-> x <= y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_le_l".  
split; intros.
rewrite <- (Qplus_0_r x), <- (Qplus_0_r y), <- (Qplus_opp_r z).
do 2 rewrite Qplus_assoc.
apply Qplus_le_compat; auto with *.
apply Qplus_le_compat; auto with *.
Qed.

Lemma Qplus_le_r (x y z: Q): z + x <= z + y <-> x <= y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_le_r".  
rewrite (Qplus_comm z x), (Qplus_comm z y).
apply Qplus_le_l.
Qed.

Lemma Qplus_lt_l (x y z: Q): x + z < y + z <-> x < y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_lt_l".  
split; intros.
rewrite <- (Qplus_0_r x), <- (Qplus_0_r y), <- (Qplus_opp_r z).
do 2 rewrite Qplus_assoc.
apply Qplus_lt_le_compat; auto with *.
apply Qplus_lt_le_compat; auto with *.
Qed.

Lemma Qplus_lt_r (x y z: Q): z + x < z + y <-> x < y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qplus_lt_r".  
rewrite (Qplus_comm z x), (Qplus_comm z y).
apply Qplus_lt_l.
Qed.

Lemma Qmult_le_compat_r : forall x y z, x <= y -> 0 <= z -> x*z <= y*z.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_le_compat_r".  
intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
Open Scope Z_scope.
intros; simpl_mult.
rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b1).
apply Z.mul_le_mono_nonneg_r; auto with zarith.
Close Scope Z_scope.
Qed.

Lemma Qmult_lt_0_le_reg_r : forall x y z, 0 < z  -> x*z <= y*z -> x <= y.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_lt_0_le_reg_r".  
intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
Open Scope Z_scope.
simpl_mult.
rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b1).
intros LT LE.
apply Z.mul_le_mono_pos_r in LE; trivial.
apply Z.mul_pos_pos; [omega|easy].
Close Scope Z_scope.
Qed.

Lemma Qmult_le_r (x y z: Q): 0 < z -> (x*z <= y*z <-> x <= y).
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_le_r".  
split; intro.
now apply Qmult_lt_0_le_reg_r with z.
apply Qmult_le_compat_r; auto with qarith.
Qed.

Lemma Qmult_le_l (x y z: Q): 0 < z -> (z*x <= z*y <-> x <= y).
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_le_l".  
rewrite (Qmult_comm z x), (Qmult_comm z y).
apply Qmult_le_r.
Qed.

Lemma Qmult_lt_compat_r : forall x y z, 0 < z  -> x < y -> x*z < y*z.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_lt_compat_r".  
intros (a1,a2) (b1,b2) (c1,c2); unfold Qle, Qlt; simpl.
Open Scope Z_scope.
intros; simpl_mult.
rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b1).
apply Z.mul_lt_mono_pos_r; auto with zarith.
apply Z.mul_pos_pos; [omega|reflexivity].
Close Scope Z_scope.
Qed.

Lemma Qmult_lt_r: forall x y z, 0 < z -> (x*z < y*z <-> x < y).
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_lt_r".  
Open Scope Z_scope.
intros (a1,a2) (b1,b2) (c1,c2).
unfold Qle, Qlt; simpl.
simpl_mult.
rewrite Z.mul_shuffle1, (Z.mul_shuffle1 b1).
intro LT. rewrite <- Z.mul_lt_mono_pos_r. reflexivity.
apply Z.mul_pos_pos; [omega|reflexivity].
Close Scope Z_scope.
Qed.

Lemma Qmult_lt_l (x y z: Q): 0 < z -> (z*x < z*y <-> x < y).
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_lt_l".  
rewrite (Qmult_comm z x), (Qmult_comm z y).
apply Qmult_lt_r.
Qed.

Lemma Qmult_le_0_compat : forall a b, 0 <= a -> 0 <= b -> 0 <= a*b.
Proof. try hammer_hook "QArith_base" "QArith_base.Qmult_le_0_compat".  
intros a b Ha Hb.
unfold Qle in *.
simpl in *.
auto with *.
Qed.

Lemma Qinv_le_0_compat : forall a, 0 <= a -> 0 <= /a.
Proof. try hammer_hook "QArith_base" "QArith_base.Qinv_le_0_compat".  
intros [[|n|n] d] Ha; assumption.
Qed.

Lemma Qle_shift_div_l : forall a b c,
0 < c -> a*c <= b -> a <= b/c.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_shift_div_l".  
intros a b c Hc H.
apply Qmult_lt_0_le_reg_r with (c).
assumption.
setoid_replace (b/c*c) with (c*(b/c)) by apply Qmult_comm.
rewrite Qmult_div_r; try assumption.
auto with *.
Qed.

Lemma Qle_shift_inv_l : forall a c,
0 < c -> a*c <= 1 -> a <= /c.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_shift_inv_l".  
intros a c Hc H.
setoid_replace (/c) with (1*/c) by (symmetry; apply Qmult_1_l).
change (a <= 1/c).
apply Qle_shift_div_l; assumption.
Qed.

Lemma Qle_shift_div_r : forall a b c,
0 < b -> a <= c*b -> a/b <= c.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_shift_div_r".  
intros a b c Hc H.
apply Qmult_lt_0_le_reg_r with b.
assumption.
setoid_replace (a/b*b) with (b*(a/b)) by apply Qmult_comm.
rewrite Qmult_div_r; try assumption.
auto with *.
Qed.

Lemma Qle_shift_inv_r : forall b c,
0 < b -> 1 <= c*b -> /b <= c.
Proof. try hammer_hook "QArith_base" "QArith_base.Qle_shift_inv_r".  
intros b c Hc H.
setoid_replace (/b) with (1*/b) by (symmetry; apply Qmult_1_l).
change (1/b <= c).
apply Qle_shift_div_r; assumption.
Qed.

Lemma Qinv_lt_0_compat : forall a, 0 < a -> 0 < /a.
Proof. try hammer_hook "QArith_base" "QArith_base.Qinv_lt_0_compat".  
intros [[|n|n] d] Ha; assumption.
Qed.

Lemma Qlt_shift_div_l : forall a b c,
0 < c -> a*c < b -> a < b/c.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_shift_div_l".  
intros a b c Hc H.
apply Qnot_le_lt.
intros H0.
apply (Qlt_not_le _ _ H).
apply Qmult_lt_0_le_reg_r with (/c).
apply Qinv_lt_0_compat.
assumption.
setoid_replace (a*c/c) with (a) by (apply Qdiv_mult_l; auto with *).
assumption.
Qed.

Lemma Qlt_shift_inv_l : forall a c,
0 < c -> a*c < 1 -> a < /c.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_shift_inv_l".  
intros a c Hc H.
setoid_replace (/c) with (1*/c) by (symmetry; apply Qmult_1_l).
change (a < 1/c).
apply Qlt_shift_div_l; assumption.
Qed.

Lemma Qlt_shift_div_r : forall a b c,
0 < b -> a < c*b -> a/b < c.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_shift_div_r".  
intros a b c Hc H.
apply Qnot_le_lt.
intros H0.
apply (Qlt_not_le _ _ H).
apply Qmult_lt_0_le_reg_r with (/b).
apply Qinv_lt_0_compat.
assumption.
setoid_replace (c*b/b) with (c) by (apply Qdiv_mult_l; auto with *).
assumption.
Qed.

Lemma Qlt_shift_inv_r : forall b c,
0 < b -> 1 < c*b -> /b < c.
Proof. try hammer_hook "QArith_base" "QArith_base.Qlt_shift_inv_r".  
intros b c Hc H.
setoid_replace (/b) with (1*/b) by (symmetry; apply Qmult_1_l).
change (1/b < c).
apply Qlt_shift_div_r; assumption.
Qed.



Definition Qpower_positive : Q -> positive -> Q :=
pow_pos Qmult.

Instance Qpower_positive_comp : Proper (Qeq==>eq==>Qeq) Qpower_positive.
Proof. try hammer_hook "QArith_base" "QArith_base.Qpower_positive_comp".  
intros x x' Hx y y' Hy. rewrite <-Hy; clear y' Hy.
unfold Qpower_positive.
induction y; simpl;
try rewrite IHy;
try rewrite Hx;
reflexivity.
Qed.

Definition Qpower (q:Q) (z:Z) :=
match z with
| Zpos p => Qpower_positive q p
| Z0 => 1
| Zneg p => /Qpower_positive q p
end.

Notation " q ^ z " := (Qpower q z) : Q_scope.

Instance Qpower_comp : Proper (Qeq==>eq==>Qeq) Qpower.
Proof. try hammer_hook "QArith_base" "QArith_base.Qpower_comp".  
intros x x' Hx y y' Hy. rewrite <- Hy; clear y' Hy.
destruct y; simpl; rewrite ?Hx; auto with *.
Qed.
