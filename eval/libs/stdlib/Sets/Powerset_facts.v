From Hammer Require Import Hammer.



























Require Export Ensembles.
Require Export Constructive_sets.
Require Export Relations_1.
Require Export Relations_1_facts.
Require Export Partial_Order.
Require Export Cpo.
Require Export Powerset.

Section Sets_as_an_algebra.
Variable U : Type.

Theorem Empty_set_zero : forall X:Ensemble U, Union U (Empty_set U) X = X.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Empty_set_zero".  
auto 6 with sets.
Qed.

Theorem Empty_set_zero' : forall x:U, Add U (Empty_set U) x = Singleton U x.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Empty_set_zero'".  
unfold Add at 1; auto using Empty_set_zero with sets.
Qed.

Lemma less_than_empty :
forall X:Ensemble U, Included U X (Empty_set U) -> X = Empty_set U.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.less_than_empty".  
auto with sets.
Qed.

Theorem Union_commutative : forall A B:Ensemble U, Union U A B = Union U B A.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Union_commutative".  
auto with sets.
Qed.

Theorem Union_associative :
forall A B C:Ensemble U, Union U (Union U A B) C = Union U A (Union U B C).
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Union_associative".  
auto 9 with sets.
Qed.

Theorem Union_idempotent : forall A:Ensemble U, Union U A A = A.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Union_idempotent".  
auto 7 with sets.
Qed.

Lemma Union_absorbs :
forall A B:Ensemble U, Included U B A -> Union U A B = A.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Union_absorbs".  
auto 7 with sets.
Qed.

Theorem Couple_as_union :
forall x y:U, Union U (Singleton U x) (Singleton U y) = Couple U x y.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Couple_as_union".  
intros x y; apply Extensionality_Ensembles; split; red.
intros x0 H'; elim H'; (intros x1 H'0; elim H'0; auto with sets).
intros x0 H'; elim H'; auto with sets.
Qed.

Theorem Triple_as_union :
forall x y z:U,
Union U (Union U (Singleton U x) (Singleton U y)) (Singleton U z) =
Triple U x y z.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Triple_as_union".  
intros x y z; apply Extensionality_Ensembles; split; red.
intros x0 H'; elim H'.
intros x1 H'0; elim H'0; (intros x2 H'1; elim H'1; auto with sets).
intros x1 H'0; elim H'0; auto with sets.
intros x0 H'; elim H'; auto with sets.
Qed.

Theorem Triple_as_Couple : forall x y:U, Couple U x y = Triple U x x y.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Triple_as_Couple".  
intros x y.
rewrite <- (Couple_as_union x y).
rewrite <- (Union_idempotent (Singleton U x)).
apply Triple_as_union.
Qed.

Theorem Triple_as_Couple_Singleton :
forall x y z:U, Triple U x y z = Union U (Couple U x y) (Singleton U z).
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Triple_as_Couple_Singleton".  
intros x y z.
rewrite <- (Triple_as_union x y z).
rewrite <- (Couple_as_union x y); auto with sets.
Qed.

Theorem Intersection_commutative :
forall A B:Ensemble U, Intersection U A B = Intersection U B A.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Intersection_commutative".  
intros A B.
apply Extensionality_Ensembles.
split; red; intros x H'; elim H'; auto with sets.
Qed.

Theorem Distributivity :
forall A B C:Ensemble U,
Intersection U A (Union U B C) =
Union U (Intersection U A B) (Intersection U A C).
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Distributivity".  
intros A B C.
apply Extensionality_Ensembles.
split; red; intros x H'.
elim H'.
intros x0 H'0 H'1; generalize H'0.
elim H'1; auto with sets.
elim H'; intros x0 H'0; elim H'0; auto with sets.
Qed.

Theorem Distributivity' :
forall A B C:Ensemble U,
Union U A (Intersection U B C) =
Intersection U (Union U A B) (Union U A C).
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Distributivity'".  
intros A B C.
apply Extensionality_Ensembles.
split; red; intros x H'.
elim H'; auto with sets.
intros x0 H'0; elim H'0; auto with sets.
elim H'.
intros x0 H'0; elim H'0; auto with sets.
intros x1 H'1 H'2; try exact H'2.
generalize H'1.
elim H'2; auto with sets.
Qed.

Theorem Union_add :
forall (A B:Ensemble U) (x:U), Add U (Union U A B) x = Union U A (Add U B x).
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Union_add".  
unfold Add; auto using Union_associative with sets.
Qed.

Theorem Non_disjoint_union :
forall (X:Ensemble U) (x:U), In U X x -> Add U X x = X.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Non_disjoint_union".  
intros X x H'; unfold Add.
apply Extensionality_Ensembles; red.
split; red; auto with sets.
intros x0 H'0; elim H'0; auto with sets.
intros t H'1; elim H'1; auto with sets.
Qed.

Theorem Non_disjoint_union' :
forall (X:Ensemble U) (x:U), ~ In U X x -> Subtract U X x = X.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Non_disjoint_union'".  
intros X x H'; unfold Subtract.
apply Extensionality_Ensembles.
split; red; auto with sets.
intros x0 H'0; elim H'0; auto with sets.
intros x0 H'0; apply Setminus_intro; auto with sets.
red; intro H'1; elim H'1.
lapply (Singleton_inv U x x0); auto with sets.
intro H'4; apply H'; rewrite H'4; auto with sets.
Qed.

Lemma singlx : forall x y:U, In U (Add U (Empty_set U) x) y -> x = y.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.singlx".  
intro x; rewrite (Empty_set_zero' x); auto with sets.
Qed.

Lemma incl_add :
forall (A B:Ensemble U) (x:U),
Included U A B -> Included U (Add U A x) (Add U B x).
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.incl_add".  
intros A B x H'; red; auto with sets.
intros x0 H'0.
lapply (Add_inv U A x x0); auto with sets.
intro H'1; elim H'1;
[ intro H'2; clear H'1 | intro H'2; rewrite <- H'2; clear H'1 ];
auto with sets.
Qed.

Lemma incl_add_x :
forall (A B:Ensemble U) (x:U),
~ In U A x -> Included U (Add U A x) (Add U B x) -> Included U A B.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.incl_add_x".  
unfold Included.
intros A B x H' H'0 x0 H'1.
lapply (H'0 x0); auto with sets.
intro H'2; lapply (Add_inv U B x x0); auto with sets.
intro H'3; elim H'3;
[ intro H'4; try exact H'4; clear H'3 | intro H'4; clear H'3 ].
absurd (In U A x0); auto with sets.
rewrite <- H'4; auto with sets.
Qed.

Lemma Add_commutative :
forall (A:Ensemble U) (x y:U), Add U (Add U A x) y = Add U (Add U A y) x.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Add_commutative".  
intros A x y.
unfold Add.
rewrite (Union_associative A (Singleton U x) (Singleton U y)).
rewrite (Union_commutative (Singleton U x) (Singleton U y)).
rewrite <- (Union_associative A (Singleton U y) (Singleton U x));
auto with sets.
Qed.

Lemma Add_commutative' :
forall (A:Ensemble U) (x y z:U),
Add U (Add U (Add U A x) y) z = Add U (Add U (Add U A z) x) y.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Add_commutative'".  
intros A x y z.
rewrite (Add_commutative (Add U A x) y z).
rewrite (Add_commutative A x z); auto with sets.
Qed.

Lemma Add_distributes :
forall (A B:Ensemble U) (x y:U),
Included U B A -> Add U (Add U A x) y = Union U (Add U A x) (Add U B y).
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.Add_distributes".  
intros A B x y H'; try assumption.
rewrite <- (Union_add (Add U A x) B y).
unfold Add at 4.
rewrite (Union_commutative A (Singleton U x)).
rewrite Union_associative.
rewrite (Union_absorbs A B H').
rewrite (Union_commutative (Singleton U x) A).
auto with sets.
Qed.

Lemma setcover_intro :
forall (U:Type) (A x y:Ensemble U),
Strict_Included U x y ->
~ (exists z : _, Strict_Included U x z /\ Strict_Included U z y) ->
covers (Ensemble U) (Power_set_PO U A) y x.
Proof. try hammer_hook "Powerset_facts" "Powerset_facts.setcover_intro".  
intros; apply Definition_of_covers; auto with sets.
Qed.

End Sets_as_an_algebra.

Hint Resolve Empty_set_zero Empty_set_zero' Union_associative Union_add
singlx incl_add: sets.

