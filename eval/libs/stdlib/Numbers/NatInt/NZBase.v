From Hammer Require Import Hammer.











Require Import NZAxioms.

Module Type NZBaseProp (Import NZ : NZDomainSig').

Include BackportEq NZ NZ.

Lemma eq_sym_iff : forall x y, x==y <-> y==x.
Proof. hammer_hook "NZBase" "NZBase.NZBaseProp.eq_sym_iff".  
intros; split; symmetry; auto.
Qed.



Theorem neq_sym : forall n m, n ~= m -> m ~= n.
Proof. hammer_hook "NZBase" "NZBase.NZBaseProp.neq_sym".  
intros n m H1 H2; symmetry in H2; false_hyp H2 H1.
Qed.

Theorem eq_stepl : forall x y z, x == y -> x == z -> z == y.
Proof. hammer_hook "NZBase" "NZBase.NZBaseProp.eq_stepl".  
intros x y z H1 H2; now rewrite <- H1.
Qed.

Declare Left Step eq_stepl.

Declare Right Step (@Equivalence_Transitive _ _ eq_equiv).

Theorem succ_inj : forall n1 n2, S n1 == S n2 -> n1 == n2.
Proof. hammer_hook "NZBase" "NZBase.NZBaseProp.succ_inj".  
intros n1 n2 H.
apply pred_wd in H. now do 2 rewrite pred_succ in H.
Qed.


Theorem succ_inj_wd : forall n1 n2, S n1 == S n2 <-> n1 == n2.
Proof. hammer_hook "NZBase" "NZBase.NZBaseProp.succ_inj_wd".  
intros; split.
apply succ_inj.
intros. now f_equiv.
Qed.

Theorem succ_inj_wd_neg : forall n m, S n ~= S m <-> n ~= m.
Proof. hammer_hook "NZBase" "NZBase.NZBaseProp.succ_inj_wd_neg".  
intros; now rewrite succ_inj_wd.
Qed.



Section CentralInduction.

Variable A : t -> Prop.
Hypothesis A_wd : Proper (eq==>iff) A.

Theorem central_induction :
forall z, A z ->
(forall n, A n <-> A (S n)) ->
forall n, A n.
Proof. hammer_hook "NZBase" "NZBase.NZBaseProp.central_induction".  
intros z Base Step; revert Base; pattern z; apply bi_induction.
solve_proper.
intro; now apply bi_induction.
intro; pose proof (Step n); tauto.
Qed.

End CentralInduction.

Tactic Notation "nzinduct" ident(n) :=
induction_maker n ltac:(apply bi_induction).

Tactic Notation "nzinduct" ident(n) constr(u) :=
induction_maker n ltac:(apply central_induction with (z := u)).

End NZBaseProp.

