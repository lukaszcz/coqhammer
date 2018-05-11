From Hammer Require Import Hammer.











Require Import NSub ZAxioms.
Require Export Ring.

Notation "s #1" := (fst s) (at level 9, format "s '#1'") : pair_scope.
Notation "s #2" := (snd s) (at level 9, format "s '#2'") : pair_scope.
Local Open Scope pair_scope.

Module ZPairsAxiomsMod (Import N : NAxiomsMiniSig) <: ZAxiomsMiniSig.
Module Import NProp.
Include NSubProp N.
End NProp.

Delimit Scope NScope with N.
Bind Scope NScope with N.t.
Infix "=="  := N.eq (at level 70) : NScope.
Notation "x ~= y" := (~ N.eq x y) (at level 70) : NScope.
Notation "0" := N.zero : NScope.
Notation "1" := N.one : NScope.
Notation "2" := N.two : NScope.
Infix "+" := N.add : NScope.
Infix "-" := N.sub : NScope.
Infix "*" := N.mul : NScope.
Infix "<" := N.lt : NScope.
Infix "<=" := N.le : NScope.
Local Open Scope NScope.



Module Z.

Definition t := (N.t * N.t)%type.
Definition zero : t := (0, 0).
Definition one : t := (1,0).
Definition two : t := (2,0).
Definition eq (p q : t) := (p#1 + q#2 == q#1 + p#2).
Definition succ (n : t) : t := (N.succ n#1, n#2).
Definition pred (n : t) : t := (n#1, N.succ n#2).
Definition opp (n : t) : t := (n#2, n#1).
Definition add (n m : t) : t := (n#1 + m#1, n#2 + m#2).
Definition sub (n m : t) : t := (n#1 + m#2, n#2 + m#1).
Definition mul (n m : t) : t :=
(n#1 * m#1 + n#2 * m#2, n#1 * m#2 + n#2 * m#1).
Definition lt (n m : t) := n#1 + m#2 < m#1 + n#2.
Definition le (n m : t) := n#1 + m#2 <= m#1 + n#2.
Definition min (n m : t) : t := (min (n#1 + m#2) (m#1 + n#2), n#2 + m#2).
Definition max (n m : t) : t := (max (n#1 + m#2) (m#1 + n#2), n#2 + m#2).





End Z.

Delimit Scope ZScope with Z.
Bind Scope ZScope with Z.t.
Infix "=="  := Z.eq (at level 70) : ZScope.
Notation "x ~= y" := (~ Z.eq x y) (at level 70) : ZScope.
Notation "0" := Z.zero : ZScope.
Notation "1" := Z.one : ZScope.
Notation "2" := Z.two : ZScope.
Infix "+" := Z.add : ZScope.
Infix "-" := Z.sub : ZScope.
Infix "*" := Z.mul : ZScope.
Notation "- x" := (Z.opp x) : ZScope.
Infix "<" := Z.lt : ZScope.
Infix "<=" := Z.le : ZScope.
Local Open Scope ZScope.

Lemma sub_add_opp : forall n m, Z.sub n m = Z.add n (Z.opp m).
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.sub_add_opp".   reflexivity. Qed.

Instance eq_equiv : Equivalence Z.eq.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.eq_equiv".  
split.
unfold Reflexive, Z.eq. reflexivity.
unfold Symmetric, Z.eq; now symmetry.
unfold Transitive, Z.eq. intros (n1,n2) (m1,m2) (p1,p2) H1 H2; simpl in *.
apply (add_cancel_r _ _ (m1+m2)%N).
rewrite add_shuffle2, H1, add_shuffle1, H2.
now rewrite add_shuffle1, (add_comm m1).
Qed.

Instance pair_wd : Proper (N.eq==>N.eq==>Z.eq) (@pair N.t N.t).
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.pair_wd".  
intros n1 n2 H1 m1 m2 H2; unfold Z.eq; simpl; now rewrite H1, H2.
Qed.

Instance succ_wd : Proper (Z.eq ==> Z.eq) Z.succ.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.succ_wd".  
unfold Z.succ, Z.eq; intros n m H; simpl.
do 2 rewrite add_succ_l; now rewrite H.
Qed.

Instance pred_wd : Proper (Z.eq ==> Z.eq) Z.pred.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.pred_wd".  
unfold Z.pred, Z.eq; intros n m H; simpl.
do 2 rewrite add_succ_r; now rewrite H.
Qed.

Instance add_wd : Proper (Z.eq ==> Z.eq ==> Z.eq) Z.add.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.add_wd".  
unfold Z.eq, Z.add; intros n1 m1 H1 n2 m2 H2; simpl.
now rewrite add_shuffle1, H1, H2, add_shuffle1.
Qed.

Instance opp_wd : Proper (Z.eq ==> Z.eq) Z.opp.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.opp_wd".  
unfold Z.eq, Z.opp; intros (n1,n2) (m1,m2) H; simpl in *.
now rewrite (add_comm n2), (add_comm m2).
Qed.

Instance sub_wd : Proper (Z.eq ==> Z.eq ==> Z.eq) Z.sub.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.sub_wd".  
intros n1 m1 H1 n2 m2 H2. rewrite 2 sub_add_opp. now do 2 f_equiv.
Qed.

Lemma mul_comm : forall n m, n*m == m*n.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.mul_comm".  
intros (n1,n2) (m1,m2); compute.
rewrite (add_comm (m1*n2)%N).
do 2 f_equiv; apply mul_comm.
Qed.

Instance mul_wd : Proper (Z.eq ==> Z.eq ==> Z.eq) Z.mul.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.mul_wd".  
assert (forall n, Proper (Z.eq ==> Z.eq) (Z.mul n)).
unfold Z.mul, Z.eq. intros (n1,n2) (p1,p2) (q1,q2) H; simpl in *.
rewrite add_shuffle1, (add_comm (n1*p1)%N).
symmetry. rewrite add_shuffle1.
rewrite <- ! mul_add_distr_l.
rewrite (add_comm p2), (add_comm q2), H.
reflexivity.
intros n n' Hn m m' Hm.
rewrite Hm, (mul_comm n), (mul_comm n'), Hn.
reflexivity.
Qed.

Section Induction.
Variable A : Z.t -> Prop.
Hypothesis A_wd : Proper (Z.eq==>iff) A.

Theorem bi_induction :
A 0 -> (forall n, A n <-> A (Z.succ n)) -> forall n, A n.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.bi_induction".  
Open Scope NScope.
intros A0 AS n; unfold Z.zero, Z.succ, Z.eq in *.
destruct n as [n m].
cut (forall p, A (p, 0)); [intro H1 |].
cut (forall p, A (0, p)); [intro H2 |].
destruct (add_dichotomy n m) as [[p H] | [p H]].
rewrite (A_wd (n, m) (0, p)) by (rewrite add_0_l; now rewrite add_comm).
apply H2.
rewrite (A_wd (n, m) (p, 0)) by now rewrite add_0_r. apply H1.
induct p. assumption. intros p IH.
apply (A_wd (0, p) (1, N.succ p)) in IH; [| now rewrite add_0_l, add_1_l].
rewrite one_succ in IH. now apply AS.
induct p. assumption. intros p IH.
replace 0 with (snd (p, 0)); [| reflexivity].
replace (N.succ p) with (N.succ (fst (p, 0))); [| reflexivity]. now apply -> AS.
Close Scope NScope.
Qed.

End Induction.



Theorem pred_succ : forall n, Z.pred (Z.succ n) == n.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.pred_succ".  
unfold Z.pred, Z.succ, Z.eq; intro n; simpl; now nzsimpl.
Qed.

Theorem succ_pred : forall n, Z.succ (Z.pred n) == n.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.succ_pred".  
intro n; unfold Z.succ, Z.pred, Z.eq; simpl; now nzsimpl.
Qed.

Theorem one_succ : 1 == Z.succ 0.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.one_succ".  
unfold Z.eq; simpl. now nzsimpl'.
Qed.

Theorem two_succ : 2 == Z.succ 1.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.two_succ".  
unfold Z.eq; simpl. now nzsimpl'.
Qed.

Theorem opp_0 : - 0 == 0.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.opp_0".  
unfold Z.opp, Z.eq; simpl. now nzsimpl.
Qed.

Theorem opp_succ : forall n, - (Z.succ n) == Z.pred (- n).
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.opp_succ".  
reflexivity.
Qed.

Theorem add_0_l : forall n, 0 + n == n.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.add_0_l".  
intro n; unfold Z.add, Z.eq; simpl. now nzsimpl.
Qed.

Theorem add_succ_l : forall n m, (Z.succ n) + m == Z.succ (n + m).
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.add_succ_l".  
intros n m; unfold Z.add, Z.eq; simpl. now nzsimpl.
Qed.

Theorem sub_0_r : forall n, n - 0 == n.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.sub_0_r".  
intro n; unfold Z.sub, Z.eq; simpl. now nzsimpl.
Qed.

Theorem sub_succ_r : forall n m, n - (Z.succ m) == Z.pred (n - m).
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.sub_succ_r".  
intros n m; unfold Z.sub, Z.eq; simpl. symmetry; now rewrite add_succ_r.
Qed.

Theorem mul_0_l : forall n, 0 * n == 0.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.mul_0_l".  
intros (n1,n2); unfold Z.mul, Z.eq; simpl; now nzsimpl.
Qed.

Theorem mul_succ_l : forall n m, (Z.succ n) * m == n * m + m.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.mul_succ_l".  
intros (n1,n2) (m1,m2); unfold Z.mul, Z.succ, Z.eq; simpl; nzsimpl.
rewrite <- (add_assoc _ m1), (add_comm m1), (add_assoc _ _ m1).
now rewrite <- (add_assoc _ m2), (add_comm m2), (add_assoc _ (n2*m1)%N m2).
Qed.



Lemma lt_eq_cases : forall n m, n<=m <-> n<m \/ n==m.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.lt_eq_cases".  
intros; apply N.lt_eq_cases.
Qed.

Theorem lt_irrefl : forall n, ~ (n < n).
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.lt_irrefl".  
intros; apply N.lt_irrefl.
Qed.

Theorem lt_succ_r : forall n m, n < (Z.succ m) <-> n <= m.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.lt_succ_r".  
intros n m; unfold Z.lt, Z.le, Z.eq; simpl; nzsimpl. apply lt_succ_r.
Qed.

Theorem min_l : forall n m, n <= m -> Z.min n m == n.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.min_l".  
unfold Z.min, Z.le, Z.eq; simpl; intros (n1,n2) (m1,m2) H; simpl in *.
rewrite min_l by assumption.
now rewrite <- add_assoc, (add_comm m2).
Qed.

Theorem min_r : forall n m, m <= n -> Z.min n m == m.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.min_r".  
unfold Z.min, Z.le, Z.eq; simpl; intros (n1,n2) (m1,m2) H; simpl in *.
rewrite min_r by assumption.
now rewrite add_assoc.
Qed.

Theorem max_l : forall n m, m <= n -> Z.max n m == n.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.max_l".  
unfold Z.max, Z.le, Z.eq; simpl; intros (n1,n2) (m1,m2) H; simpl in *.
rewrite max_l by assumption.
now rewrite <- add_assoc, (add_comm m2).
Qed.

Theorem max_r : forall n m, n <= m -> Z.max n m == m.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.max_r".  
unfold Z.max, Z.le, Z.eq; simpl; intros n m H.
rewrite max_r by assumption.
now rewrite add_assoc.
Qed.

Theorem lt_nge : forall n m, n < m <-> ~(m<=n).
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.lt_nge".  
intros. apply lt_nge.
Qed.

Instance lt_wd : Proper (Z.eq ==> Z.eq ==> iff) Z.lt.
Proof. try hammer_hook "ZNatPairs" "ZNatPairs.ZPairsAxiomsMod.lt_wd".  
assert (forall n, Proper (Z.eq==>iff) (Z.lt n)).
intros (n1,n2). apply proper_sym_impl_iff; auto with *.
unfold Z.lt, Z.eq; intros (r1,r2) (s1,s2) Eq H; simpl in *.
apply le_lt_add_lt with (r1+r2)%N (r1+r2)%N; [apply le_refl; auto with *|].
rewrite add_shuffle2, (add_comm s2), Eq.
rewrite (add_comm s1 n2), (add_shuffle1 n2), (add_comm n2 r1).
now rewrite <- add_lt_mono_r.
intros n n' Hn m m' Hm.
rewrite Hm. rewrite 2 lt_nge, 2 lt_eq_cases, Hn; auto with *.
Qed.

Definition t := Z.t.
Definition eq := Z.eq.
Definition zero := Z.zero.
Definition one := Z.one.
Definition two := Z.two.
Definition succ := Z.succ.
Definition pred := Z.pred.
Definition add := Z.add.
Definition sub := Z.sub.
Definition mul := Z.mul.
Definition opp := Z.opp.
Definition lt := Z.lt.
Definition le := Z.le.
Definition min := Z.min.
Definition max := Z.max.

End ZPairsAxiomsMod.






