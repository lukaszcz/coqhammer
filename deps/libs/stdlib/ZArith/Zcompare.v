From Hammer Require Import Hammer.















Require Export BinPos BinInt.
Require Import Lt Gt Plus Mult.

Local Open Scope Z_scope.




Lemma Zcompare_Gt_Lt_antisym : forall n m:Z, (n ?= m) = Gt <-> (m ?= n) = Lt.
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_Gt_Lt_antisym".  exact (Z.gt_lt_iff). Qed.

Lemma Zcompare_antisym n m : CompOpp (n ?= m) = (m ?= n).
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_antisym".  exact (eq_sym (Z.compare_antisym n m)). Qed.



Lemma Zcompare_Lt_trans :
forall n m p:Z, (n ?= m) = Lt -> (m ?= p) = Lt -> (n ?= p) = Lt.
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_Lt_trans".  exact (Z.lt_trans). Qed.

Lemma Zcompare_Gt_trans :
forall n m p:Z, (n ?= m) = Gt -> (m ?= p) = Gt -> (n ?= p) = Gt.
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_Gt_trans".  
intros n m p. change (n > m -> m > p -> n > p).
Z.swap_greater. intros. now transitivity m.
Qed.



Lemma Zcompare_opp n m : (n ?= m) = (- m ?= - n).
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_opp".  
symmetry. apply Z.compare_opp.
Qed.



Lemma Zcompare_Gt_spec n m : (n ?= m) = Gt ->  exists h, n + - m = Zpos h.
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_Gt_spec".  
rewrite Z.compare_sub. unfold Z.sub.
destruct (n+-m) as [|p|p]; try discriminate. now exists p.
Qed.



Lemma Zcompare_plus_compat n m p : (p + n ?= p + m) = (n ?= m).
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_plus_compat".  
apply Z.add_compare_mono_l.
Qed.

Lemma Zplus_compare_compat (r:comparison) (n m p q:Z) :
(n ?= m) = r -> (p ?= q) = r -> (n + p ?= m + q) = r.
Proof. hammer_hook "Zcompare" "Zcompare.Zplus_compare_compat".  
rewrite (Z.compare_sub n), (Z.compare_sub p), (Z.compare_sub (n+p)).
unfold Z.sub. rewrite Z.opp_add_distr. rewrite Z.add_shuffle1.
destruct (n+-m), (p+-q); simpl; intros; now subst.
Qed.

Lemma Zcompare_succ_Gt n : (Z.succ n ?= n) = Gt.
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_succ_Gt".  
apply Z.lt_gt. apply Z.lt_succ_diag_r.
Qed.

Lemma Zcompare_Gt_not_Lt n m : (n ?= m) = Gt <-> (n ?= m+1) <> Lt.
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_Gt_not_Lt".  
change (n > m <-> n >= m+1). Z.swap_greater. symmetry. apply Z.le_succ_l.
Qed.



Lemma Zcompare_succ_compat n m : (Z.succ n ?= Z.succ m) = (n ?= m).
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_succ_compat".  
rewrite <- 2 Z.add_1_l. apply Z.add_compare_mono_l.
Qed.



Lemma Zcompare_mult_compat :
forall (p:positive) (n m:Z), (Zpos p * n ?= Zpos p * m) = (n ?= m).
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_mult_compat".  
intros p [|n|n] [|m|m]; simpl; trivial; now rewrite Pos.mul_compare_mono_l.
Qed.

Lemma Zmult_compare_compat_l n m p:
p > 0 -> (n ?= m) = (p * n ?= p * m).
Proof. hammer_hook "Zcompare" "Zcompare.Zmult_compare_compat_l".  
intros; destruct p; try discriminate.
symmetry. apply Zcompare_mult_compat.
Qed.

Lemma Zmult_compare_compat_r n m p :
p > 0 -> (n ?= m) = (n * p ?= m * p).
Proof. hammer_hook "Zcompare" "Zcompare.Zmult_compare_compat_r".  
intros; rewrite 2 (Z.mul_comm _ p); now apply Zmult_compare_compat_l.
Qed.



Lemma Zcompare_elim :
forall (c1 c2 c3:Prop) (n m:Z),
(n = m -> c1) ->
(n < m -> c2) ->
(n > m -> c3) -> match n ?= m with
| Eq => c1
| Lt => c2
| Gt => c3
end.
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_elim".  
intros. case Z.compare_spec; trivial. now Z.swap_greater.
Qed.

Lemma Zcompare_eq_case :
forall (c1 c2 c3:Prop) (n m:Z),
c1 -> n = m -> match n ?= m with
| Eq => c1
| Lt => c2
| Gt => c3
end.
Proof. hammer_hook "Zcompare" "Zcompare.Zcompare_eq_case".  
intros. subst. now rewrite Z.compare_refl.
Qed.

Lemma Zle_compare :
forall n m:Z,
n <= m -> match n ?= m with
| Eq => True
| Lt => True
| Gt => False
end.
Proof. hammer_hook "Zcompare" "Zcompare.Zle_compare".  
intros. case Z.compare_spec; trivial; Z.order.
Qed.

Lemma Zlt_compare :
forall n m:Z,
n < m -> match n ?= m with
| Eq => False
| Lt => True
| Gt => False
end.
Proof. hammer_hook "Zcompare" "Zcompare.Zlt_compare".  
intros x y H; now rewrite H.
Qed.

Lemma Zge_compare :
forall n m:Z,
n >= m -> match n ?= m with
| Eq => True
| Lt => False
| Gt => True
end.
Proof. hammer_hook "Zcompare" "Zcompare.Zge_compare".  
intros. now case Z.compare_spec.
Qed.

Lemma Zgt_compare :
forall n m:Z,
n > m -> match n ?= m with
| Eq => False
| Lt => False
| Gt => True
end.
Proof. hammer_hook "Zcompare" "Zcompare.Zgt_compare".  
intros x y H; now rewrite H.
Qed.



Notation Zcompare_refl := Z.compare_refl (compat "8.3").
Notation Zcompare_Eq_eq := Z.compare_eq (compat "8.3").
Notation Zcompare_Eq_iff_eq := Z.compare_eq_iff (compat "8.3").
Notation Zcompare_spec := Z.compare_spec (compat "8.3").
Notation Zmin_l := Z.min_l (compat "8.3").
Notation Zmin_r := Z.min_r (compat "8.3").
Notation Zmax_l := Z.max_l (compat "8.3").
Notation Zmax_r := Z.max_r (compat "8.3").
Notation Zabs_eq := Z.abs_eq (compat "8.3").
Notation Zabs_non_eq := Z.abs_neq (compat "8.3").
Notation Zsgn_0 := Z.sgn_null (compat "8.3").
Notation Zsgn_1 := Z.sgn_pos (compat "8.3").
Notation Zsgn_m1 := Z.sgn_neg (compat "8.3").


