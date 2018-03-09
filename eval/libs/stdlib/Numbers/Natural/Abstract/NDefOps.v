From Hammer Require Import Hammer.











Require Import Bool.
Require Import RelationPairs.
Require Export NStrongRec.



Module NdefOpsProp (Import N : NAxiomsRecSig').
Include NStrongRecProp N.



Definition if_zero (A : Type) (a b : A) (n : N.t) : A :=
recursion a (fun _ _ => b) n.

Arguments if_zero [A] a b n.

Instance if_zero_wd (A : Type) :
Proper (Logic.eq ==> Logic.eq ==> N.eq ==> Logic.eq) (@if_zero A).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.if_zero_wd". Restart. 
unfold if_zero.
f_equiv'.
Qed.

Theorem if_zero_0 : forall (A : Type) (a b : A), if_zero a b 0 = a.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.if_zero_0". Restart. 
unfold if_zero; intros; now rewrite recursion_0.
Qed.

Theorem if_zero_succ :
forall (A : Type) (a b : A) (n : N.t), if_zero a b (S n) = b.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.if_zero_succ". Restart. 
intros; unfold if_zero.
now rewrite recursion_succ.
Qed.




Definition def_add (x y : N.t) := recursion y (fun _ => S) x.

Local Infix "+++" := def_add (at level 50, left associativity).

Instance def_add_wd : Proper (N.eq ==> N.eq ==> N.eq) def_add.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.def_add_wd". Restart. 
unfold def_add. f_equiv'.
Qed.

Theorem def_add_0_l : forall y, 0 +++ y == y.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.def_add_0_l". Restart. 
intro y. unfold def_add. now rewrite recursion_0.
Qed.

Theorem def_add_succ_l : forall x y, S x +++ y == S (x +++ y).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.def_add_succ_l". Restart. 
intros x y; unfold def_add.
rewrite recursion_succ; f_equiv'.
Qed.

Theorem def_add_add : forall n m, n +++ m == n + m.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.def_add_add". Restart. 
intros n m; induct n.
now rewrite def_add_0_l, add_0_l.
intros n H. now rewrite def_add_succ_l, add_succ_l, H.
Qed.




Definition def_mul (x y : N.t) := recursion 0 (fun _ p => p +++ x) y.

Local Infix "**" := def_mul (at level 40, left associativity).

Instance def_mul_wd : Proper (N.eq ==> N.eq ==> N.eq) def_mul.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.def_mul_wd". Restart. 
unfold def_mul.
f_equiv'.
Qed.

Theorem def_mul_0_r : forall x, x ** 0 == 0.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.def_mul_0_r". Restart. 
intro. unfold def_mul. now rewrite recursion_0.
Qed.

Theorem def_mul_succ_r : forall x y, x ** S y == x ** y +++ x.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.def_mul_succ_r". Restart. 
intros x y; unfold def_mul.
rewrite recursion_succ; auto with *.
f_equiv'.
Qed.

Theorem def_mul_mul : forall n m, n ** m == n * m.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.def_mul_mul". Restart. 
intros n m; induct m.
now rewrite def_mul_0_r, mul_0_r.
intros m IH; now rewrite def_mul_succ_r, mul_succ_r, def_add_add, IH.
Qed.




Definition ltb (m : N.t) : N.t -> bool :=
recursion
(if_zero false true)
(fun _ f n => recursion false (fun n' _ => f n') n)
m.

Local Infix "<<" := ltb (at level 70, no associativity).

Instance ltb_wd : Proper (N.eq ==> N.eq ==> Logic.eq) ltb.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.ltb_wd". Restart. 
unfold ltb. f_equiv'.
Qed.

Theorem ltb_base : forall n, 0 << n = if_zero false true n.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.ltb_base". Restart. 
intro n; unfold ltb; now rewrite recursion_0.
Qed.

Theorem ltb_step :
forall m n, S m << n = recursion false (fun n' _ => m << n') n.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.ltb_step". Restart. 
intros m n; unfold ltb at 1.
f_equiv.
rewrite recursion_succ; f_equiv'.
Qed.



Theorem ltb_0 : forall n, n << 0 = false.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.ltb_0". Restart. 
cases n.
rewrite ltb_base; now rewrite if_zero_0.
intro n; rewrite ltb_step. now rewrite recursion_0.
Qed.

Theorem ltb_0_succ : forall n, 0 << S n = true.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.ltb_0_succ". Restart. 
intro n; rewrite ltb_base; now rewrite if_zero_succ.
Qed.

Theorem succ_ltb_mono : forall n m, (S n << S m) = (n << m).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.succ_ltb_mono". Restart. 
intros n m.
rewrite ltb_step. rewrite recursion_succ; f_equiv'.
Qed.

Theorem ltb_lt : forall n m, n << m = true <-> n < m.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.ltb_lt". Restart. 
double_induct n m.
cases m.
rewrite ltb_0. split; intro H; [discriminate H | false_hyp H nlt_0_r].
intro n. rewrite ltb_0_succ. split; intro; [apply lt_0_succ | reflexivity].
intro n. rewrite ltb_0. split; intro H; [discriminate | false_hyp H nlt_0_r].
intros n m. rewrite succ_ltb_mono. now rewrite <- succ_lt_mono.
Qed.

Theorem ltb_ge : forall n m, n << m = false <-> n >= m.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.ltb_ge". Restart. 
intros. rewrite <- not_true_iff_false, ltb_lt. apply nlt_ge.
Qed.




Definition even (x : N.t) := recursion true (fun _ p => negb p) x.

Instance even_wd : Proper (N.eq==>Logic.eq) even.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.even_wd". Restart. 
unfold even. f_equiv'.
Qed.

Theorem even_0 : even 0 = true.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.even_0". Restart. 
unfold even.
now rewrite recursion_0.
Qed.

Theorem even_succ : forall x, even (S x) = negb (even x).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.even_succ". Restart. 
unfold even.
intro x; rewrite recursion_succ; f_equiv'.
Qed.




Definition half_aux (x : N.t) : N.t * N.t :=
recursion (0, 0) (fun _ p => let (x1, x2) := p in (S x2, x1)) x.

Definition half (x : N.t) := snd (half_aux x).

Instance half_aux_wd : Proper (N.eq ==> N.eq*N.eq) half_aux.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_aux_wd". Restart. 
intros x x' Hx. unfold half_aux.
f_equiv; trivial.
intros y y' Hy (u,v) (u',v') (Hu,Hv). compute in *.
rewrite Hu, Hv; auto with *.
Qed.

Instance half_wd : Proper (N.eq==>N.eq) half.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_wd". Restart. 
unfold half. f_equiv'.
Qed.

Lemma half_aux_0 : half_aux 0 = (0,0).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_aux_0". Restart. 
unfold half_aux. rewrite recursion_0; auto.
Qed.

Lemma half_aux_succ : forall x,
half_aux (S x) = (S (snd (half_aux x)), fst (half_aux x)).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_aux_succ". Restart. 
intros.
remember (half_aux x) as h.
destruct h as (f,s); simpl in *.
unfold half_aux in *.
rewrite recursion_succ, <- Heqh; simpl; f_equiv'.
Qed.

Theorem half_aux_spec : forall n,
n == fst (half_aux n) + snd (half_aux n).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_aux_spec". Restart. 
apply induction.
intros x x' Hx. setoid_rewrite Hx; auto with *.
rewrite half_aux_0; simpl; rewrite add_0_l; auto with *.
intros.
rewrite half_aux_succ. simpl.
rewrite add_succ_l, add_comm; auto.
now f_equiv.
Qed.

Theorem half_aux_spec2 : forall n,
fst (half_aux n) == snd (half_aux n) \/
fst (half_aux n) == S (snd (half_aux n)).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_aux_spec2". Restart. 
apply induction.
intros x x' Hx. setoid_rewrite Hx; auto with *.
rewrite half_aux_0; simpl. auto with *.
intros.
rewrite half_aux_succ; simpl.
destruct H; auto with *.
right; now f_equiv.
Qed.

Theorem half_0 : half 0 == 0.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_0". Restart. 
unfold half. rewrite half_aux_0; simpl; auto with *.
Qed.

Theorem half_1 : half 1 == 0.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_1". Restart. 
unfold half. rewrite one_succ, half_aux_succ, half_aux_0; simpl; auto with *.
Qed.

Theorem half_double : forall n,
n == 2 * half n \/ n == 1 + 2 * half n.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_double". Restart. 
intros. unfold half.
nzsimpl'.
destruct (half_aux_spec2 n) as [H|H]; [left|right].
rewrite <- H at 1. apply half_aux_spec.
rewrite <- add_succ_l. rewrite <- H at 1. apply half_aux_spec.
Qed.

Theorem half_upper_bound : forall n, 2 * half n <= n.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_upper_bound". Restart. 
intros.
destruct (half_double n) as [E|E]; rewrite E at 2.
apply le_refl.
nzsimpl.
apply le_le_succ_r, le_refl.
Qed.

Theorem half_lower_bound : forall n, n <= 1 + 2 * half n.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_lower_bound". Restart. 
intros.
destruct (half_double n) as [E|E]; rewrite E at 1.
nzsimpl.
apply le_le_succ_r, le_refl.
apply le_refl.
Qed.

Theorem half_nz : forall n, 1 < n -> 0 < half n.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_nz". Restart. 
intros n LT.
assert (LE : 0 <= half n) by apply le_0_l.
le_elim LE; auto.
destruct (half_double n) as [E|E];
rewrite <- LE, mul_0_r, ?add_0_r in E; rewrite E in LT.
order'.
order.
Qed.

Theorem half_decrease : forall n, 0 < n -> half n < n.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.half_decrease". Restart. 
intros n LT.
destruct (half_double n) as [E|E]; rewrite E at 2; nzsimpl'.
rewrite <- add_0_l at 1.
rewrite <- add_lt_mono_r.
assert (LE : 0 <= half n) by apply le_0_l.
le_elim LE; auto.
rewrite <- LE, mul_0_r in E. rewrite E in LT. destruct (nlt_0_r _ LT).
rewrite <- add_succ_l.
rewrite <- add_0_l at 1.
rewrite <- add_lt_mono_r.
apply lt_0_succ.
Qed.





Definition pow (n m : N.t) := recursion 1 (fun _ r => n*r) m.

Local Infix "^^" := pow (at level 30, right associativity).

Instance pow_wd : Proper (N.eq==>N.eq==>N.eq) pow.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.pow_wd". Restart. 
unfold pow. f_equiv'.
Qed.

Lemma pow_0 : forall n, n^^0 == 1.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.pow_0". Restart. 
intros. unfold pow. rewrite recursion_0. auto with *.
Qed.

Lemma pow_succ : forall n m, n^^(S m) == n*(n^^m).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.pow_succ". Restart. 
intros. unfold pow. rewrite recursion_succ; f_equiv'.
Qed.





Definition log (x : N.t) : N.t :=
strong_rec 0
(fun g x =>
if x << 2 then 0
else S (g (half x)))
x.

Instance log_prewd :
Proper ((N.eq==>N.eq)==>N.eq==>N.eq)
(fun g x => if x<<2 then 0 else S (g (half x))).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.log_prewd". Restart. 
intros g g' Hg n n' Hn.
rewrite Hn.
destruct (n' << 2); auto with *.
f_equiv. apply Hg. now f_equiv.
Qed.

Instance log_wd : Proper (N.eq==>N.eq) log.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.log_wd". Restart. 
intros x x' Exx'. unfold log.
apply strong_rec_wd; f_equiv'.
Qed.

Lemma log_good_step : forall n h1 h2,
(forall m, m < n -> h1 m == h2 m) ->
(if n << 2 then 0 else S (h1 (half n))) ==
(if n << 2 then 0 else S (h2 (half n))).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.log_good_step". Restart. 
intros n h1 h2 E.
destruct (n<<2) eqn:H.
auto with *.
f_equiv. apply E, half_decrease.
rewrite two_succ, <- not_true_iff_false, ltb_lt, nlt_ge, le_succ_l in H.
order'.
Qed.
Hint Resolve log_good_step.

Theorem log_init : forall n, n < 2 -> log n == 0.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.log_init". Restart. 
intros n Hn. unfold log. rewrite strong_rec_fixpoint; auto with *.
replace (n << 2) with true; auto with *.
symmetry. now rewrite ltb_lt.
Qed.

Theorem log_step : forall n, 2 <= n -> log n == S (log (half n)).
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.log_step". Restart. 
intros n Hn. unfold log. rewrite strong_rec_fixpoint; auto with *.
replace (n << 2) with false; auto with *.
symmetry. rewrite <- not_true_iff_false, ltb_lt, nlt_ge; auto.
Qed.

Theorem pow2_log : forall n, 0 < n -> half n < 2^^(log n) <= n.
Proof. hammer_hook "NDefOps" "NDefOps.NdefOpsProp.pow2_log". Restart. 
intro n; generalize (le_refl n). set (k:=n) at -2. clearbody k.
revert k. pattern n. apply induction; clear n.
intros n n' Hn; setoid_rewrite Hn; auto with *.
intros k Hk1 Hk2.
le_elim Hk1. destruct (nlt_0_r _ Hk1).
rewrite Hk1 in Hk2. destruct (nlt_0_r _ Hk2).

intros n IH k Hk1 Hk2.
destruct (lt_ge_cases k 2) as [LT|LE].

rewrite log_init, pow_0 by auto.
rewrite <- le_succ_l, <- one_succ in Hk2.
le_elim Hk2.
rewrite two_succ, <- nle_gt, le_succ_l in LT. destruct LT; auto.
rewrite <- Hk2.
rewrite half_1; auto using lt_0_1, le_refl.

rewrite log_step, pow_succ by auto.
rewrite two_succ, le_succ_l in LE.
destruct (IH (half k)) as (IH1,IH2).
rewrite <- lt_succ_r. apply lt_le_trans with k; auto.
now apply half_decrease.
apply half_nz; auto.
set (K:=2^^log (half k)) in *; clearbody K.
split.
rewrite <- le_succ_l in IH1.
apply mul_le_mono_l with (p:=2) in IH1.
eapply lt_le_trans; eauto.
nzsimpl'.
rewrite lt_succ_r.
eapply le_trans; [ eapply half_lower_bound | ].
nzsimpl'; apply le_refl.
eapply le_trans; [ | eapply half_upper_bound ].
apply mul_le_mono_l; auto.
Qed.

End NdefOpsProp.

