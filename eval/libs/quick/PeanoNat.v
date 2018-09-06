From Hammer Require Import Hammer.











Require Import NAxioms NProperties OrdersFacts.

Theorem bi_induction :
forall A : nat -> Prop, Proper (eq==>iff) A ->
A 0 -> (forall n : nat, A n <-> A (S n)) -> forall n : nat, A n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.bi_induction".
intros A A_wd A0 AS. apply nat_ind. assumption. intros; now apply -> AS.
Qed.



Definition recursion {A} : A -> (nat -> A -> A) -> nat -> A :=
nat_rect (fun _ => A).

Instance recursion_wd {A} (Aeq : relation A) :
Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) recursion.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.recursion_wd".
intros a a' Ha f f' Hf n n' Hn. subst n'.
induction n; simpl; auto. apply Hf; auto.
Qed.

Theorem recursion_0 :
forall {A} (a : A) (f : nat -> A -> A), recursion a f 0 = a.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.recursion_0".
reflexivity.
Qed.

Theorem recursion_succ :
forall {A} (Aeq : relation A) (a : A) (f : nat -> A -> A),
Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
forall n : nat, Aeq (recursion a f (S n)) (f n (recursion a f n)).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.recursion_succ".
unfold Proper, respectful in *; induction n; simpl; auto.
Qed.





Definition eq := @Logic.eq nat.
Definition le := Peano.le.
Definition lt := Peano.lt.

Set Hammer CrushLimit 0.

Lemma pred_succ n : pred (S n) = n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.pred_succ".
reflexivity.
Qed.

Lemma pred_0 : pred 0 = 0.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.pred_0".
reflexivity.
Qed.

Lemma one_succ : 1 = S 0.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.one_succ".
reflexivity.
Qed.

Lemma two_succ : 2 = S 1.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.two_succ".
reflexivity.
Qed.

Lemma add_0_l n : 0 + n = n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.add_0_l".
reflexivity.
Qed.

Lemma add_succ_l n m : (S n) + m = S (n + m).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.add_succ_l".
reflexivity.
Qed.

Lemma sub_0_r n : n - 0 = n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.sub_0_r".
now destruct n.
Qed.

Lemma sub_succ_r n m : n - (S m) = pred (n - m).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.sub_succ_r".
revert m. induction n; destruct m; simpl; auto. apply sub_0_r.
Qed.

Lemma mul_0_l n : 0 * n + 1 = 1.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.mul_0_l".
reflexivity.
Qed.

Lemma mul_succ_l n m : S n * m + 1 = n * m + m + 1.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.mul_succ_l".
       Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.mul_succ_l) Reconstr.Empty.
Qed.

Lemma lt_succ_r n m : n < S m <-> m + 1 > n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.lt_succ_r".
       Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_1_r) (@Coq.Init.Peano.gt).
Qed.



Lemma eqb_eq n m : eqb n m = true <-> n = m.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.eqb_eq".
revert m.
induction n; destruct m; simpl; rewrite ?IHn; split; try easy.
Qed.

Require Import Arith.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.leb_le".
revert m.
induction n; destruct m; simpl.
- now split.
- split; trivial. intros; apply Peano.le_0_n.
- now split.
- rewrite IHn; split.
+ apply Peano.le_n_S.
+ apply Peano.le_S_n.
Qed.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.ltb_lt".
apply leb_le.
Qed.



Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.eq_dec".
induction n; destruct m.
- now left.
- now right.
- now right.
- destruct (IHn m); [left|right]; auto.
Defined.





Lemma compare_eq_iff n m : (n ?= m) = Eq <-> n = m.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.compare_eq_iff".
revert m; induction n; destruct m; simpl; rewrite ?IHn; split; auto; easy.
Qed.

Lemma compare_lt_iff n m : (n ?= m) = Lt <-> n < m.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.compare_lt_iff".
revert m; induction n; destruct m; simpl; rewrite ?IHn; split; try easy.
- intros _. apply Peano.le_n_S, Peano.le_0_n.
- apply Peano.le_n_S.
- apply Peano.le_S_n.
Qed.

Lemma compare_le_iff n m : (n ?= m) <> Gt <-> n <= m.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.compare_le_iff".
revert m; induction n; destruct m; simpl; rewrite ?IHn.
- now split.
- split; intros. apply Peano.le_0_n. easy.
- split. now destruct 1. inversion 1.
- split; intros. now apply Peano.le_n_S. now apply Peano.le_S_n.
Qed.

Lemma compare_antisym n m : (m ?= n) = CompOpp (n ?= m).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.compare_antisym".
revert m; induction n; destruct m; simpl; trivial.
Qed.

Lemma compare_succ n m : (S n ?= S m) = (n ?= m).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.compare_succ".
reflexivity.
Qed.






Lemma max_l : forall n m, m <= n -> max n m = n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.max_l".
exact Peano.max_l.
Qed.

Lemma max_r : forall n m, n <= m -> max n m = m.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.max_r".
exact Peano.max_r.
Qed.

Lemma min_l : forall n m, n <= m -> min n m = n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.min_l".
exact Peano.min_l.
Qed.

Lemma min_r : forall n m, m <= n -> min n m = m.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.min_r".
exact Peano.min_r.
Qed.

Lemma pow_0_r a : a^0 = 1.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.pow_0_r".   reflexivity. Qed.

Lemma pow_succ_r a b : 0<=b -> a^(S b) = a * a^b.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.pow_succ_r".   reflexivity. Qed.



Lemma square_spec n : Nat.square n = n * n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.square_spec".   reflexivity. Qed.



Definition Even n := exists m, n = 2*m.
Definition Odd n := exists m, n = 2*m+1.

Module Private_Parity.

Lemma Even_1 : ~ Even 1.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.Private_Parity.Even_1".
intros ([|], H); try discriminate.
simpl in H. now rewrite <- plus_n_Sm in H.
Qed.

Lemma Even_2 n : Even n <-> Even (S (S n)).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.Private_Parity.Even_2".
split; intros (m,H).
- exists (S m). rewrite H. simpl. now rewrite plus_n_Sm.
- destruct m; try discriminate.
exists m. simpl in H. rewrite <- plus_n_Sm in H. now inversion H.
Qed.

Lemma Odd_0 : ~ Odd 0.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.Private_Parity.Odd_0".
now intros ([|], H).
Qed.

Lemma Odd_2 n : Odd n <-> Odd (S (S n)).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.Private_Parity.Odd_2".
split; intros (m,H).
- exists (S m). rewrite H. simpl. now rewrite <- (plus_n_Sm m).
- destruct m; try discriminate.
exists m. simpl in H. rewrite <- plus_n_Sm in H. inversion H.
simpl. now rewrite <- !plus_n_Sm, <- !plus_n_O.
Qed.

End Private_Parity.
Import Private_Parity.

Lemma even_spec : forall n, Nat.even n = true <-> Even n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.even_spec".
fix 1.
destruct n as [|[|n]]; simpl.
- split; [ now exists 0 | trivial ].
- split; [ discriminate | intro H; elim (Even_1 H) ].
- rewrite even_spec. apply Even_2.
Qed.

Lemma odd_spec : forall n, Nat.odd n = true <-> Odd n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.odd_spec".
unfold Nat.odd.
fix 1.
destruct n as [|[|n]]; simpl.
- split; [ discriminate | intro H; elim (Odd_0 H) ].
- split; [ now exists 0 | trivial ].
- rewrite odd_spec. apply Odd_2.
Qed.



Lemma divmod_spec : forall x y q u, u <= y ->
let (q',u') := Nat.divmod x y q u in
x + (S y)*q + (y-u) = (S y)*q' + (y-u') /\ u' <= y.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.divmod_spec".
induction x.
- simpl; intuition.
- intros y q u H. destruct u; simpl Nat.divmod.
+ generalize (IHx y (S q) y (le_n y)). destruct Nat.divmod as (q',u').
intros (EQ,LE); split; trivial.
rewrite <- EQ, sub_0_r, Nat.sub_diag, Nat.add_0_r.
now rewrite !add_succ_l, <- Nat.add_succ_r, <- Nat.add_assoc, Nat.mul_succ_r.
+ assert (H' : u <= y).
{ apply le_trans with (S u); trivial. do 2 constructor. }
generalize (IHx y q u H'). destruct Nat.divmod as (q',u').
intros (EQ,LE); split; trivial.
rewrite <- EQ.
rewrite !add_succ_l, <- Nat.add_succ_r. f_equal. now rewrite <- Nat.sub_succ_l.
Qed.

Lemma div_mod x y : y<>0 -> x = y*(x/y) + x mod y.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.div_mod".
intros Hy.
destruct y; [ now elim Hy | clear Hy ].
unfold Nat.div, Nat.modulo.
generalize (divmod_spec x y 0 y (le_n y)).
destruct Nat.divmod as (q,u).
intros (U,V).
simpl in *.
now rewrite Nat.mul_0_r, Nat.sub_diag, !Nat.add_0_r in U.
Qed.

Lemma mod_bound_pos x y : 0<=x -> 0<y -> 0 <= x mod y < y.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.mod_bound_pos".
intros Hx Hy. split. apply Nat.le_0_l.
destruct y; [ now elim Hy | clear Hy ].
unfold Nat.modulo.
apply lt_succ_r.
assert (H: forall z, y + 1 > y - z).
hammer_hook "PeanoNat" "PeanoNat.Nat.mod_bound_pos.lem_lt_le_trans".
Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.sub_0_le, @Coq.Arith.PeanoNat.Nat.lt_succ_r, @Coq.Arith.PeanoNat.Nat.le_sub_l, @Coq.Arith.PeanoNat.Nat.le_ge_cases, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.sub_succ_l) (@Coq.Init.Peano.gt, @Coq.Init.Peano.lt).
apply H.
Qed.



Lemma sqrt_iter_spec : forall k p q r,
q = p+p -> r<=q ->
let s := Nat.sqrt_iter k p q r in
s*s <= k + p*p + (q - r) < (S s)*(S s).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.sqrt_iter_spec".
induction k.
-
simpl; intros p q r Hq Hr.
split.
+ apply Nat.le_add_r.
+ apply Nat.lt_succ_r.
rewrite Nat.mul_succ_r.
rewrite Nat.add_assoc, (Nat.add_comm p), <- Nat.add_assoc.
apply Nat.add_le_mono_l.
rewrite <- Hq. apply Nat.le_sub_l.
-
destruct r.
+
intros Hq _.
replace (S k + p*p + (q-0)) with (k + (S p)*(S p) + (S (S q) - S (S q))).
* apply IHk.
simpl. now rewrite Nat.add_succ_r, Hq. apply le_n.
* rewrite Nat.sub_diag, sub_0_r, Nat.add_0_r. simpl.
rewrite Nat.add_succ_r; f_equal. rewrite <- Nat.add_assoc; f_equal.
rewrite Nat.mul_succ_r, (Nat.add_comm p), <- Nat.add_assoc. now f_equal.
+
intros Hq Hr.
replace (S k + p*p + (q-S r)) with (k + p*p + (q - r)).
* apply IHk; trivial. apply le_trans with (S r); trivial. do 2 constructor.
* simpl. rewrite <- Nat.add_succ_r. f_equal. rewrite <- Nat.sub_succ_l; trivial.
Qed.

Lemma sqrt_specif n : (Nat.sqrt n)*(Nat.sqrt n) <= n < S (Nat.sqrt n) * S (Nat.sqrt n).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.sqrt_specif".
set (s:=Nat.sqrt n).
replace n with (n + 0*0 + (0-0)).
apply sqrt_iter_spec; auto.
simpl. now rewrite !Nat.add_0_r.
Qed.

Definition sqrt_spec a (Ha:0<=a) := sqrt_specif a.

Lemma sqrt_neg a : a<0 -> Nat.sqrt a = 0.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.sqrt_neg".   inversion 1. Qed.



Lemma log2_iter_spec : forall k p q r,
2^(S p) = q + S r -> r < 2^p ->
let s := Nat.log2_iter k p q r in
2^s <= k + q < 2^(S s).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.log2_iter_spec".
induction k.
-
intros p q r EQ LT. simpl Nat.log2_iter. cbv zeta.
split.
+ rewrite add_0_l.
rewrite (Nat.add_le_mono_l _ _ (2^p)).
simpl Nat.pow in EQ. rewrite Nat.add_0_r in EQ. rewrite EQ.
rewrite Nat.add_comm. apply Nat.add_le_mono_r. apply LT.
+ rewrite EQ, Nat.add_comm. apply Nat.add_lt_mono_l.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.le_0_l, @Coq.Arith.PeanoNat.Nat.lt_succ_r) Reconstr.Empty.
-
intros p q r EQ LT. destruct r.
+
rewrite Nat.add_succ_r, Nat.add_0_r in EQ.
rewrite add_succ_l, <- Nat.add_succ_r. apply IHk.
* rewrite <- EQ. remember (S p) as p'; simpl. now rewrite Nat.add_0_r.
* rewrite EQ. constructor.
+
rewrite add_succ_l, <- Nat.add_succ_r. apply IHk.
* now rewrite add_succ_l, <- Nat.add_succ_r.
* apply le_lt_trans with (S r); trivial. do 2 constructor.
Qed.

Lemma log2_spec n : 0<n ->
2^(Nat.log2 n) <= n < 2^(S (Nat.log2 n)).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.log2_spec".
intros.
set (s:=Nat.log2 n).
replace n with (pred n + 1).
apply log2_iter_spec; auto.
rewrite Nat.add_1_r.
apply Nat.succ_pred. now apply Nat.neq_sym, Nat.lt_neq.
Qed.

Lemma log2_nonpos n : n<=0 -> Nat.log2 n = 0.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.log2_nonpos".
inversion 1; now subst.
Qed.



Definition divide x y := exists z, y=z*x.
Notation "( x | y )" := (divide x y) (at level 0) : nat_scope.

Lemma gcd_divide : forall a b, (Nat.gcd a b | a) /\ (Nat.gcd a b | b).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.gcd_divide".
fix 1.
intros [|a] b; simpl.
split.
now exists 0.
exists 1. simpl. now rewrite <- plus_n_O.
fold (b mod (S a)).
destruct (gcd_divide (b mod (S a)) (S a)) as (H,H').
set (a':=S a) in *.
split; auto.
rewrite (div_mod b a') at 2 by discriminate.
destruct H as (u,Hu), H' as (v,Hv).
rewrite Nat.mul_comm.
exists ((b/a')*v + u).
rewrite Nat.mul_add_distr_r.
now rewrite <- Nat.mul_assoc, <- Hv, <- Hu.
Qed.

Lemma gcd_divide_l : forall a b, (Nat.gcd a b | a).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.gcd_divide_l".
intros. apply gcd_divide.
Qed.

Lemma gcd_divide_r : forall a b, (Nat.gcd a b | b).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.gcd_divide_r".
intros. apply gcd_divide.
Qed.

Lemma gcd_greatest : forall a b c, (c|a) -> (c|b) -> (c|Nat.gcd a b).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.gcd_greatest".
fix 1.
intros [|a] b; simpl; auto.
fold (b mod (S a)).
intros c H H'. apply gcd_greatest; auto.
set (a':=S a) in *.
rewrite (div_mod b a') in H' by discriminate.
destruct H as (u,Hu), H' as (v,Hv).
exists (v - (b/a')*u).
rewrite Nat.mul_comm in Hv.
rewrite Nat.mul_sub_distr_r, <- Hv, <- Nat.mul_assoc, <-Hu.
now rewrite Nat.add_comm, Nat.add_sub.
Qed.

Lemma gcd_nonneg a b : 0<=Nat.gcd a b.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.gcd_nonneg".   apply Nat.le_0_l. Qed.




Lemma div2_double n : Nat.div2 (2*n) = n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.div2_double".
induction n; trivial.
simpl Nat.mul. rewrite Nat.add_succ_r. simpl. now f_equal.
Qed.

Lemma div2_succ_double n : Nat.div2 (S (2*n)) = n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.div2_succ_double".
induction n; trivial.
simpl. f_equal. now rewrite Nat.add_succ_r.
Qed.

Lemma le_div2 n : Nat.div2 (S n) <= n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.le_div2".
revert n.
fix 1.
destruct n; simpl; trivial. apply lt_succ_r.
destruct n; [simpl|]; trivial. now constructor.
hammer_hook "PeanoNat" "PeanoNat.Nat.le_div2.subgoal_1".
Reconstr.ryelles6 (@Coq.Arith.PeanoNat.Nat.div2_decr, @Coq.Arith.PeanoNat.Nat.succ_le_mono, @Coq.Init.Peano.le_S, @Coq.Init.Peano.le_n, @Coq.Arith.PeanoNat.Nat.add_1_r) (@Coq.Init.Peano.lt, @Coq.Init.Peano.gt).
Qed.

Lemma lt_div2 n : 0 < n -> Nat.div2 n < n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.lt_div2".
destruct n.
- inversion 1.
- Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_div2) Reconstr.Empty.
Qed.

Lemma div2_decr a n : a <= S n -> Nat.div2 a <= n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.div2_decr".
destruct a; intros H.
- simpl. apply Nat.le_0_l.
- apply Nat.succ_le_mono in H.
apply le_trans with a; [ apply le_div2 | trivial ].
Qed.

Lemma double_twice : forall n, Nat.double n = 2*n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.double_twice".
simpl; intros. now rewrite Nat.add_0_r.
Qed.

Lemma testbit_0_l : forall n, Nat.testbit 0 n = false.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.testbit_0_l".
now induction n.
Qed.

Lemma testbit_odd_0 a : Nat.testbit (2*a+1) 0 = true.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.testbit_odd_0".
unfold Nat.testbit. rewrite odd_spec. now exists a.
Qed.

Lemma testbit_even_0 a : Nat.testbit (2*a) 0 = false.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.testbit_even_0".
unfold Nat.testbit, Nat.odd. rewrite (proj2 (even_spec _)); trivial.
now exists a.
Qed.

Lemma testbit_odd_succ' a n : Nat.testbit (2*a+1) (S n) = Nat.testbit a n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.testbit_odd_succ'".
unfold Nat.testbit; fold Nat.testbit.
rewrite Nat.add_1_r. f_equal.
apply div2_succ_double.
Qed.

Lemma testbit_even_succ' a n : Nat.testbit (2*a) (S n) = Nat.testbit a n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.testbit_even_succ'".
unfold Nat.testbit; fold Nat.testbit. f_equal. apply div2_double.
Qed.

Lemma shiftr_specif : forall a n m,
Nat.testbit (Nat.shiftr a n) m = Nat.testbit a (m+n).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.shiftr_specif".
induction n; intros m. trivial.
now rewrite Nat.add_0_r.
now rewrite Nat.add_succ_r, <- add_succ_l, <- IHn.
Qed.

Lemma shiftl_specif_high : forall a n m, n<=m ->
Nat.testbit (Nat.shiftl a n) m = Nat.testbit a (m-n).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.shiftl_specif_high".
induction n; intros m H. trivial.
now rewrite sub_0_r.
destruct m. inversion H.
simpl. apply Nat.succ_le_mono in H.
change (Nat.shiftl a (S n)) with (double (shiftl a n)).
rewrite double_twice, div2_double. now apply IHn.
Qed.

Lemma shiftl_spec_low : forall a n m, m<n ->
Nat.testbit (Nat.shiftl a n) m = false.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.shiftl_spec_low".
induction n; intros m H. inversion H.
change (Nat.shiftl a (S n)) with (Nat.double (Nat.shiftl a n)).
destruct m; simpl.
unfold Nat.odd. apply negb_false_iff.
apply even_spec. exists (Nat.shiftl a n). apply double_twice.
rewrite double_twice, div2_double. apply IHn.
now apply Nat.succ_le_mono.
Qed.

Lemma div2_bitwise : forall op n a b,
Nat.div2 (Nat.bitwise op (S n) a b) = Nat.bitwise op n (Nat.div2 a) (Nat.div2 b).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.div2_bitwise".
intros. unfold Nat.bitwise; fold Nat.bitwise.
destruct (op (Nat.odd a) (Nat.odd b)).
now rewrite div2_succ_double.
now rewrite add_0_l, div2_double.
Qed.

Lemma odd_bitwise : forall op n a b,
Nat.odd (Nat.bitwise op (S n) a b) = op (Nat.odd a) (Nat.odd b).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.odd_bitwise".
intros. unfold Nat.bitwise; fold Nat.bitwise.
destruct (op (Nat.odd a) (Nat.odd b)).
apply odd_spec. rewrite Nat.add_comm. eexists; eauto.
unfold Nat.odd. apply negb_false_iff. apply even_spec.
rewrite add_0_l; eexists; eauto.
Qed.

Lemma testbit_bitwise_1 : forall op, (forall b, op false b = false) ->
forall n m a b, a<=n ->
Nat.testbit (Nat.bitwise op n a b) m = op (Nat.testbit a m) (Nat.testbit b m).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.testbit_bitwise_1".
intros op Hop.
induction n; intros m a b Ha.
simpl. inversion Ha; subst. now rewrite testbit_0_l.
destruct m.
apply odd_bitwise.
unfold Nat.testbit; fold Nat.testbit. rewrite div2_bitwise.
apply IHn. now apply div2_decr.
Qed.

Lemma testbit_bitwise_2 : forall op, op false false = false ->
forall n m a b, a<=n -> b<=n ->
Nat.testbit (Nat.bitwise op n a b) m = op (Nat.testbit a m) (Nat.testbit b m).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.testbit_bitwise_2".
intros op Hop.
induction n; intros m a b Ha Hb.
simpl. inversion Ha; inversion Hb; subst. now rewrite testbit_0_l.
destruct m.
apply odd_bitwise.
unfold Nat.testbit; fold Nat.testbit. rewrite div2_bitwise.
apply IHn; now apply div2_decr.
Qed.

Lemma land_spec a b n :
Nat.testbit (Nat.land a b) n = Nat.testbit a n && Nat.testbit b n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.land_spec".
unfold Nat.land. apply testbit_bitwise_1; trivial.
Qed.

Lemma ldiff_spec a b n :
Nat.testbit (Nat.ldiff a b) n = Nat.testbit a n && negb (Nat.testbit b n).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.ldiff_spec".
unfold Nat.ldiff. apply testbit_bitwise_1; trivial.
Qed.

Lemma lor_spec a b n :
Nat.testbit (Nat.lor a b) n = Nat.testbit a n || Nat.testbit b n.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.lor_spec".
unfold Nat.lor. apply testbit_bitwise_2.
- trivial.
- destruct (Nat.compare_spec a b).
+ rewrite max_l; subst; trivial.
+ apply Nat.lt_le_incl in H. now rewrite max_r.
+ apply Nat.lt_le_incl in H. now rewrite max_l.
- destruct (Nat.compare_spec a b).
+ rewrite max_r; subst; trivial.
+ apply Nat.lt_le_incl in H. now rewrite max_r.
+ apply Nat.lt_le_incl in H. now rewrite max_l.
Qed.

Lemma lxor_spec a b n :
Nat.testbit (Nat.lxor a b) n = xorb (Nat.testbit a n) (Nat.testbit b n).
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.lxor_spec".
unfold Nat.lxor. apply testbit_bitwise_2.
- trivial.
- destruct (Nat.compare_spec a b).
+ rewrite max_l; subst; trivial.
+ apply Nat.lt_le_incl in H. now rewrite max_r.
+ apply Nat.lt_le_incl in H. now rewrite max_l.
- destruct (Nat.compare_spec a b).
+ rewrite max_r; subst; trivial.
+ apply Nat.lt_le_incl in H. now rewrite max_r.
+ apply Nat.lt_le_incl in H. now rewrite max_l.
Qed.

Lemma div2_spec a : Nat.div2 a = Nat.shiftr a 1.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.div2_spec".
reflexivity.
Qed.



Definition testbit_odd_succ a n (_:0<=n) := testbit_odd_succ' a n.
Definition testbit_even_succ a n (_:0<=n) := testbit_even_succ' a n.
Lemma testbit_neg_r a n (H:n<0) : Nat.testbit a n = false.
Proof. hammer_hook "PeanoNat" "PeanoNat.Nat.testbit_neg_r".   inversion H. Qed.

Definition shiftl_spec_high a n m (_:0<=m) := shiftl_specif_high a n m.
Definition shiftr_spec a n m (_:0<=m) := shiftr_specif a n m.



Section TestOrder.
Let test : forall x y, x<=y -> y<=x -> x=y.
Proof. hammer_hook "PeanoNat" "PeanoNat.TestOrder.test".
Nat.order.
Qed.
End TestOrder.
