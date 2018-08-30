From Hammer Require Import Hammer.









Require Import Wf_nat ZArith_base Omega Zcomplements.
Require Export Zpow_def.
Local Open Scope Z_scope.








Definition Zpower_nat (z:Z) := nat_rect _ 1 (fun _ => Z.mul z).

Lemma Zpower_nat_0_r z : Zpower_nat z 0 = 1.
Proof. hammer_hook "Zpower" "Zpower.Zpower_nat_0_r".   reflexivity. Qed.

Lemma Zpower_nat_succ_r n z : Zpower_nat z (S n) = z * (Zpower_nat z n).
Proof. hammer_hook "Zpower" "Zpower.Zpower_nat_succ_r".   reflexivity. Qed.



Lemma Zpower_nat_is_exp :
forall (n m:nat) (z:Z),
Zpower_nat z (n + m) = Zpower_nat z n * Zpower_nat z m.
Proof. hammer_hook "Zpower" "Zpower.Zpower_nat_is_exp".  
induction n.
- intros. now rewrite Zpower_nat_0_r, Z.mul_1_l.
- intros. simpl. now rewrite IHn, Z.mul_assoc.
Qed.



Lemma Zpower_pos_nat (z : Z) (p : positive) :
Z.pow_pos z p = Zpower_nat z (Pos.to_nat p).
Proof. hammer_hook "Zpower" "Zpower.Zpower_pos_nat".  
apply Pos2Nat.inj_iter.
Qed.

Lemma Zpower_nat_Z (z : Z) (n : nat) :
Zpower_nat z n = z ^ (Z.of_nat n).
Proof. hammer_hook "Zpower" "Zpower.Zpower_nat_Z".  
induction n. trivial.
rewrite Zpower_nat_succ_r, Nat2Z.inj_succ, Z.pow_succ_r.
now f_equal.
apply Nat2Z.is_nonneg.
Qed.

Theorem Zpower_nat_Zpower z n : 0 <= n ->
z^n = Zpower_nat z (Z.abs_nat n).
Proof. hammer_hook "Zpower" "Zpower.Zpower_nat_Zpower".  
intros. now rewrite Zpower_nat_Z, Zabs2Nat.id_abs, Z.abs_eq.
Qed.



Lemma Zpower_pos_is_exp (n m : positive)(z:Z) :
Z.pow_pos z (n + m) = Z.pow_pos z n * Z.pow_pos z m.
Proof. hammer_hook "Zpower" "Zpower.Zpower_pos_is_exp".  
now apply (Z.pow_add_r z (Zpos n) (Zpos m)).
Qed.

Hint Immediate Zpower_nat_is_exp Zpower_pos_is_exp : zarith.
Hint Unfold Z.pow_pos Zpower_nat: zarith.

Theorem Zpower_exp x n m :
n >= 0 -> m >= 0 -> x ^ (n + m) = x ^ n * x ^ m.
Proof. hammer_hook "Zpower" "Zpower.Zpower_exp".  
Z.swap_greater. apply Z.pow_add_r.
Qed.

Section Powers_of_2.





Definition shift_nat (n:nat) (z:positive) := nat_rect _ z (fun _ => xO) n.
Definition shift_pos (n z:positive) := Pos.iter xO z n.
Definition shift (n:Z) (z:positive) :=
match n with
| Z0 => z
| Zpos p => Pos.iter xO z p
| Zneg p => z
end.

Definition two_power_nat (n:nat) := Zpos (shift_nat n 1).
Definition two_power_pos (x:positive) := Zpos (shift_pos x 1).

Definition two_p (x:Z) :=
match x with
| Z0 => 1
| Zpos y => two_power_pos y
| Zneg y => 0
end.



Lemma shift_nat_equiv n p : shift_nat n p = Pos.shiftl_nat p n.
Proof. hammer_hook "Zpower" "Zpower.shift_nat_equiv".   reflexivity. Qed.

Lemma shift_pos_equiv n p : shift_pos n p = Pos.shiftl p (Npos n).
Proof. hammer_hook "Zpower" "Zpower.shift_pos_equiv".   reflexivity. Qed.

Lemma shift_equiv n p : 0<=n -> Zpos (shift n p) = Z.shiftl (Zpos p) n.
Proof. hammer_hook "Zpower" "Zpower.shift_equiv".  
destruct n.
- trivial.
- simpl; intros. now apply Pos.iter_swap_gen.
- now destruct 1.
Qed.

Lemma two_power_nat_equiv n : two_power_nat n = 2 ^ (Z.of_nat n).
Proof. hammer_hook "Zpower" "Zpower.two_power_nat_equiv".  
induction n.
- trivial.
- now rewrite Nat2Z.inj_succ, Z.pow_succ_r, <- IHn by apply Nat2Z.is_nonneg.
Qed.

Lemma two_power_pos_equiv p : two_power_pos p = 2 ^ Zpos p.
Proof. hammer_hook "Zpower" "Zpower.two_power_pos_equiv".  
now apply Pos.iter_swap_gen.
Qed.

Lemma two_p_equiv x : two_p x = 2 ^ x.
Proof. hammer_hook "Zpower" "Zpower.two_p_equiv".  
destruct x; trivial. apply two_power_pos_equiv.
Qed.



Lemma two_power_nat_S n : two_power_nat (S n) = 2 * two_power_nat n.
Proof. hammer_hook "Zpower" "Zpower.two_power_nat_S".   reflexivity. Qed.

Lemma shift_nat_plus n m x :
shift_nat (n + m) x = shift_nat n (shift_nat m x).
Proof. hammer_hook "Zpower" "Zpower.shift_nat_plus".  
induction n; simpl; now f_equal.
Qed.

Theorem shift_nat_correct n x :
Zpos (shift_nat n x) = Zpower_nat 2 n * Zpos x.
Proof. hammer_hook "Zpower" "Zpower.shift_nat_correct".  
induction n.
- trivial.
- now rewrite Zpower_nat_succ_r, <- Z.mul_assoc, <- IHn.
Qed.

Theorem two_power_nat_correct n : two_power_nat n = Zpower_nat 2 n.
Proof. hammer_hook "Zpower" "Zpower.two_power_nat_correct".  
now rewrite two_power_nat_equiv, Zpower_nat_Z.
Qed.

Lemma shift_pos_nat p x : shift_pos p x = shift_nat (Pos.to_nat p) x.
Proof. hammer_hook "Zpower" "Zpower.shift_pos_nat".  
apply Pos2Nat.inj_iter.
Qed.

Lemma two_power_pos_nat p : two_power_pos p = two_power_nat (Pos.to_nat p).
Proof. hammer_hook "Zpower" "Zpower.two_power_pos_nat".  
unfold two_power_pos. now rewrite shift_pos_nat.
Qed.

Theorem shift_pos_correct p x :
Zpos (shift_pos p x) = Z.pow_pos 2 p * Zpos x.
Proof. hammer_hook "Zpower" "Zpower.shift_pos_correct".  
now rewrite shift_pos_nat, Zpower_pos_nat, shift_nat_correct.
Qed.

Theorem two_power_pos_correct x : two_power_pos x = Z.pow_pos 2 x.
Proof. hammer_hook "Zpower" "Zpower.two_power_pos_correct".  
apply two_power_pos_equiv.
Qed.

Theorem two_power_pos_is_exp x y :
two_power_pos (x + y) = two_power_pos x * two_power_pos y.
Proof. hammer_hook "Zpower" "Zpower.two_power_pos_is_exp".  
rewrite 3 two_power_pos_equiv. now apply (Z.pow_add_r 2 (Zpos x) (Zpos y)).
Qed.

Lemma two_p_correct x : two_p x = 2^x.
Proof. hammer_hook "Zpower" "Zpower.two_p_correct".  exact ((two_p_equiv x)). Qed.

Theorem two_p_is_exp x y :
0 <= x -> 0 <= y -> two_p (x + y) = two_p x * two_p y.
Proof. hammer_hook "Zpower" "Zpower.two_p_is_exp".  
rewrite !two_p_equiv. apply Z.pow_add_r.
Qed.

Lemma two_p_gt_ZERO x : 0 <= x -> two_p x > 0.
Proof. hammer_hook "Zpower" "Zpower.two_p_gt_ZERO".  
Z.swap_greater. rewrite two_p_equiv. now apply Z.pow_pos_nonneg.
Qed.

Lemma two_p_S x : 0 <= x -> two_p (Z.succ x) = 2 * two_p x.
Proof. hammer_hook "Zpower" "Zpower.two_p_S".  
rewrite !two_p_equiv. now apply Z.pow_succ_r.
Qed.

Lemma two_p_pred x : 0 <= x -> two_p (Z.pred x) < two_p x.
Proof. hammer_hook "Zpower" "Zpower.two_p_pred".  
rewrite !two_p_equiv. intros. apply Z.pow_lt_mono_r; auto with zarith.
Qed.

End Powers_of_2.

Hint Resolve two_p_gt_ZERO: zarith.
Hint Immediate two_p_pred two_p_S: zarith.

Section power_div_with_rest.






Definition Zdiv_rest_aux (qrd:Z * Z * Z) :=
let '(q,r,d) := qrd in
(match q with
| Z0 => (0, r)
| Zpos xH => (0, d + r)
| Zpos (xI n) => (Zpos n, d + r)
| Zpos (xO n) => (Zpos n, r)
| Zneg xH => (-1, d + r)
| Zneg (xI n) => (Zneg n - 1, d + r)
| Zneg (xO n) => (Zneg n, r)
end, 2 * d).

Definition Zdiv_rest (x:Z) (p:positive) :=
let (qr, d) := Pos.iter Zdiv_rest_aux (x, 0, 1) p in qr.

Lemma Zdiv_rest_correct1 (x:Z) (p:positive) :
let (_, d) := Pos.iter Zdiv_rest_aux (x, 0, 1) p in
d = two_power_pos p.
Proof. hammer_hook "Zpower" "Zpower.Zdiv_rest_correct1".  
rewrite Pos2Nat.inj_iter, two_power_pos_nat.
induction (Pos.to_nat p); simpl; trivial.
destruct (nat_rect _ _ _ _) as ((q,r),d).
unfold Zdiv_rest_aux. rewrite two_power_nat_S; now f_equal.
Qed.

Lemma Zdiv_rest_correct2 (x:Z) (p:positive) :
let '(q,r,d) := Pos.iter Zdiv_rest_aux (x, 0, 1) p in
x = q * d + r /\ 0 <= r < d.
Proof. hammer_hook "Zpower" "Zpower.Zdiv_rest_correct2".  
apply Pos.iter_invariant; [|omega].
intros ((q,r),d) (H,H'). unfold Zdiv_rest_aux.
destruct q as [ |[q|q| ]|[q|q| ]]; try omega.
- rewrite Pos2Z.inj_xI, Z.mul_add_distr_r in H.
rewrite Z.mul_shuffle3, Z.mul_assoc. omega.
- rewrite Pos2Z.inj_xO in H.
rewrite Z.mul_shuffle3, Z.mul_assoc. omega.
- rewrite Pos2Z.neg_xI, Z.mul_sub_distr_r in H.
rewrite Z.mul_sub_distr_r, Z.mul_shuffle3, Z.mul_assoc. omega.
- rewrite Pos2Z.neg_xO in H.
rewrite Z.mul_shuffle3, Z.mul_assoc. omega.
Qed.



Inductive Zdiv_rest_proofs (x:Z) (p:positive) : Set :=
Zdiv_rest_proof :
forall q r:Z,
x = q * two_power_pos p + r ->
0 <= r -> r < two_power_pos p -> Zdiv_rest_proofs x p.

Lemma Zdiv_rest_correct (x:Z) (p:positive) : Zdiv_rest_proofs x p.
Proof. hammer_hook "Zpower" "Zpower.Zdiv_rest_correct".  
generalize (Zdiv_rest_correct1 x p); generalize (Zdiv_rest_correct2 x p).
destruct (Pos.iter Zdiv_rest_aux (x, 0, 1) p) as ((q,r),d).
intros (H1,(H2,H3)) ->. now exists q r.
Qed.



Lemma Zdiv_rest_ok x p :
let (q,r) := Zdiv_rest x p in
x = q * 2^(Zpos p) + r /\ 0 <= r < 2^(Zpos p).
Proof. hammer_hook "Zpower" "Zpower.Zdiv_rest_ok".  
unfold Zdiv_rest.
generalize (Zdiv_rest_correct1 x p); generalize (Zdiv_rest_correct2 x p).
destruct (Pos.iter Zdiv_rest_aux (x, 0, 1) p) as ((q,r),d).
intros H ->. now rewrite two_power_pos_equiv in H.
Qed.



Lemma Zdiv_rest_shiftr x p :
fst (Zdiv_rest x p) = Z.shiftr x (Zpos p).
Proof. hammer_hook "Zpower" "Zpower.Zdiv_rest_shiftr".  
generalize (Zdiv_rest_ok x p). destruct (Zdiv_rest x p) as (q,r).
intros (H,H'). simpl.
rewrite Z.shiftr_div_pow2 by easy.
apply Z.div_unique_pos with r; trivial. now rewrite Z.mul_comm.
Qed.

End power_div_with_rest.
