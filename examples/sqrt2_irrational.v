(* This file contains a proof of the fact that the square root of 2 is
   irrational. *)

(* From Hammer Require Import Hammer. *)
From Hammer Require Import Tactics.

Require Import Reals.
Require Import Arith.
Require Import Wf_nat.
Require Import Even.
Require Import Lia.

Lemma lem_0 : forall n m, n <> 0 -> m * m = 2 * n * n -> m < 2 * n.
Proof.
  intros n m H H0.
  destruct (lt_dec m (2 * n)) as [|H1]; try strivial.
  exfalso.
  assert (m >= 2 * n) by lia.
  clear H1.
  assert (m * m >= 2 * n * (2 * n)).
  { assert (m * m >= 2 * n * m).
    { hauto use: @Nat.le_0_l, @Nat.mul_le_mono_nonneg_r unfold: ge. }
    assert (2 * n * m >= 2 * n * (2 * n)).
    { hauto use: @Nat.le_0_l, @Nat.mul_le_mono_nonneg_l unfold: ge. }
    eauto with arith. }
  sauto.
Qed.

Lemma lem_main : forall n m, n * n = 2 * m * m -> m = 0.
Proof.
  intro n; pattern n; apply lt_wf_ind; clear n.
  intros n H m H0.
  destruct (Nat.eq_dec n 0) as [H1|H1]; subst.
  - sauto.
  - destruct (even_odd_cor n) as [k HH].
    destruct HH as [H2|H2]; subst.
    + assert (2 * k * k = m * m) by lia.
      assert (m < 2 * k).
      { qauto use: @Nat.mul_0_r, @lem_0. }
      sauto.
    + sauto.
Qed.

Theorem thm_irrational :
  forall (p q : nat), q <> 0 -> sqrt 2 <> (INR p / INR q)%R.
Proof.
  unfold not.
  intros p q H H0.
  assert (2 * q * q = p * p).
  { assert (((sqrt 2) ^ 2)%R = 2%R).
    { hauto use: @Rsqr_sqrt, @Rlt_R0_R2, @Rsqr_pow2 unfold: Rle. }
    assert (((INR p / INR q) ^ 2)%R = ((INR p / INR q) * (INR p / INR q))%R).
    { qauto use: @Rsqr_pow2 unfold: Rsqr. }
    assert (((INR p / INR q) * (INR p / INR q))%R = ((INR p * INR p) / (INR q * INR q))%R).
    { hauto use: @Rsqr_div, @not_0_INR. }
    assert (HH: 2%R = ((INR p * INR p) / (INR q * INR q))%R) by sauto.
    assert (INR q <> 0%R).
    { qauto use: @INR_not_0, @INR_eq. }
    assert (HH2: (2 * INR q * INR q)%R = (INR p * INR p)%R).
    { rewrite HH; rewrite Rmult_assoc.
      hfcrush use: @Rinv_l_sym, @Rmult_1_r, @Rmult_integral_contrapositive_currified, @Rmult_assoc unfold: Rsqr, Rdiv. }
    clear -HH2.
    assert (forall a b, INR a = INR b -> a = b).
    { qauto use: @INR_eq. }
    assert (INR (2 * q * q) = INR (p * p)).
    { assert (INR (p * p) = (INR p * INR p)%R).
      { hfcrush use: @mult_INR. }
      assert (INR (2 * q * q) = (2 * INR q * INR q)%R).
      { assert (INR (2 * q * q) = (INR 2 * INR q * INR q)%R).
        { hauto ered: off use: @mult_INR. }
        sauto. }
      sauto. }
    sauto. }
  sauto use: lem_main.
Qed.
