From Hammer Require Import Hammer Reconstr.

Require Import Arith.

Lemma lem_1 : le 1 2.
Proof.
  hammer_hook "arith" "arith.lem_1".
  scrush.
Qed.

Lemma lem_2 : forall n : nat, Nat.Odd n \/ Nat.Odd (n + 1).
Proof.
  hammer_hook "arith" "arith.lem_2".
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.Even_or_Odd, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.Odd_succ) Reconstr.Empty.
Qed.

Lemma lem_2_1 : forall n : nat, Nat.Even n \/ Nat.Even (n + 1).
Proof.
  hammer_hook "arith" "arith.lem_2_1".
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.Even_or_Odd, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.Even_succ) Reconstr.Empty.
Qed.

Lemma lem_3 : le 2 3.
Proof.
  hammer_hook "arith" "arith.lem_2".
  scrush.
Qed.

Lemma lem_4 : le 3 10.
Proof.
  hammer_hook "arith" "arith.lem_4".
  scrush.
Qed.

Lemma mult_1 : forall m n k : nat, m * n + k = k + n * m.
Proof.
  hammer_hook "arith" "arith.mult_1".
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_comm, @Coq.Arith.PeanoNat.Nat.mul_comm) Reconstr.Empty.
Qed.

Lemma lem_rew : forall m n : nat, 1 + n + m + 1 = m + 2 + n.
Proof.
  hammer_hook "arith" "arith.lem_rew".
  Reconstr.reasy (@Coq.Arith.Plus.plus_Snm_nSm, @Coq.Arith.PeanoNat.Nat.add_assoc, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Init.Peano.plus_n_Sm, @Coq.Arith.PeanoNat.Nat.add_1_l, @Coq.Arith.PeanoNat.Nat.add_comm) (@Coq.Arith.PeanoNat.Nat.b2n).
Qed.

Lemma lem_pow : forall n : nat, 3 * 3 ^ n = 3 ^ (n + 1).
Proof.
  hammer_hook "arith" "arith.lem_pow".
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.pow_succ_r', @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
Qed.

Lemma lem_pow' : forall n m : nat, m * m ^ n = m ^ (n + 1).
Proof.
  hammer_hook "arith" "arith.lem_pow'".
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.le_0_l, @Coq.Arith.PeanoNat.Nat.pow_succ_r, @Coq.Arith.PeanoNat.Nat.add_1_r) Reconstr.Empty.
Qed.

Lemma le_minusni_n : forall n i:nat, i <= n -> n - i <= n.
Proof.
  hammer_hook "arith" "arith.lem_minusni_n".
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.le_sub_l) Reconstr.Empty.
Qed.

Lemma even_odd_cor :
  forall n:nat, exists p : nat, n = (2 * p) \/ n = S (2 * p).
Proof.
  induction n; sauto.
  - hammer_hook "arith" "arith.even_odd_cor.subgoal_1".
    Reconstr.reasy (@Coq.Init.Peano.plus_O_n) Reconstr.Empty.
  - hammer_hook "arith" "arith.even_odd_cor.subgoal_2".
    Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.add_succ_l, @Coq.Init.Peano.plus_n_O, @Coq.Init.Peano.plus_n_Sm) Reconstr.Empty.
Qed.

Lemma le_double : forall m n:nat, 2 * m <= 2 * n -> m <= n.
Proof.
  hammer_hook "arith" "arith.le_double".
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.mul_le_mono_pos_l, @Coq.Arith.PeanoNat.Nat.lt_0_succ) Reconstr.Empty.
Qed.

Lemma le_mul : forall m n k:nat, k > 0 -> k * m <= k * n -> m <= n.
Proof.
  hammer_hook "arith" "arith.le_mul".
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.mul_le_mono_pos_l) (@Coq.Init.Peano.gt).
Qed.

Lemma lem_lt_le_trans : forall m n, m + 1 > m - n.
Proof.
  hammer_hook "arith" "arith.lem_lt_le_trans".
  Reconstr.rsimple (@Coq.Arith.PeanoNat.Nat.sub_0_le, @Coq.Arith.PeanoNat.Nat.lt_succ_r, @Coq.Arith.PeanoNat.Nat.le_sub_l, @Coq.Arith.PeanoNat.Nat.le_ge_cases, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.sub_succ_l) (@Coq.Init.Peano.gt, @Coq.Init.Peano.lt).
Qed.

Lemma leb_compare2 : forall m n : nat,
                      PeanoNat.Nat.leb n m = true <->
                      (PeanoNat.Nat.compare n m = Lt \/ PeanoNat.Nat.compare n m = Eq).
Proof.
  hammer_hook "arith" "arith.leb_compare2".
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.lt_eq_cases, @Coq.Arith.PeanoNat.Nat.compare_refl, @Coq.Arith.Compare_dec.leb_compare, @Coq.Arith.Compare_dec.leb_complete, @Coq.Arith.Compare_dec.nat_compare_eq, @Coq.Arith.Compare_dec.nat_compare_lt, @Coq.Arith.PeanoNat.Nat.leb_refl) Reconstr.Empty.
Qed.

Lemma lem_arith_0 : forall m n, (m + n) * (m + n) = m * m + 2 * m * n + n * n.
Proof.
  hammer_hook "arith" "arith.lem_arith_0".
  sauto; eauto with arith.
Qed.

Lemma lem_arith_1 : forall m n, (m + n) * (n + m) = m * m + 2 * m * n + n * n.
Proof.
  hammer_hook "arith" "arith.lem_arith_1".
  sauto.
  rewrite Arith.PeanoNat.Nat.mul_comm.
  rewrite Arith.PeanoNat.Nat.mul_comm.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.add_assoc, @Coq.Arith.PeanoNat.Nat.add_comm, @Coq.Arith.PeanoNat.Nat.add_shuffle0) Reconstr.Empty.
Qed.

Lemma lem_arith_2 : forall m n, (m + n)^2 = m^2 + 2 * m * n + n^2.
Proof.
  hammer_hook "arith" "arith.lem_arith_2".
  sauto; eauto with arith.
Qed.

Lemma lem_arith_3 : forall m n, (m + n)^3 = m^3 + 3 * m^2 * n + 3 * m * n^2 + n^3.
Proof.
  hammer_hook "arith" "arith.lem_arith_3".
  sauto; ring.
Qed.

Lemma lem_arith_4 : forall m n, (m + n)^4 = m^4 + 4 * m^3 * n + 6 * m^2 * n^2 + 4 * m * n^3 + n^4.
Proof.
  hammer_hook "arith" "arith.lem_arith_4".
  sauto; ring.
Qed.
