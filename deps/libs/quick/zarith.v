From Hammer Require Import Hammer Reconstr.

Require Import ZArith.
Open Scope Z_scope.

Lemma lem_1 : Z.le 1 2.
Proof.
  hammer_hook "zarith" "zarith.lem_1".
  scrush.
Qed.

Lemma lem_2 : forall n : Z, BinInt.Z.Odd n \/ BinInt.Z.Odd (n + 1).
Proof.
  hammer_hook "zarith" "zarith.lem_2".
  Reconstr.reasy (@Coq.ZArith.BinInt.Z.Even_or_Odd, @Coq.ZArith.BinInt.Z.Odd_succ, @Coq.ZArith.BinInt.Z.add_1_r) Reconstr.Empty.
Qed.

Lemma lem_2_1 : forall n : Z, BinInt.Z.Even n \/ BinInt.Z.Even (n + 1).
Proof.
  hammer_hook "zarith" "zarith.lem_2_1".
  Reconstr.reasy (@Coq.ZArith.BinInt.Z.Even_or_Odd, @Coq.ZArith.BinInt.Z.Even_succ, @Coq.ZArith.BinInt.Z.add_1_r) Reconstr.Empty.
Qed.

Lemma lem_3 : Z.le 2 3.
Proof.
  hammer_hook "zarith" "zarith.lem_2".
  scrush.
Qed.

Lemma lem_4 : Z.le 3 10.
Proof.
  hammer_hook "zarith" "zarith.lem_4".
  scrush.
Qed.

Lemma mult_1 : forall m n k : Z, m * n + k = k + n * m.
Proof.
  hammer_hook "zarith" "zarith.mult_1".
  Reconstr.reasy (@Coq.ZArith.BinInt.Z.mul_comm, @Coq.ZArith.BinInt.Z.add_comm) Reconstr.Empty.
Qed.

Lemma lem_rew : forall m n : Z, 1 + n + m + 1 = m + 2 + n.
Proof.
  hammer_hook "zarith" "zarith.lem_rew".
  Reconstr.reasy (@Coq.ZArith.BinInt.Z.two_succ, @Coq.ZArith.BinInt.Z.add_succ_l, @Coq.ZArith.BinInt.Z.add_succ_r, @Coq.ZArith.BinInt.Z.add_comm, @Coq.ZArith.BinInt.Z.add_1_l, @Coq.ZArith.BinInt.Z.add_assoc, @Coq.ZArith.BinInt.Z.add_shuffle0, @Coq.ZArith.BinInt.Z.div2_odd, @Coq.ZArith.BinInt.Z.one_succ) Reconstr.Empty.
Qed.

Lemma lem_pow_pos : forall m n : Z, m > 0 -> m ^ n >= 0.
Proof.
  hammer_hook "zarith" "zarith.lem_pow_pos".
  Reconstr.rblast (@Coq.ZArith.Zabs.Zabs_spec, @Coq.ZArith.BinInt.Z.le_ngt, @Coq.ZArith.Zorder.Zgt_asym, @Coq.ZArith.BinInt.Z.pow_nonneg) (@Coq.ZArith.BinInt.Z.ge, @Coq.ZArith.BinInt.Z.lt).
Qed.

Lemma le_minusni_n : forall n i:Z, i >= 0 -> i <= n -> n - i <= n.
Proof.
  hammer_hook "zarith" "zarith.lem_minusni_n".
  Reconstr.reasy (@Coq.ZArith.BinInt.Z.ge_le_iff, @Coq.ZArith.BinInt.Z.le_sub_nonneg) (@Coq.ZArith.BinInt.Z.ge, @Coq.ZArith.BinInt.Z.le).
Qed.

Lemma even_odd_cor :
  forall n:Z, exists p : Z, n = (2 * p) \/ n = (2 * p) + 1.
Proof.
  hammer_hook "zarith" "zarith.even_or_odd".
  Reconstr.reasy (@Coq.ZArith.BinInt.Z.Even_or_Odd) (@Coq.ZArith.BinInt.Z.Even, @Coq.ZArith.BinInt.Z.Odd).
Qed.

Lemma le_double : forall m n:Z, 2 * m <= 2 * n -> m <= n.
Proof.
  hammer_hook "zarith" "zarith.le_double".
  scrush.
Qed.

Lemma le_mul : forall m n k:Z, k > 0 -> k * m <= k * n -> m <= n.
Proof.
  hammer_hook "zarith" "zarith.le_mul".
  Reconstr.reasy (@Coq.ZArith.Zorder.Zmult_gt_compat_l, @Coq.ZArith.Zorder.Znot_gt_le) (@Coq.ZArith.BinInt.Z.le, @Coq.ZArith.BinInt.Z.gt).
Qed.

Lemma lem_arith_0 : forall m n, (m + n) * (m + n) = m * m + 2 * m * n + n * n.
Proof.
  hammer_hook "zarith" "zarith.lem_arith_0".
  intros; ring.
Qed.

Lemma lem_arith_1 : forall m n, (m + n) * (n + m) = m * m + 2 * m * n + n * n.
Proof.
  hammer_hook "zarith" "zarith.lem_arith_1".
  intros; ring.
Qed.

Lemma lem_arith_2 : forall m n, (m + n)^2 = m^2 + 2 * m * n + n^2.
Proof.
  hammer_hook "zarith" "zarith.lem_arith_2".
  intros; ring.
Qed.

Lemma lem_arith_3 : forall m n, (m + n)^3 = m^3 + 3 * m^2 * n + 3 * m * n^2 + n^3.
Proof.
  hammer_hook "zarith" "zarith.lem_arith_3".
  intros; ring.
Qed.

Lemma lem_arith_4 : forall m n, (m + n)^4 = m^4 + 4 * m^3 * n + 6 * m^2 * n^2 + 4 * m * n^3 + n^4.
Proof.
  hammer_hook "zarith" "zarith.lem_arith_4".
  intros; ring.
Qed.

Lemma lem_sub_2 : forall m n, (m - n)^2 = m^2 - 2 * m * n + n^2.
Proof.
  hammer_hook "zarith" "zarith.lem_sub_2".
  intros; ring.
Qed.

Lemma lem_sub_3 : forall m n, (m - n)^3 = m^3 - 3 * m^2 * n + 3 * m * n^2 - n^3.
Proof.
  hammer_hook "zarith" "zarith.lem_sub_3".
  intros; ring.
Qed.

Lemma lem_sub_4 : forall m n, (m - n)^4 = m^4 - 4 * m^3 * n + 6 * m^2 * n^2 - 4 * m * n^3 + n^4.
Proof.
  hammer_hook "zarith" "zarith.lem_sub_4".
  intros; ring.
Qed.
