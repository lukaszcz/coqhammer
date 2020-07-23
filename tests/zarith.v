From Hammer Require Import Hammer.

Require Import ZArith.
Open Scope Z_scope.

Hammer_version.
Hammer_objects.

Set Hammer SAutoLimit 0.

Lemma lem_1 : Z.le 1 2.
Proof.
  hammer.
Qed.

Lemma lem_2 : forall n : Z, BinInt.Z.Odd n \/ BinInt.Z.Odd (n + 1).
Proof.
  hammer.
Qed.

Lemma lem_3 : Z.le 2 3.
Proof.
  hammer.
Qed.

Lemma mult_1 : forall m n k : Z, m * n + k = k + n * m.
Proof.
  hammer.
Qed.

Lemma lem_rew : forall m n : Z, 1 + n + m + 1 = m + 2 + n.
Proof.
  hammer.
Qed.

Lemma le_minusni_n : forall n i:Z, i >= 0 -> i <= n -> n - i <= n.
Proof.
  hammer.
Qed.

Lemma le_double : forall m n:Z, 2 * m <= 2 * n -> m <= n.
Proof.
  hammer.
Qed.

Lemma le_mul : forall m n k:Z, k > 0 -> k * m <= k * n -> m <= n.
Proof.
  hammer.
Qed.

Lemma le_plus : forall x:Z, x >= 0 -> x + x >= x.
Proof.
  hammer.
Qed.

Lemma le_plus_2 : forall x:Z, 0 < x -> x < x + x.
Proof.
  hammer.
Qed.
