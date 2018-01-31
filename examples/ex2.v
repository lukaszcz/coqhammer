
From Hammer Require Import Hammer.
From Hammer Require Import Reconstr.

Require Import ZArith.

Open Scope Z_scope.

Lemma lem_1 : forall f g,
    (exists c, forall x : Z, Z.abs (f x) <= c * (Z.abs (g x))) <->
    (exists c, c > 0 /\ forall x, Z.abs (f x) <= c * (Z.abs (g x))).
Proof.
  sauto.
  assert (c > 0 \/ c <= 0).
  Reconstr.hobvious Reconstr.Empty
		    Reconstr.Empty
		    (@Coq.ZArith.BinInt.Z.le, @Coq.ZArith.BinInt.Z.gt).
  sauto.
  assert (forall x, Z.abs (f x) <= 0).
  Reconstr.hobvious Reconstr.AllHyps
	            (@Coq.ZArith.BinInt.Z.mul_nonpos_nonneg, @Coq.ZArith.BinInt.Z.abs_nonneg, @Coq.ZArith.BinInt.Z.le_trans)
		    Reconstr.Empty.
  assert (forall x, Z.abs (g x) >= 0).
  Reconstr.hobvious Reconstr.Empty
	(@Coq.ZArith.BinInt.Z.ge_le_iff, @Coq.ZArith.BinInt.Z.le_refl, @Coq.ZArith.BinInt.Z.abs_spec, @Coq.ZArith.BinInt.Z.abs_nonneg, @Coq.ZArith.BinInt.Z.abs_eq)
	(@Coq.ZArith.BinIntDef.Z.abs, @Coq.ZArith.BinInt.Z.ge).
  exists 1; sauto.
  Reconstr.hobvious Reconstr.AllHyps
		    (@Coq.ZArith.BinInt.Z.abs_spec, @Coq.ZArith.BinInt.Z.le_trans)
		    (@Coq.ZArith.BinInt.Z.ge, @Coq.ZArith.BinInt.Z.lt).
  ycrush.
Qed.

Lemma lem_2 : forall f g,
    (exists c, forall x : Z, Z.abs (f x) <= c * (Z.abs (g x))) <->
    (exists c, c > 0 /\ forall x, Z.abs (f x) <= c * (Z.abs (g x))).
Proof.
  sauto.
  assert (c > 0 \/ c <= 0).
  Reconstr.hobvious Reconstr.Empty
		    Reconstr.Empty
		    (@Coq.ZArith.BinInt.Z.le, @Coq.ZArith.BinInt.Z.gt).
  sauto.
  assert (forall x, Z.abs (f x) <= Z.abs (g x)).
  Reconstr.heasy Reconstr.AllHyps
		 (@Coq.ZArith.BinInt.Z.mul_nonpos_nonneg, @Coq.ZArith.BinInt.Z.abs_nonneg, @Coq.ZArith.BinInt.Z.le_trans)
		 Reconstr.Empty.
  exists 1; sauto.
Qed.
