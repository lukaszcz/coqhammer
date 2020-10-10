From Hammer Require Import Hammer.

Hammer_version.
Hammer_objects.

Set Hammer SAutoLimit 0.

Require NArith.Ndec.

Lemma Nleb_alt :
  forall b a c : BinNums.N, Ndec.Nleb b c = BinNat.N.leb b c /\ Ndec.Nleb a b = BinNat.N.leb a b.
Proof.
  hammer.
Qed.

Require NArith.BinNat.

Lemma setbit_iff : forall m a n : BinNums.N,
                     n = m \/ true = BinNat.N.testbit a m <->
                     BinNat.N.testbit (BinNat.N.setbit a n) m = true.
Proof.
  hammer.
Qed.

Lemma in_int_p_Sq : forall r p q a : nat, a >= 0 ->
                      Between.in_int p (S q) r -> Between.in_int p q r \/ r = q \/ a = 0.
Proof.
  hammer.
Qed.

Require Reals.Rminmax.

Lemma min_spec_1 : forall n m : Rdefinitions.R,
                   (Rdefinitions.Rle m n /\ Rbasic_fun.Rmin m m = m) \/
                   (Rdefinitions.Rlt n m /\ Rbasic_fun.Rmin m n = n).
Proof.
  hammer.
Qed.

Lemma min_spec_2 : forall n m : Rdefinitions.R,
                   (Rdefinitions.Rle m n /\ Rbasic_fun.Rmin m n = m) \/
                   (Rdefinitions.Rlt n m /\ Rbasic_fun.Rmin m n = n).
Proof.
  hammer.
Qed.

Require Reals.Rpower.

Lemma exp_Ropp
     : forall x y : Rdefinitions.R,
       Rdefinitions.Rinv (Rtrigo_def.exp x) = Rtrigo_def.exp (Rdefinitions.Ropp x).
Proof.
  hammer.
Qed.

(*
Lemma leb_compare2 : forall m n : nat,
                      PeanoNat.Nat.leb n m = true <->
                      (PeanoNat.Nat.compare n m = Lt \/ PeanoNat.Nat.compare n m = Eq).
Proof.
  assert (forall c : Datatypes.comparison, c = Eq \/ c = Lt \/ c = Gt) by sauto inverting Datatypes.comparison.
  (* Reconstr.yelles can do it. Reason: different cost model *)
  hammer.
Qed.
*)

Lemma leb_1 : forall m n : nat, PeanoNat.Nat.leb m n = true <-> m <= n.
Proof.
  hammer.
Qed.

Lemma leb_2 : forall m n : nat, PeanoNat.Nat.leb m n = false <-> m > n.
Proof.
  hammer.
Qed.

Lemma in_int_lt2 : forall p q r : nat, Between.in_int p q r -> q >= p /\ r >= p /\ r <= q.
Proof.
  hammer.
Qed.

Lemma nat_compare_eq : forall n m : nat, PeanoNat.Nat.compare n m = Eq <-> n = m.
Proof.
  hammer.
Qed.
