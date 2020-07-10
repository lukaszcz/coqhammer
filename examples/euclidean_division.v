(* This file demonstrates the use of the `hammer` tactic to find
   lemmas about real number in the standard library. All tactics with
   the `use:` option have been obtained by invoking `hammer`. *)

(* From Hammer Require Import Hammer. *)
From Hammer Require Import Tactics.

Require Import Reals.
Require Import Lra.

Local Open Scope Z_scope.
Local Open Scope R_scope.

Lemma euclidean_division :
  forall x y:R,
    y <> 0 ->
    exists k : Z, (exists r : R, x = IZR k * y + r /\ 0 <= r < Rabs y).
Proof.
  unfold not; intros x y H.
  assert (H0: y > 0 \/ y <= 0).
  { hecrush use: @Rtotal_order unfold: Rle. }
  destruct H0 as [H0|H0].
  - pose (k := (up (x / y) - 1)%Z).
    exists k.
    exists (x - IZR k * y).
    assert (HH: IZR k = IZR (up (x / y)) - 1).
    { assert (IZR k = IZR (up (x / y)) - IZR 1%Z).
      { qauto use: @Z_R_minus. }
      sauto. }
    rewrite HH; clear HH.
    clear k.
    split.
    + qauto use: RIneq.Rplus_minus.
    + assert (HH: x - (IZR (up (x / y)) - 1) * y = x - IZR (up (x / y)) * y + y) by lra.
      rewrite HH; clear HH.
      split.
      * assert (IZR (up (x / y)) * y <= y + x).
        { assert (IZR (up (x / y)) <= 1 + (x / y)).
          { generalize (archimed (x / y)); sintuition.
            assert (IZR (up (x / y)) - (x / y) + (x / y) <= 1 + (x / y)).
            { qauto use: @Rplus_le_compat_r. }
            qauto use: Rplus_opp_l, Rplus_assoc, Rplus_0_r unfold: Rdefinitions.Rminus. }
          assert (IZR (up (x / y)) * y <= (1 + x / y) * y) by sauto.
          assert (IZR (up (x / y)) * y <= y + ((x / y) * y)).
          { qauto use: @Rmult_1_l, @Rmult_plus_distr_r. }
          hfcrush use: @Rmult_1_r, @Rmult_assoc, @Rinv_l_sym unfold: Rdiv. }
        lra.
      * assert (IZR (up (x / y)) * y > x).
        { assert (IZR (up (x / y)) > x / y).
          { hauto use: @archimed. }
          assert (IZR (up (x / y)) * y > (x / y) * y).
          { hauto use: @Rmult_gt_compat_r. }
          hfcrush use: @Rmult_1_r, @Rmult_assoc, @Rmult_comm, @Rinv_r_sym unfold: Rdiv. }
        assert (HH: Rabs y = y).
        { (* Unset Hammer CVC4. hammer. *)
          (* If you get an unreconstructible proof, it might help to
             disable the prover which found it. *)
          hauto ered: off use: @Rlt_asym unfold: Rabs, Rgt. }
        rewrite HH; clear HH.
        lra.
  - pose (k := (1 - up (x / -y))%Z).
    exists k.
    exists (x - IZR k * y).
    assert (HH: IZR k = 1 - IZR (up (x / -y))).
    { assert (IZR k = IZR 1 - IZR (up (x / -y))).
      { hauto ered: off use: @Z_R_minus unfold: Rminus, BinIntDef.Z.sub, Rdiv. }
      sauto. }
    rewrite HH; clear HH.
    clear k.
    split.
    + qauto use: @Rplus_minus.
    + assert (HH: x - (1 - IZR (up (x / - y))) * y = x - y + IZR (up (x / -y)) * y) by lra.
      rewrite HH; clear HH.
      split.
      * assert (IZR (up (x / -y)) * y >= y - x).
        { assert (IZR (up (x / -y)) <= 1 + (x / -y)).
          { generalize (archimed (x / -y)); sintuition.
            assert (IZR (up (x / -y)) - (x / -y) + (x / -y) <= 1 + (x / -y)).
            { hauto use: @Rplus_comm, @Rplus_le_compat_l. }
            hcrush use: @Rplus_opp_l, @Rplus_assoc, @Rplus_0_r unfold: Rminus, Rmax. }
          assert (y < 0) by sauto.
          assert (IZR (up (x / - y)) * y >= y + (x / - y) * y).
          { assert (IZR (up (x / - y)) * (-y) <= (1 + (x / - y)) * (-y)).
            { hauto use: @Ropp_0_ge_le_contravar, @Rmult_le_compat_r, @RIneq.Rle_ge. }
            assert (HH: IZR (up (x / - y)) * (-y) = - (IZR (up (x / - y)) * y)) by lra.
            rewrite HH in *; clear HH.
            assert (HH: (1 + (x / - y)) * (-y) = - (y + (x / -y) * y)) by lra.
            rewrite HH in *; clear HH.
            hfcrush use: @Rle_ge, @Ropp_le_cancel unfold: Rle, Rge, Rgt. }
          assert (HH: y + x / - y * y = y - x).
          { assert (x / - y * - y = x).
            { assert (HH1: - y > 0) by lra.
              assert (HH2: forall u, u <> 0 -> (x / u) * u = x).
              { hfcrush use: @Rinv_l_sym, @Rmult_1_r, @Rmult_assoc unfold: Rdiv. }
              (* Unset Hammer CVC4. hammer. *)
              qauto use: @Ropp_gt_cancel, @atan_right_inv, @Rgt_not_eq unfold: atan, Rdiv. }
            qauto use: @Ropp_involutive, @Ropp_mult_distr_r_reverse unfold: Rminus. }
          rewrite HH in *; clear HH.
          sauto. }
        lra.
      * assert (HH: Rabs y = -y).
        { qauto use: @Rabs_left1. }
        rewrite HH; clear HH.
        assert (IZR (up (x / -y)) * y < -x).
        { assert (IZR (up (x / -y)) > x / -y).
          { hfcrush use: @archimed. }
          assert (IZR (up (x / -y)) * -y > (x / -y) * -y).
          { hauto ered: off use: @Rlt_irrefl, @Rmult_gt_compat_r, @Rabs_pos, @Rabs_pos_lt, @Rle_lt_trans unfold: Rabs, Rle, Rgt. }
          assert (HH: x / - y * - y = x).
          { assert (- y <> 0).
            { hauto use: @Rplus_0_r, @Rplus_opp_r. }
            assert (forall u, u <> 0 -> (x / u) * u = x).
            { hfcrush use: @Rmult_1_r, @Rinv_l_sym, @Rmult_assoc unfold: Rdiv. }
            sauto. }
          rewrite HH in *; clear HH.
          lra. }
        lra.
Qed.
