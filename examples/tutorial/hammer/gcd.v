From Hammer Require Import Tactics.
From Hammer Require Import Hammer. (* for `hammer` *)
Require Import Program.
Require Import Arith.
Require Import Lia.

(* Is "d" a common divisor of "a" and "b"? *)
Definition is_cd d a b :=
  a mod d = 0 /\ b mod d = 0.
(* Is "d" the greatest common divisor of "a" and "b"? *)
Definition is_gcd d a b :=
  is_cd d a b /\ forall d', is_cd d' a b -> d' <= d.

Lemma lem_gcd_step : forall a b d,
    b <> 0 -> is_gcd d b (a mod b) -> is_gcd d a b.
Proof.
  unfold is_gcd, is_cd.
  intros a b d Hb.
  sintuition.
  - destruct (Nat.eq_dec d 0) as [Hd|Hd].
    + subst; reflexivity.
    + assert (Hc1: exists c1, b = d * c1).
      { (* hammer. *) strivial use: Nat.mod_divides. }
      assert (Hc2: exists c2, a mod b = d * c2).
      { (* hammer. *) strivial use: Nat.mod_divides. }
      assert (Hc3: exists c3, a = b * c3 + a mod b).
      { (* hammer. *) srun eauto use: Nat.div_mod. }
      clear -Hc1 Hc2 Hc3 Hd.
      destruct Hc1 as [c1 H1].
      destruct Hc2 as [c2 H2].
      destruct Hc3 as [c3 H3].
      subst.
      rewrite H2 in H3.
      subst.
      assert (H: d * c1 * c3 + d * c2 = (c1 * c3 + c2) * d) by lia.
      rewrite H.
      auto using Nat.mod_mul.
  - enough ((a mod b) mod d' = 0) by auto.
    destruct (Nat.eq_dec d' 0) as [Hd|Hd].
    + subst; reflexivity.
    + assert (Hc1: exists c1, b = d' * c1) by hauto use: Nat.mod_divides.
      assert (Hc2: exists c2, a = d' * c2) by hauto use: Nat.mod_divides.
      assert (Hc3: exists c3, a = b * c3 + a mod b).
      { exists (a / b); auto using Nat.div_mod. }
      clear -Hc1 Hc2 Hc3 Hd Hb.
      destruct Hc1 as [c1 H1].
      destruct Hc2 as [c2 H2].
      destruct Hc3 as [c3 H3].
      subst.
      (* hammer. *)
      clear - Hb Hd.
      (* Coq.Arith.PeanoNat.Nat.mod_mul,
      Coq.Arith.PeanoNat.Nat.mul_mod_distr_l,
      Coq.Arith.PeanoNat.Nat.mul_comm *)
      rewrite Nat.mul_mod_distr_l; [| lia | lia ].
      rewrite Nat.mul_comm.
      apply Nat.mod_mul; assumption.
Qed.

Program Fixpoint gcd (a b : nat) {measure b} :
  {d : nat | a + b > 0 -> is_gcd d a b} :=
  match b with
  | 0 => a
  | _ => gcd b (a mod b)
  end.
Next Obligation.
  unfold is_gcd, is_cd.
  sintuition.
  - (* hammer. *)
    sfirstorder use: Nat.mod_same.
  - (* hammer. *)
    (* time sauto. *)
    (* Set Hammer SAutoLimit 0.
    hammer. *)
    sfirstorder use: Nat.mod_0_l.
  - (* hammer. *)
    qauto use: Nat.add_pos_cases, Nat.le_gt_cases,
               Nat.mod_small, Nat.neq_0_lt_0.
Qed.
Next Obligation.
  (* hammer. *)
  srun eauto use: Nat.mod_upper_bound.
Qed.
Next Obligation.
  simpl_sigma.
  (* hammer. *)
  apply lem_gcd_step; [ lia | apply i; lia ].
Qed.

Check gcd.
Compute ` (gcd 2 3).
Compute ` (gcd 5 15).
Compute ` (gcd 20 15).
Compute ` (gcd 2424 1542).
