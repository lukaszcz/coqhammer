(* This file showcases hammer usage. Most of the problems here are
simple modifications of lemmas present in the standard library
(e.g. by changing the order of quantifiers or premises, duplicating
some premises, changing function argument order, changing the
conclusion to an equivalent one, etc) or a combination of a few
lemmas.

The calls to the "hammer" tactic are left here only for illustrative
purposes. Because the success of the hammer is not guaranteed to be
reproducible, in the final scripts "hammer" should be replaced with an
appropriate reconstruction tactic.
*)

From Hammer Require Import Hammer.

(*********************************************************************************************)

(*
Lemma lem_classic : forall P : Prop, P \/ ~P.
Proof.
  hammer.
Qed. *)

Require Import Arith.

(* disable the preliminary sauto tactic *)
Set Hammer SAutoLimit 0.

Lemma lem_1 : le 1 2.
  hammer. Restart.
  scongruence use: Nat.lt_0_2 unfold: lt.
Qed.

Lemma lem_2 : forall n : nat, Nat.Odd n \/ Nat.Odd (n + 1).
  hammer. Restart.
  hauto lq: on use: Nat.Even_or_Odd, Nat.add_1_r, Nat.Odd_succ.
Qed.

Lemma lem_2_1 : forall n : nat, Nat.Even n \/ Nat.Even (n + 1).
  hammer. Restart.
  hauto lq: on use: Nat.add_1_r, Nat.Even_or_Odd, Nat.Even_succ.
Qed.

Lemma lem_3 : le 2 3.
  hammer. Restart.
  srun eauto use: Nat.le_succ_diag_r unfold: Init.Nat.two.
Qed.

Lemma lem_4 : le 3 10.
  hammer. Restart.
  sfirstorder use: Nat.nle_succ_0, Nat.le_gt_cases, Nat.lt_succ_r, Nat.succ_le_mono, Nat.log2_up_2 unfold: Init.Nat.two.
Qed.

Lemma mult_1 : forall m n k : nat, m * n + k = k + n * m.
Proof.
  hammer. Restart.
  scongruence use: Nat.mul_comm, Nat.add_comm.
Qed.

Lemma lem_rew : forall m n : nat, 1 + n + m + 1 = m + 2 + n.
Proof.
  hammer. Restart.
  strivial use: Nat.add_comm, Nat.add_1_r, Nat.add_shuffle1, Nat.add_assoc.
Qed.

Lemma lem_pow : forall n : nat, 3 * 3 ^ n = 3 ^ (n + 1).
Proof.
  hammer. Restart.
  qauto use: Nat.pow_succ_r, Nat.le_0_l, Nat.add_1_r.
Qed.

Require Coq.Reals.RIneq.
Require Coq.Reals.Raxioms.
Require Coq.Reals.Rtrigo1.

Lemma cos_decreasing_1 :
  forall y x : Rdefinitions.R,
    Rdefinitions.Rlt x y ->
    Rdefinitions.Rle x Rtrigo1.PI ->
    Rdefinitions.Rge y Rdefinitions.R0 ->
    Rdefinitions.Rle y Rtrigo1.PI ->
    Rdefinitions.Rge x Rdefinitions.R0 ->
    Rdefinitions.Rlt (Rtrigo_def.cos y) (Rtrigo_def.cos x).
Proof.
  (* hammer. Restart. *)
  hauto using (@Reals.Rtrigo1.cos_decreasing_1, @Reals.RIneq.Rge_le).
Qed.

Require ZArith.BinInt.

Lemma max_lub : forall m p k n : BinNums.Z,
                  BinInt.Z.ge p m -> BinInt.Z.le n p -> BinInt.Z.le (BinInt.Z.max n m) p.
Proof.
  hammer. Restart.
  srun eauto use: BinInt.Z.max_lub, BinInt.Z.ge_le.
Qed.

Require Reals.

Lemma lem_iso : forall x1 y1 x2 y2 theta : Rdefinitions.R,
    Rgeom.dist_euc x1 y1 x2 y2 =
    Rgeom.dist_euc (Rgeom.xr x1 y1 theta) (Rgeom.yr x1 y1 theta) (Rgeom.xr x2 y2 theta)
                   (Rgeom.yr x2 y2 theta).
Proof.
  hammer. Restart.
  scongruence use: Rgeom.isometric_rotation.
Qed.

Require Import List.

Lemma lem_lst :
  forall {A} (x : A) l1 l2 (P : A -> Prop),
    In x (l1 ++ l2) -> (forall y, In y l1 -> P y) -> (forall y, In y l2 -> P y) ->
    P x.
Proof.
  hammer. Restart.
  qauto use: in_app_iff.
  (* `firstorder with datatypes' does not work *)
Qed.

Lemma lem_lst2 : forall {A} (y1 y2 y3 : A) l l' z, In z l \/ In z l' ->
                                                   In z (y1 :: y2 :: l ++ y3 :: l').
Proof.
  hammer. Restart.
  hauto lq: on use: in_app_iff, in_or_app, not_in_cons, in_cons, Add_in unfold: app.
  (* `firstorder with datatypes' does not work *)
Qed.

Lemma lem_lst3 : forall {A} (l : list A), length (tl l) <= length l.
Proof.
  hammer. Restart.
  qauto use: le_S, Nat.le_0_l, le_n unfold: tl, length.
Qed.

Require NArith.Ndec.

Lemma Nleb_alt :
  forall b a c : BinNums.N, Ndec.Nleb b c = BinNat.N.leb b c /\ Ndec.Nleb a b = BinNat.N.leb a b.
Proof.
  hammer. Restart.
  srun eauto use: Ndec.Nleb_alt.
Qed.

Require NArith.BinNat.

Lemma setbit_iff : forall m a n : BinNums.N,
                     n = m \/ true = BinNat.N.testbit a m <->
                     BinNat.N.testbit (BinNat.N.setbit a n) m = true.
Proof.
  hammer. Restart.
  hfcrush use: BinNat.N.setbit_iff.
Qed.

Lemma in_int_p_Sq : forall r p q a : nat, a >= 0 ->
                      Between.in_int p (S q) r -> Between.in_int p q r \/ r = q \/ a = 0.
Proof.
  hammer. Restart.
  hauto lq: on use: in_int_p_Sq.
Qed.

Require Reals.Rminmax.

Lemma min_spec_1 : forall n m : Rdefinitions.R,
                   (Rdefinitions.Rle m n /\ Rbasic_fun.Rmin m m = m) \/
                   (Rdefinitions.Rlt n m /\ Rbasic_fun.Rmin m n = n).
Proof.
  hammer. Restart.
  hauto use: RIneq.Rnot_le_lt unfold: Rbasic_fun.Rmin.
Qed.

Lemma min_spec_2 : forall n m : Rdefinitions.R,
                   (Rdefinitions.Rle m n /\ Rbasic_fun.Rmin m n = m) \/
                   (Rdefinitions.Rlt n m /\ Rbasic_fun.Rmin m n = n).
Proof.
  hammer. Restart.
  hauto use: RIneq.Rnot_le_lt unfold: Rbasic_fun.Rmin.
Qed.

Lemma incl_app : forall (A : Type) (n l m : list A),
                   List.incl l n /\ List.incl m n -> List.incl (l ++ m) n.
Proof.
  hammer. Restart.
  strivial use: incl_app.
Qed.

Require Reals.Rpower.

Lemma exp_Ropp
     : forall x y : Rdefinitions.R,
       Rdefinitions.Rinv (Rtrigo_def.exp x) = Rtrigo_def.exp (Rdefinitions.Ropp x).
Proof.
  hammer. Restart.
  srun eauto use: Rpower.exp_Ropp.
Qed.

Lemma lem_lst_1 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  (* The hammer can't do induction. If induction is necessary to carry out the
  proof, then one needs to start the induction manually. *)
  induction l'.
  - hammer. Undo.
    scongruence use: app_nil_end.
  - hammer. Undo.
    srun eauto use: NoDup_remove_1.
Qed.

Lemma NoDup_remove_2
     : forall (A : Type) (a : A) (l' l : list A),
       List.NoDup (l ++ a :: l') ->
       ~ List.In a (l ++ l') /\ List.NoDup (l ++ l') /\ List.NoDup l.
Proof.
  hammer. Restart.
  strivial use: lem_lst_1, NoDup_remove.
Qed.

Lemma leb_compare2 : forall m n : nat,
                      PeanoNat.Nat.leb n m = true <->
                      (PeanoNat.Nat.compare n m = Lt \/ PeanoNat.Nat.compare n m = Eq).
Proof.
  (* hammer. Restart. *)
  (* Sometimes the tactics cannot reconstruct the goal, but the
  returned dependencies may still be used to create the proof
  semi-manually. *)
  assert (forall c : Datatypes.comparison, c = Eq \/ c = Lt \/ c = Gt) by sauto inv: Datatypes.comparison.
  hauto erew: off use: Compare_dec.leb_compare.
Qed.

Lemma leb_1 : forall m n : nat, PeanoNat.Nat.leb m n = true <-> m <= n.
Proof.
  hammer. Restart.
  srun eauto use: Nat.leb_le, Nat.leb_nle, leb_correct, leb_complete.
Qed.

Lemma leb_2 : forall m n : nat, PeanoNat.Nat.leb m n = false <-> m > n.
Proof.
  hammer. Restart.
  srun eauto use: leb_iff_conv, leb_correct_conv unfold: gt.
Qed.

Lemma incl_appl_1
     : forall (A : Type) (l m n : list A),
       List.incl l n -> List.incl l (n ++ m) /\ List.incl l (m ++ n) /\ List.incl l (l ++ l).
Proof.
  hammer. Restart.
  strivial use: incl_appl, incl_refl, incl_appr.
Qed.

Lemma in_int_lt2 : forall p q r : nat, Between.in_int p q r -> q >= p /\ r >= p /\ r <= q.
Proof.
  hammer. Restart.
  sfirstorder use: Nat.lt_le_incl, in_int_lt unfold: ge, in_int.
Qed.

Lemma nat_compare_eq : forall n m : nat, PeanoNat.Nat.compare n m = Eq <-> n = m.
Proof.
  hammer. Restart.
  srun eauto use: Nat.compare_eq_iff.
Qed.

Lemma Forall_1
     : forall (A : Type) (P : A -> Prop) (a : A),
       forall (l l' : list A), List.Forall P l /\ List.Forall P l' /\ P a -> List.Forall P (l ++ a :: l').
Proof.
  induction l.
  - hammer. Undo.
    strivial use: app_nil_l, Forall_cons.
  - (* hammer. Undo. *)
    sauto use: Forall_cons.
  Restart.
  induction l; qsimpl.
Qed.
(* Neither the base case nor the inductive step may be solved using 'firstorder with datatypes'. *)

Lemma Forall_impl
     : forall (A : Type) (P : A -> Prop),
       forall l : list A, List.Forall P l -> List.Forall P (l ++ l).
Proof.
  induction l.
  - hammer. Undo.
    srun eauto use: app_nil_end.
  - hammer. Undo.
    qauto use: Forall_inv, Forall_inv_tail, Forall_1.
Qed.

Lemma minus_neq_O : forall n i:nat, (i < n) -> (n - i) <> 0.
Proof.
  hammer. Undo.
  srun eauto use: Nat.sub_gt.
Qed.
