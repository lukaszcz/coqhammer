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
From Hammer Require Reconstr.

(************************************************************************************************)

Require Import Arith.

(* disable the preliminary crush-like tactic *)
Set Hammer CrushLimit 0.

Lemma lem_1 : le 1 2.
  hammer. Restart.
  hauto using (@Arith.PeanoNat.Nat.lt_0_2) unfolding (@Init.Peano.lt).
Qed.

Lemma lem_2 : forall n : nat, Nat.Odd n \/ Nat.Odd (n + 1).
  hammer. Restart.
  hauto 200 using (@Arith.PeanoNat.Nat.add_1_r, @Arith.PeanoNat.Nat.Odd_succ, @Arith.PeanoNat.Nat.Even_or_Odd).
Qed.

Lemma lem_2_1 : forall n : nat, Nat.Even n \/ Nat.Even (n + 1).
  hammer. Restart.
  hauto 200 using (@Arith.PeanoNat.Nat.Even_or_Odd, @Arith.PeanoNat.Nat.Even_succ, @Arith.PeanoNat.Nat.add_1_r).
Qed.

Lemma lem_3 : le 2 3.
  hammer. Restart.
  hauto using (@Arith.PeanoNat.Nat.le_le_succ_r, @Arith.PeanoNat.Nat.lt_1_2) unfolding (@Init.Peano.lt).
Qed.

Lemma lem_4 : le 3 10.
  time hammer. Restart.
  hauto 200 using (@Arith.PeanoNat.Nat.le_1_r, @Arith.PeanoNat.Nat.le_gt_cases, @Arith.PeanoNat.Nat.succ_inj_wd, @Arith.PeanoNat.Nat.succ_le_mono) unfolding (@Init.Peano.lt).
Qed.

Lemma mult_1 : forall m n k : nat, m * n + k = k + n * m.
Proof.
  hammer. Restart.
  hauto using (@Arith.PeanoNat.Nat.add_comm, @Arith.PeanoNat.Nat.mul_comm).
Qed.

Lemma lem_rew : forall m n : nat, 1 + n + m + 1 = m + 2 + n.
Proof.
  time hammer. Restart.
  hauto using (@Arith.PeanoNat.Nat.add_assoc, @Arith.PeanoNat.Nat.add_comm, @Arith.PeanoNat.Nat.add_1_r, @Arith.PeanoNat.Nat.add_shuffle1).
Qed.

Lemma lem_pow : forall n : nat, 3 * 3 ^ n = 3 ^ (n + 1).
Proof.
  hammer. Restart.
  hauto using (@Arith.PeanoNat.Nat.pow_succ_r, @Arith.PeanoNat.Nat.add_1_r, @Arith.PeanoNat.Nat.le_0_l).
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
  hauto using (@ZArith.BinInt.Z.ge_le, @ZArith.BinInt.Z.max_lub).
Qed.

Require Reals.

Lemma lem_iso : forall x1 y1 x2 y2 theta : Rdefinitions.R,
    Rgeom.dist_euc x1 y1 x2 y2 =
    Rgeom.dist_euc (Rgeom.xr x1 y1 theta) (Rgeom.yr x1 y1 theta) (Rgeom.xr x2 y2 theta)
                   (Rgeom.yr x2 y2 theta).
Proof.
  hammer. Restart.
  hauto using (@Reals.Rgeom.isometric_rotation).
Qed.

Require Import List.

Lemma lem_lst :
  forall {A} (x : A) l1 l2 (P : A -> Prop),
    In x (l1 ++ l2) -> (forall y, In y l1 -> P y) -> (forall y, In y l2 -> P y) ->
    P x.
Proof.
  hammer. Restart.
  hauto using (@Lists.List.in_app_iff).
  (* `firstorder with datatypes' does not work *)
Qed.

Lemma lem_lst2 : forall {A} (y1 y2 y3 : A) l l' z, In z l \/ In z l' ->
                                                   In z (y1 :: y2 :: l ++ y3 :: l').
Proof.
  hammer. Restart.
  sauto using (@Lists.List.in_cons, @Lists.List.not_in_cons, @Lists.List.in_or_app).
  (* `firstorder with datatypes' does not work *)
Qed.

Lemma lem_lst3 : forall {A} (l : list A), length (tl l) <= length l.
Proof.
  hammer. Restart.
  hauto using (@Arith.PeanoNat.Nat.le_0_l, @Init.Peano.le_S, @Init.Peano.le_n) unfolding (@Init.Datatypes.length, @Lists.List.tl).
Qed.

Require NArith.Ndec.

Lemma Nleb_alt :
  forall b a c : BinNums.N, Ndec.Nleb b c = BinNat.N.leb b c /\ Ndec.Nleb a b = BinNat.N.leb a b.
Proof.
  hammer. Restart.
  hauto using (@NArith.Ndec.Nleb_alt).
Qed.

Require NArith.BinNat.

Lemma setbit_iff : forall m a n : BinNums.N,
                     n = m \/ true = BinNat.N.testbit a m <->
                     BinNat.N.testbit (BinNat.N.setbit a n) m = true.
Proof.
  hammer. Restart.
  hauto using (@NArith.BinNat.N.setbit_iff).
Qed.

Lemma in_int_p_Sq : forall r p q a : nat, a >= 0 ->
                      Between.in_int p (S q) r -> Between.in_int p q r \/ r = q \/ a = 0.
Proof.
  hammer. Restart.
  hauto using (@Arith.Between.in_int_p_Sq).
Qed.

Require Reals.Rminmax.

Lemma min_spec_1 : forall n m : Rdefinitions.R,
                   (Rdefinitions.Rle m n /\ Rbasic_fun.Rmin m m = m) \/
                   (Rdefinitions.Rlt n m /\ Rbasic_fun.Rmin m n = n).
Proof.
  hammer. Restart.
  hauto using (@Reals.RIneq.Rnot_le_lt) unfolding (@Reals.Rbasic_fun.Rmin).
Qed.

Lemma min_spec_2 : forall n m : Rdefinitions.R,
                   (Rdefinitions.Rle m n /\ Rbasic_fun.Rmin m n = m) \/
                   (Rdefinitions.Rlt n m /\ Rbasic_fun.Rmin m n = n).
Proof.
  hammer. Restart.
  hauto using (@Reals.RIneq.Rnot_le_lt) unfolding (@Reals.Rbasic_fun.Rmin).
Qed.

Lemma incl_app : forall (A : Type) (n l m : list A),
                   List.incl l n /\ List.incl m n -> List.incl (l ++ m) n.
Proof.
  hammer. Restart.
  hauto using (@Lists.List.incl_app).
Qed.

Require Reals.Rpower.

Lemma exp_Ropp
     : forall x y : Rdefinitions.R,
       Rdefinitions.Rinv (Rtrigo_def.exp x) = Rtrigo_def.exp (Rdefinitions.Ropp x).
Proof.
  hammer. Restart.
  hauto using (@Reals.Rpower.exp_Ropp).
Qed.

Lemma lem_lst_1 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  (* The hammer can't do induction. If induction is necessary to carry out the
  proof, then one needs to start the induction manually. *)
  induction l'.
  - hammer. Undo.
    scrush using (@Lists.List.app_nil_end).
  - hammer. Undo.
    hauto using (@Lists.List.NoDup_remove_1).
Qed.

Lemma NoDup_remove_1
     : forall (A : Type) (a : A) (l' l : list A),
       List.NoDup (l ++ a :: l') ->
       ~ List.In a (l ++ l') /\ List.NoDup (l ++ l') /\ List.NoDup l.
Proof.
  hammer. Restart.
  hauto using (@Lists.List.NoDup_remove, @lem_lst_1).
Qed.

Lemma leb_compare2 : forall m n : nat,
                      PeanoNat.Nat.leb n m = true <->
                      (PeanoNat.Nat.compare n m = Lt \/ PeanoNat.Nat.compare n m = Eq).
Proof.
  (* hammer. Restart. *)
  (* Sometimes the tactics cannot reconstruct the goal, but the
  returned dependencies may still be used to create the proof
  semi-manually. *)
  assert (forall c : Datatypes.comparison, c = Eq \/ c = Lt \/ c = Gt) by sauto.
  time scrush using (Coq.Arith.Compare_dec.leb_correct, Coq.Arith.PeanoNat.Nat.leb_refl, Coq.Arith.PeanoNat.Nat.compare_nge_iff, Coq.Arith.PeanoNat.Nat.lt_eq_cases, Coq.Init.Peano.le_n, Coq.Arith.Compare_dec.leb_compare, Coq.Arith.PeanoNat.Nat.compare_lt_iff).
  (* TODO: inversion axioms giving hints for reconstruction *)
Qed.

Lemma leb_1 : forall m n : nat, PeanoNat.Nat.leb m n = true <-> m <= n.
Proof.
  hammer. Restart.
  hauto using (@Arith.PeanoNat.Nat.leb_le).
Qed.

Lemma leb_2 : forall m n : nat, PeanoNat.Nat.leb m n = false <-> m > n.
Proof.
  hammer. Restart.
  hauto using (@Arith.Compare_dec.leb_correct_conv, @Arith.Compare_dec.leb_iff_conv) unfolding (@Init.Peano.gt).
Qed.

Lemma incl_appl
     : forall (A : Type) (l m n : list A),
       List.incl l n -> List.incl l (n ++ m) /\ List.incl l (m ++ n) /\ List.incl l (l ++ l).
Proof.
  hammer. Restart.
  hauto using (@Lists.List.incl_appl, @Lists.List.incl_appr, @Lists.List.incl_refl).
Qed.

Lemma in_int_lt2 : forall p q r : nat, Between.in_int p q r -> q >= p /\ r >= p /\ r <= q.
Proof.
  hammer. Restart.
  hauto using (@Arith.PeanoNat.Nat.lt_le_incl, @Arith.Between.in_int_lt) unfolding (@Init.Peano.ge, @Arith.Between.in_int).
Qed.

Lemma nat_compare_eq : forall n m : nat, PeanoNat.Nat.compare n m = Eq <-> n = m.
Proof.
  hammer. Restart.
  hauto using (@Arith.PeanoNat.Nat.compare_eq_iff).
Qed.

Lemma Forall_1
     : forall (A : Type) (P : A -> Prop) (a : A),
       forall (l l' : list A), List.Forall P l /\ List.Forall P l' /\ P a -> List.Forall P (l ++ a :: l').
Proof.
  induction l.
  - hammer. Undo.
    hauto using (@Lists.List.app_nil_l, @Lists.List.Forall_cons).
  - (* hammer. Undo. *)
    sauto using (@Coq.Lists.List.Forall_cons).
  Restart.
  induction l; ssimpl.
Qed.
(* Neither the base case nor the inductive step may be solved using 'firstorder with datatypes'. *)

Lemma Forall_impl
     : forall (A : Type) (P : A -> Prop),
       forall l : list A, List.Forall P l -> List.Forall P (l ++ l).
Proof.
  induction l.
  hammer. Undo.
  hauto using (@Lists.List.app_nil_end).
  hammer. Restart.
  scrush using (@Lists.List.app_cons_not_nil, @Lists.List.app_nil_r, @Forall_1).
Qed.
