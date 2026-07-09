From Hammer Require Import Hammer.

From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Arith.Wf_nat Bool.Bool Lia Program.Wf Vectors.Vector.

Set Hammer SAutoLimit 0.

Definition h (x y z : nat) (p : x = y /\ y = z) : {u : nat | x = u} :=
  match p with conj p1 p2 => exist (fun u => x = u) z (eq_trans p1 p2) end.

Definition safe_pred (n : nat) : n <> 0 -> {m : nat | n = S m} :=
  match n return n <> 0 -> {m : nat | n = S m} with
  | 0 => fun p => False_rect _ (p eq_refl)
  | S m => fun _ => exist _ m eq_refl
  end.

Definition tr (P : nat -> Set) (a b : nat) (e : a = b) (x : P a) : P b :=
  eq_rect a P x b e.

(* Pin non-primitive projections: primitive projections would route pval through
   the unsupported $Proj fallback and fail the test for out-of-scope reasons. *)
Unset Primitive Projections.
Record posnat := mkpos { pval : nat ; pval_pos : 0 < pval }.

Definition beq (n m : nat) : bool := if Nat.eq_dec n m then true else false.

Definition between (n : nat) : {m : nat | n <= m & m <= S n} :=
  exist2 _ _ n (le_n n) (le_S _ _ (le_n n)).

Definition tag (n : nat) : nat * (n = n) := (n, eq_refl).

Definition vhead {A n} (v : Vector.t A (S n)) : A :=
  match v with Vector.cons _ x _ _ => x end.

Program Fixpoint idiv (a b : nat) (p : b <> 0) {measure a} : nat :=
  if le_lt_dec b a then S (idiv (a - b) b p) else 0.
Next Obligation.
  lia.
Qed.

Lemma no_junk : 2 + 2 = 4.
Proof. hammer. Qed.

Lemma idiv2_decr : forall b a : nat, b <> 0 -> b <= a -> a - b < a.
Proof. lia. Qed.

Definition idiv2 (b : nat) (Hb : b <> 0) : nat -> nat :=
  Fix lt_wf (fun _ => nat)
    (fun a rec =>
       match le_lt_dec b a with
       | left Hba => S (rec (a - b) (idiv2_decr b a Hb Hba))
       | right _ => 0
       end).

Definition idiv3 (b : nat) (Hb : b <> 0) (a : nat) : nat :=
  Fix_F (fun _ => nat)
    (fun a rec =>
       match le_lt_dec b a with
       | left Hba => S (rec (a - b) (idiv2_decr b a Hb Hba))
       | right _ => 0
       end) (lt_wf a).

Lemma extraction_h_proj : forall x y z p, proj1_sig (h x y z p) = z.
Proof. hammer. Qed.

Lemma extraction_h_spec : forall x y z p, x = proj1_sig (h x y z p).
Proof. hammer. Qed.

Lemma extraction_h_two_specs :
  forall a b c p q, proj1_sig (h a b c p) = proj1_sig (h c b a q) -> a = c.
Proof. hammer. Qed.

Lemma extraction_safe_pred_spec : forall n p, S (proj1_sig (safe_pred n p)) = n.
Proof. hammer. Qed.

Lemma extraction_safe_pred_proof_irrel :
  forall n p q, proj1_sig (safe_pred (S n) p) = proj1_sig (safe_pred (S n) q).
Proof. hammer. Qed.

Lemma extraction_tr_refl : forall (P : nat -> Set) a (e : a = a) x, tr P a a e x = x.
Proof. Fail hammer. Abort.

Lemma extraction_posnat_payload : forall p : posnat, 0 < pval p.
Proof. hammer. Qed.

Lemma extraction_beq_correct : forall n m, beq n m = true <-> n = m.
Proof. Fail hammer. Abort.

Lemma extraction_between_low : forall n, n <= proj1_sig (sig_of_sig2 (between n)).
Proof. hammer. Qed.

Lemma extraction_tag_fst : forall n, fst (tag n) = n.
Proof. hammer. Qed.

Lemma extraction_vhead_cons : forall A n (x : A) (v : Vector.t A n), vhead (Vector.cons A x n v) = x.
Proof. hammer. Qed.

Lemma extraction_refinement_hyp : forall s : {u : nat | 0 < u}, 1 <= proj1_sig s.
Proof. hammer. Qed.

Lemma extraction_h_exists :
  forall x y z p, exists u, proj1_sig (h x y z p) = u /\ x = u.
Proof. hammer. Qed.

Lemma extraction_idiv_small : forall a b p, b <> 0 -> a < b -> idiv a b p = 0.
Proof. Fail hammer. Abort.

Lemma extraction_idiv2_small : forall b Hb a, b <> 0 -> a < b -> idiv2 b Hb a = 0.
Proof. Fail hammer. Abort.

Lemma extraction_idiv3_small : forall b Hb a, b <> 0 -> a < b -> idiv3 b Hb a = 0.
Proof. Fail hammer. Abort.

Set Hammer ATPLimit 5.
Lemma canary : False.
Proof. Fail hammer. Abort.
