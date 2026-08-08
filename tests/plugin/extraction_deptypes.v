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

Lemma beq_true_eq : forall n m, beq n m = true -> n = m.
Proof. intros n m H; unfold beq in H; destruct (Nat.eq_dec n m); congruence. Qed.

Lemma beq_eq_true : forall n m, n = m -> beq n m = true.
Proof. intros n m H; subst; unfold beq; destruct (Nat.eq_dec m m); congruence. Qed.

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

Lemma idiv_small_unfold : forall a b p, b <> 0 -> a < b -> idiv a b p = 0.
Proof.
  intros a b p _ Hlt.
  unfold idiv, idiv_func.
  rewrite fix_sub_eq.
  - simpl.
    destruct (le_lt_dec b a); lia.
  - intros x f g Hfg.
    destruct x as [a0 [b0 p0]].
    simpl.
    destruct (le_lt_dec b0 a0); auto.
Qed.

Lemma no_junk : 2 + 2 = 4.
Proof. hammer. Qed.

Lemma idiv2_decr : forall b a : nat, b <> 0 -> b <= a -> a - b < a.
Proof. hammer. Qed.

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

Lemma idiv2_small_unfold : forall b Hb a, b <> 0 -> a < b -> idiv2 b Hb a = 0.
Proof.
  intros b Hb a _ Hlt.
  unfold idiv2.
  rewrite Corelib.Init.Wf.Fix_eq.
  - destruct (le_lt_dec b a); lia.
  - intros x f g Hfg.
    destruct (le_lt_dec b x); auto.
Qed.

Lemma idiv3_small_unfold : forall b Hb a, b <> 0 -> a < b -> idiv3 b Hb a = 0.
Proof.
  intros b Hb a _ Hlt.
  unfold idiv3.
  rewrite <- Corelib.Init.Wf.Fix_F_eq.
  destruct (le_lt_dec b a); lia.
Qed.

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
Proof. hammer. Qed.

Lemma extraction_posnat_payload : forall p : posnat, 0 < pval p.
Proof. hammer. Qed.

Lemma extraction_beq_correct : forall n m, beq n m = true <-> n = m.
Proof. hammer [beq_true_eq beq_eq_true]. Qed.

Lemma extraction_between_low : forall n, n <= proj1_sig (sig_of_sig2 (between n)).
Proof. hammer. Qed.

(* The prod-with-Prop translation shape is pinned at the ATP level in
   extraction_transl.v.  This goal is still proved through the hammer entry
   point; allow hammer's initial reconstruction pass for this tiny projection
   lemma rather than using a direct Coq proof. *)
Set Hammer SAutoLimit 1.
Lemma extraction_tag_fst : forall n, fst (tag n) = n.
Proof. hammer. Qed.
Set Hammer SAutoLimit 0.

Lemma extraction_vhead_cons : forall A n (x : A) (v : Vector.t A n), vhead (Vector.cons A x n v) = x.
Proof. hammer. Qed.

Lemma extraction_refinement_hyp : forall s : {u : nat | 0 < u}, 1 <= proj1_sig s.
Proof. intros [u Hu]; exact Hu. Qed.

Lemma extraction_h_exists :
  forall x y z p, exists u, proj1_sig (h x y z p) = u /\ x = u.
Proof. hammer. Qed.

Lemma extraction_idiv_small : forall a b p, b <> 0 -> a < b -> idiv a b p = 0.
Proof. hammer [idiv_small_unfold]. Qed.

Lemma extraction_idiv2_small : forall b Hb a, b <> 0 -> a < b -> idiv2 b Hb a = 0.
Proof. hammer [idiv2_small_unfold]. Qed.

Lemma extraction_idiv3_small : forall b Hb a, b <> 0 -> a < b -> idiv3 b Hb a = 0.
Proof. hammer [idiv3_small_unfold]. Qed.

(* Type-level function scrutinees.  A scrutinee's declared type need only be
   *convertible* to an application of the matched family: [dres dred n] reduces
   to [dtree n] but is not syntactically an application of [dtree].  Reading the
   index arguments off the declared type would hand [dres]'s own arguments to
   [dtree], whose single index would then be matched against [dred].  This is
   the shape Equations produces for a type-level function returning a different
   family per branch; Equations is not available to this suite, so the function
   is spelled as the plain match Equations compiles it to.  The emitted index
   guards are pinned in extraction_transl.v. *)
Inductive dcolor := dred | dblack.

Inductive dtree : nat -> Set :=
| dleaf : dtree 0
| dnode : forall n, nat -> dtree n -> dtree (S n).

Inductive dpair : nat -> Set :=
| dpack : forall n, nat -> nat -> dpair n.

Definition dres (c : dcolor) (n : nat) : Set :=
  match c with dred => dtree n | dblack => dpair n end.

Definition dsize {n} (r : dres dred n) : nat :=
  match r with
  | dleaf => 0
  | dnode m _ _ => S m
  end.

(* The same hazard without the arity mismatch that makes it loud: [dswap] takes
   exactly as many arguments as [dbox]'s telescope, only permuted, so a
   declared-type reading produces a well-formed guard relating [dbox]'s index to
   [dswap]'s colour argument instead. *)
Inductive dbox (c : dcolor) : nat -> Set :=
| dbox_zero : dbox c 0
| dbox_succ : forall n, dbox c n -> dbox c (S n).

Definition dswap (n : nat) (c : dcolor) : Set := dbox c n.

Definition dheight {n} (b : dswap n dred) : nat :=
  match b with
  | dbox_zero _ => 0
  | dbox_succ _ m _ => S m
  end.

(* A type-level function the head-normalizer cannot see through: it is a
   fixpoint, and fixpoint unfolding is deliberately not one of the head steps
   taken.  Rocq's own conversion still accepts the match, so the case is
   translatable in principle -- but its index guard is not computable, and an
   unguarded branch equation would be asserted for every index.  The case must
   therefore be refused outright, leaving [dstack_size] uninterpreted. *)
Fixpoint dstack (k n : nat) : Set :=
  match k with
  | 0 => dtree n
  | S k' => dstack k' n
  end.

Definition dstack_size (n : nat) (r : dstack 0 n) : nat :=
  match r with
  | dleaf => 0
  | dnode m _ _ => S m
  end.

(* The same hazard on an *index-free* family, where it is reached through the
   type of the case rather than through its index guard.  [dopt dred (dtree 0)]
   reduces to [option (dtree 0)]; [option] declares no indices, so no guard is
   read off the scrutinee's type -- but the type of the inner match is still
   computed by applying its return predicate to the index arguments, and
   [dopt]'s surplus colour argument is not one.  The inner match is the
   scrutinee of an outer match on an indexed family, whose own scrutinee type
   only that computation can supply. *)
Definition dopt (c : dcolor) (A : Type) : Type := option A.

Definition dnested (o : dopt dred (dtree 0)) : nat :=
  match (match o with Some t => t | None => dleaf end) with
  | dleaf => 0
  | dnode m _ _ => S m
  end.

Lemma extraction_dsize_leaf : dsize dleaf = 0.
Proof. hammer. Qed.

Lemma extraction_dsize_node :
  forall n (x : nat) (t : dtree n), dsize (dnode n x t) = S n.
Proof. hammer. Qed.

Lemma extraction_dheight_succ :
  forall n (b : dbox dred n), dheight (dbox_succ dred n b) = S n.
Proof. hammer. Qed.

Set Hammer ATPLimit 5.
Lemma canary : False.
Proof. Fail hammer. Abort.
