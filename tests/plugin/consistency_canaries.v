(* ATP-level consistency canaries for the extraction-factored translation plan.
   Each goal is dumped with Hammer_dump; check-consistency.sh replaces the
   conjecture by $false and asks ATPs to ensure the selected axiom set is not
   already inconsistent. *)

From Hammer Require Import Hammer.

From Stdlib Require Import Arith.PeanoNat Strings.String Vectors.Fin.

Require Import extraction_deptypes.

Open Scope string_scope.

Set Hammer SAutoLimit 0.
Set Hammer Predictions 1024.

Definition prop_or_match (P Q : Prop) (h : P \/ Q) : P \/ Q :=
  match h with
  | or_introl p => or_introl p
  | or_intror q => or_intror q
  end.

Definition false_case_prop (h : False) : Prop :=
  match h with end.

(* An index-blind expansion of [reflect] in a negative guard is unsound.
   Keep both polarities in separate dumps: the result type of
   [reflect_positive_canary] puts [reflect P true] in positive position, while
   [reflect_negative_canary]'s argument puts [reflect P b] in negative
   position.  Their typing axioms retain these expansions after the checker
   replaces the conjecture by [$false]. *)
Definition reflect_negative_canary
    (P : Prop) (b : bool) (r : reflect P b) : bool :=
  match r with
  | ReflectT _ _ => true
  | ReflectF _ _ => false
  end.

Definition reflect_positive_canary
    (P : Prop) (p : P) : reflect P true :=
  ReflectT _ p.

Goal
    (forall (P Q : Prop) (h : P \/ Q), prop_or_match P Q h = h) /\
    (forall (P : Prop) b (r : reflect P b),
        reflect_negative_canary P b r = b).
  hammer_dump "consistency-prop-or-match.p".
Abort.

Goal
    (forall h : False, false_case_prop h) /\
    (forall (P : Prop) (p : P),
        reflect_positive_canary P p = ReflectT _ p).
  hammer_dump "consistency-false-case-prop.p".
Abort.

Goal forall a b p, b <> 0 -> a < b -> idiv a b p = 0.
  hammer_dump "consistency-idiv.p".
Abort.

Goal forall b Hb a, b <> 0 -> a < b -> idiv2 b Hb a = 0.
  hammer_dump "consistency-idiv2.p".
Abort.

Goal forall b Hb a, b <> 0 -> a < b -> idiv3 b Hb a = 0.
  hammer_dump "consistency-idiv3.p".
Abort.

(* An indexed refinement at index zero has the refutable payload [k < 0].
   The projection's typing axiom expands that payload, and the empty-instance
   eliminator ensures the dump also retains the negative occurrence. *)
Inductive canary_ibounded : nat -> Set :=
| CanaryIBounded : forall n k, k < n -> canary_ibounded n.

Definition canary_ibval n (b : canary_ibounded n) : nat :=
  match b with
  | CanaryIBounded _ k _ => k
  end.

Definition canary_ibounded0_empty (b : canary_ibounded 0) : False :=
  match b in canary_ibounded n return n = 0 -> False with
  | CanaryIBounded n k H =>
      fun E => Nat.nlt_0_r k (eq_rect n (fun m => k < m) H 0 E)
  end eq_refl.

Goal
    (forall x y z p, proj1_sig (h x y z p) = z) /\
    (forall b : canary_ibounded 0,
        False_rect Prop (canary_ibounded0_empty b)).
  hammer_dump "consistency-h.p".
Abort.

(* If these constructor occurrences were both collapsed to [x] while
   constructor injectivity remained enabled, injectivity would imply [0 = 1]
   and make the dumped theory inconsistent. *)
Inductive canary_indexed_poly_subset (A : Type) : nat -> Type :=
| CanaryIndexedPolySubset :
    forall n (x : A), True -> canary_indexed_poly_subset A n.

Definition canary_indexed_poly_value
    A n (v : canary_indexed_poly_subset A n) : A :=
  match v with
  | CanaryIndexedPolySubset _ _ x _ => x
  end.

Goal forall (A : Type) (x : A) (pf : True),
    canary_indexed_poly_value A 0
      (CanaryIndexedPolySubset A 0 x pf) = x /\
    canary_indexed_poly_value A 1
      (CanaryIndexedPolySubset A 1 x pf) = x.
  hammer_dump "consistency-indexed-poly-subset.p".
Abort.

(* Case index guards read off a type-level function's own arguments relate
   unrelated symbols, so the guarded branch equations they protect are asserted
   at the wrong indices.  Both scrutinee shapes are dumped: dsize's declared
   type has a different arity than the matched family's telescope, dheight's has
   the same arity permuted. *)
(* At index zero the successor branch of [canary_vec_zero] and both
   constructors of [Fin.t] rigidly clash.  The hypotheses remain under
   universal guards, rather than being introduced as contradictory axioms. *)
Inductive canary_vec (A : Type) : nat -> Type :=
| CanaryVNil : canary_vec A 0
| CanaryVCons : forall n, A -> canary_vec A n -> canary_vec A (S n).

Definition canary_vec_zero (A : Type) (v : canary_vec A 0) : nat :=
  match v in canary_vec _ n return
      match n with 0 => nat | S _ => unit end with
  | CanaryVNil _ => 0
  | CanaryVCons _ _ _ _ => tt
  end.

Definition canary_fin0 (f : Fin.t 0) : False :=
  Fin.case0 (fun _ => False) f.

Goal
    (forall n (x : nat) (t : dtree n), dsize (dnode n x t) = S n) /\
    (forall (A : Type) (v : canary_vec A 0), canary_vec_zero A v = 0).
  hammer_dump "consistency-dsize.p".
Abort.

Goal
    (forall n (b : dbox dred n), dheight (dbox_succ dred n b) = S n) /\
    (forall f : Fin.t 0, False_rect Prop (canary_fin0 f)).
  hammer_dump "consistency-dheight.p".
Abort.

Goal forall (P : nat -> Set) a (e : a = a) x, tr P a a e x = x.
  hammer_dump "transport-tr-refl.p".
Abort.

(* F*-#1542 guard: the impossible equality lets a dependent match return the
   positive [reflect] constructor at the observably distinct [false] index.
   Its guards-off collapse is unconditional, but its result typing must remain
   behind [true = false].  The nested transport crosses three distinct types
   in the same problem, so erased polymorphic equations cannot leak between
   their type instances. *)
Definition equality_match_1542 (e : true = false)
    : reflect (false = true) false :=
  match e in (_ = b) return reflect (b = true) b with
  | eq_refl => ReflectT _ eq_refl
  end.

Definition multi_type_transports_1542
    (e_nb : nat = bool) (e_bs : bool = string) (n : nat) : string :=
  eq_rect bool (fun T => T)
    (eq_rect nat (fun T => T) n bool e_nb) string e_bs.

Goal
    (forall (P : nat -> Set) a (e1 e2 : a = a) (x : P a),
        eq_rect a P (eq_rect a P x a e1) a e2 = x) /\
    (forall (e : true = false) (e_nb : nat = bool)
        (e_bs : bool = string) (n : nat),
        equality_match_1542 e = ReflectF _ Bool.diff_false_true /\
        multi_type_transports_1542 e_nb e_bs n = EmptyString).
  hammer_dump "consistency-eq-rect.p".
Abort.

Goal 2 + 2 = 4.
  hammer_dump "consistency-nat-add.p".
Abort.
