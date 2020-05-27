From Hammer Require Import Tactics.

Lemma lem_test_1 : (forall x y, x + y = y + x -> False) -> forall x, x > x.
  ssimpl.
Qed.

Lemma lem_test_1_1 : (forall x, x >= x /\ x < x + x) -> forall x, x >= x /\ x < x + x.
  strivial.
Qed.

Lemma lem_test_2 : (forall x, x > x) -> (forall x, x + x > x) -> exists x, x > x \/ x + x > x.
  strivial.
Qed.

Lemma lem_test_3 : (forall x, x > x) -> (forall x, x + x > x) -> { x & { x > x } + { x + x > x } }.
  strivial.
Qed.

Lemma lem_test_4 : (forall x, x + x > x) -> { x & { x > x } + { x + x > x } }.
  hauto.
Qed.

Lemma lem_test_5 : (forall P : nat -> Prop, P 0 -> (forall x, P x -> P (S x)) -> P 60).
  hauto.
Qed.

Lemma lem_test_6 : (forall P : nat -> Prop, P 0 -> P (S 0) ->
                                            (forall x, P x -> P (S x) -> P (S (S x))) -> P 20).
  qblast.
Qed.

Require Import Arith.

Lemma lem_odd : forall n : nat, Nat.Odd n \/ Nat.Odd (n + 1).
  hauto using (@Coq.Arith.PeanoNat.Nat.Odd_succ, @Coq.Arith.PeanoNat.Nat.Even_or_Odd, @Coq.Arith.PeanoNat.Nat.add_1_r).
Qed.

Lemma lem_odd_2 : forall n : nat, Nat.Odd n \/ Nat.Odd (n + 1).
  lauto using (@Coq.Arith.PeanoNat.Nat.Odd_succ, @Coq.Arith.PeanoNat.Nat.Even_or_Odd, @Coq.Arith.PeanoNat.Nat.add_1_r).
Qed.

Lemma lem_2_1 : forall n : nat, Nat.Even n \/ Nat.Even (n + 1).
  hauto using (@Coq.Arith.PeanoNat.Nat.Even_succ, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.Even_or_Odd).
Qed.

Lemma lem_mult_1 : forall m n k : nat, m * n + k = k + n * m.
Proof.
  hauto using (PeanoNat.Nat.mul_comm, PeanoNat.Nat.add_comm).
Qed.

Lemma lem_pow : forall n : nat, 3 * 3 ^ n = 3 ^ (n + 1).
  hauto using (Coq.Arith.PeanoNat.Nat.pow_succ_r, Coq.Arith.PeanoNat.Nat.add_1_r, Coq.Arith.PeanoNat.Nat.le_0_l).
Qed.

Lemma lem_even_or_odd :
  forall n:nat, exists p : nat, n = (2 * p) \/ n = S (2 * p).
Proof.
  induction n; sintuition.
  exists (S p); strivial.
Qed.

Require Import ZArith.

Lemma le_mul : forall m n k : Z, (k > 0 -> k * m <= k * n -> m <= n)%Z.
Proof.
  hauto using (Coq.ZArith.BinInt.Z.mul_comm, Coq.ZArith.BinInt.Z.mul_le_mono_pos_r, Coq.ZArith.BinInt.Z.gt_lt_iff).
Qed.

Lemma lem_bnat_test_1 : forall x y, Nat.eqb x y = true -> y = x.
Proof.
  intros.
  bnat_reflect.
  assumption.
Qed.

Lemma lem_bnat_test_2 : forall x y, Nat.eqb x y = false -> x = y -> False.
Proof.
  intros x y H.
  bnat_reflect.
  assumption.
Qed.

Lemma lem_bnat_test_3 : forall x y, Nat.leb x y = true -> x <= y.
Proof.
  intros x y H.
  bnat_reflect.
  assumption.
Qed.

Lemma lem_bnat_test_4 : forall x y, Nat.leb x y = false -> y < x.
Proof.
  intros x y H.
  bnat_reflect.
  assumption.
Qed.

Lemma lem_bnat_test_5 : forall x y, Nat.ltb x y = true -> x < y.
Proof.
  intros x y H.
  bnat_reflect.
  assumption.
Qed.

Lemma lem_bnat_test_6 : forall x y, Nat.ltb x y = false -> y <= x.
Proof.
  intros x y H.
  bnat_reflect.
  assumption.
Qed.

Require NArith.BinNat.

Lemma lem_nbnat_test_1 : forall x y, BinNat.N.eqb x y = true -> x = y.
Proof.
  intros.
  bnat_reflect.
  assumption.
Qed.

Lemma lem_nbnat_test_2 : forall x y, BinNat.N.eqb x y = false -> x = y -> False.
Proof.
  intros x y H.
  bnat_reflect.
  assumption.
Qed.

Lemma setbit_iff : forall m a n : BinNums.N,
                     n = m \/ true = BinNat.N.testbit a m <->
                     BinNat.N.testbit (BinNat.N.setbit a n) m = true.
Proof.
  scrush using (@NArith.BinNat.N.setbit_iff).
Qed.

Section Sets.

Variable U : Type.
Variable P : U -> Prop.
Variable Q : U -> Prop.
Variable R : U -> Prop.

Lemma lem_sets_1 :
  (forall x, P x \/ Q x) /\ (forall x y, x = y /\ P x -> R y) /\
  (forall x y, x = y /\ Q x -> R y) -> forall x, R x.
Proof.
  hauto.
Qed.

Lemma lem_sets_1_1 :
  (forall x, P x \/ Q x) /\ (forall x y, x = y /\ P x -> R y) /\
  (forall x y, x = y /\ Q x -> R y) -> forall x, R x.
Proof.
  sauto inverting list.
Qed.

Variable Sum : U -> U -> U.
Variable Subset : U -> U -> Prop.
Variable In : U -> U -> Prop.
Variable Seteq : U -> U -> Prop.

Lemma lem_sets_2 :
  (forall A B X, In X (Sum A B) <-> In X A \/ In X B) /\
  (forall A B, Seteq A B <-> Subset A B /\ Subset B A) /\
  (forall A B, Subset A B <-> forall X, In X A -> In X B) ->
  (forall A, Seteq (Sum A A) A).
Proof.
  hauto.
Qed.

End Sets.

Section FOFProblem1.

Variable Universe : Set.

Variable r : Universe -> Prop.
Variable q : Universe -> Universe -> Prop.
Variable p : Universe -> Prop.

Variable axiom1_1 : (forall X : Universe, (p X -> (r X \/ (exists Y : Universe, q X Y)))).
Variable axiom2_2 : (forall X : Universe, (r X -> ~((exists X : Universe, p X)))).
Variable axiom3_3 : (exists X : Universe, p X).

Theorem con_4 : (exists X : Universe, (exists Y : Universe, q X Y)).
Proof.
  hauto.
Qed.

End FOFProblem1.

Section FOFProblem2.

Variable Universe : Set.
Variable UniverseElement : Universe.

Variable a_ : Universe -> Universe -> Prop.

Theorem prove_this_1 : (forall X : Universe, (exists Y : Universe, (a_ X Y /\ a_ Y Y))) ->
                       (exists Z : Universe, a_ Z Z).
Proof.
  sauto.
Qed.

End FOFProblem2.

Require Import List.

Section Lists.

Lemma lem_lst :
  forall {A} (x : A) l1 l2 (P : A -> Prop),
    In x (l1 ++ l2) -> (forall y, In y l1 -> P y) -> (forall y, In y l2 -> P y) ->
    P x.
Proof.
  sauto.
Qed.

Lemma lem_lst2 : forall {A} (y1 y2 y3 : A) l l' z, In z l \/ In z l' ->
                                                   In z (y1 :: y2 :: l ++ y3 :: l').
Proof.
  sauto.
Qed.

Lemma lem_lst3 : forall {A} (l : list A), length (tl l) <= length l.
Proof.
  hauto inverting list.
Qed.

Lemma lem_lst4 : forall {A} (l : list A), l <> nil -> length (tl l) < length l.
Proof.
  hauto inverting list.
Qed.

Lemma lem_lst5 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  induction l'.
  - hauto using (@Lists.List.app_nil_end).
  - hauto using (@Lists.List.NoDup_remove_1).
Qed.

End Lists.

From Hammer Require Import Reflect.

Lemma lem_breflect_test_1 : forall b1 b2 b3, b1 && b2 || b3 -> b3 || b2 || b1.
Proof.
  intros.
  breflect in *.
  tauto.
Qed.

Lemma lem_breflect_test_2 : forall b1 b2 b3, implb (b1 && b2 || b3) (b3 || b2 || b1).
Proof.
  intros.
  breflect.
  tauto.
Qed.

Lemma lem_breflect_test_3 : forall b1 b2 b3, eqb (b1 && b2 || b3) (b3 || b2 && b1).
Proof.
  intros.
  breflect.
  tauto.
Qed.

Lemma lem_breflect_test_1' : forall b1 b2 b3, b1 && b2 || b3 -> b3 || b2 || b1.
Proof.
  breflect.
  tauto.
Qed.

Lemma lem_breflect_test_2' : forall b1 b2 b3, implb (b1 && b2 || b3) (b3 || b2 || b1).
Proof.
  breflect.
  tauto.
Qed.

Lemma lem_breflect_test_3' : forall b1 b2 b3, eqb (b1 && b2 || b3) (b3 || b2 && b1).
Proof.
  breflect.
  tauto.
Qed.

Lemma lem_breflect_test_4 :
  forall b1 b2 b3, (forall n, Nat.eqb n n) ->
                   (implb (b1 || b2) (Nat.eqb 0 0 && (b2 || b1 || b3))).
Proof.
  breflect.
  tauto.
Qed.

Lemma lem_bauto_test_1 : forall b1 b2 b3, b1 && b2 || b3 -> b3 || b2 || b1.
Proof.
  sauto.
Qed.

Lemma lem_bauto_test_2 : forall b1 b2 b3, implb (b1 && b2 || b3) (b3 || b2 || b1).
Proof.
  sauto.
Qed.

Lemma lem_bauto_test_3 : forall b1 b2 b3, eqb (b1 && b2 || b3) (b3 || b2 && b1).
Proof.
  sauto.
Qed.

Require Import Nat.
Require Import Psatz.

Inductive Term : Set :=
| LS : Term
| LK : Term
| LI : Term
| LVar : nat -> Term
| LApp : Term -> Term -> Term
| LLam : nat -> Term -> Term.

Fixpoint size (t : Term) : nat :=
  match t with
    | LS | LK | LVar _ => 1
    | LI => 2
    | LApp x y => size x + size y + 1
    | LLam _ x => size x + 1
  end.

Fixpoint abstr (v : nat) (t : Term) : Term :=
  match t with
    | LS | LK | LI => LApp LK t
    | LVar n => if n =? v then LI else LApp LK t
    | LApp x y => LApp (LApp LS (abstr v x)) (abstr v y)
    | LLam _ _ => t
  end.

Fixpoint transl (t : Term) : Term :=
  match t with
    | LS | LK | LI | LVar _ => t
    | LApp x y => LApp (transl x) (transl y)
    | LLam v x => abstr v (transl x)
  end.

(* variable-capturing substitution *)
Fixpoint csubst (t : Term) (v : nat) (s : Term) : Term :=
  match t with
    | LS | LK | LI => t
    | LVar n => if n =? v then s else t
    | LApp x y => LApp (csubst x v s) (csubst y v s)
    | LLam u x => LLam u (csubst x v s)
  end.

Inductive NoLambdas : Term -> Prop :=
| nl_s : NoLambdas LS
| nl_k : NoLambdas LK
| nl_i : NoLambdas LI
| nl_var : forall n : nat, NoLambdas (LVar n)
| nl_app : forall x y : Term, NoLambdas x -> NoLambdas y -> NoLambdas (LApp x y).

Lemma no_lams_abstr : forall (v : nat) (t : Term), NoLambdas t -> NoLambdas (abstr v t).
Proof.
  induction t; sauto.
Qed.

Lemma no_lams_transl : forall t : Term, NoLambdas (transl t).
Proof.
  induction t; sauto using no_lams_abstr.
Qed.

Inductive HasVar : nat -> Term -> Prop :=
| hs_var : forall n : nat, HasVar n (LVar n)
| hs_app : forall (n : nat) (x y : Term), HasVar n x \/ HasVar n y -> HasVar n (LApp x y)
| hs_lem : forall (n v : nat) (x : Term), n <> v -> HasVar n x -> HasVar n (LLam v x).

Lemma vars_abstr :
  forall (t : Term) (n v : nat), n <> v -> (HasVar n t <-> HasVar n (abstr v t)).
Proof.
  induction t; scrush.
Qed.

Lemma novar_abstr : forall (v : nat) (t : Term), NoLambdas t -> ~(HasVar v (abstr v t)).
Proof.
  induction t; qsimpl.
Qed.

Lemma vars_transl : forall (t : Term) (n : nat), HasVar n t <-> HasVar n (transl t).
Proof.
  induction t; qsimpl.
  - hauto using vars_abstr.
  - hauto using (@hs_lem, @vars_abstr, @novar_abstr, @no_lams_transl).
Qed.

Notation "X @ Y" := (LApp X Y) (at level 11, left associativity).

Inductive WeakEqual : Term -> Term -> Prop :=
| we_refl : forall (t : Term), WeakEqual t t
| we_sym : forall (t u : Term), WeakEqual t u -> WeakEqual u t
| we_trans : forall (t u w : Term), WeakEqual t u -> WeakEqual u w -> WeakEqual t w
| we_cong : forall (t1 t2 s1 s2 : Term),
              WeakEqual t1 t2 -> WeakEqual s1 s2 -> WeakEqual (t1 @ s1) (t2 @ s2)
| we_s : forall (x y z : Term), WeakEqual (LS @ x @ y @ z) ((x @ z) @ (y @ z))
| we_k : forall (x y : Term), WeakEqual (LK @ x @ y) x
| we_i : forall (x y : Term), WeakEqual (LI @ x) x.

Notation "X =w Y" := (WeakEqual X Y) (at level 80).

Lemma abstr_correct :
  forall (t s : Term) (v : nat), NoLambdas t -> abstr v t @ s =w csubst t v s.
Proof.
  induction t; scrush.
Qed.

Lemma abstr_size :
  forall (t : Term) (v : nat), size (abstr v t) <= 3 * size t.
Proof.
  intros; induction t; qsimpl.
Qed.

Lemma lem_pow_3 : (forall x y : nat, 3 ^ x + 3 ^ y + 1 <= 3 ^ (x + y + 1)).
Proof.
  intros.
  induction x; simpl in *.
  induction y; simpl in *; lia.
  lia.
Qed.

Lemma transl_size :
  forall (t : Term), size (transl t) <= 3 ^ (size t).
Proof.
  induction t; qsimpl.
  - assert (size (transl t1) + size (transl t2) <= 3 ^ size t1 + 3 ^ size t2).
    { eauto using PeanoNat.Nat.add_le_mono. }
    assert (size (transl t1) + size (transl t2) + 1 <= 3 ^ size t1 + 3 ^ size t2 + 1).
    { auto with zarith. }
    hauto using (@Coq.Arith.PeanoNat.Nat.le_lt_trans, @lem_pow_3, @Coq.Arith.PeanoNat.Nat.lt_succ_r).
  - assert (size (abstr n (transl t)) <= 3 * size (transl t)).
    { eauto using abstr_size with zarith. }
    assert (size (abstr n (transl t)) <= 3 * 3 ^ size t).
    { eauto using Nat.le_trans with zarith. }
    assert (forall x : nat, 3 * 3 ^ x = 3 ^ (x + 1)) by hauto using Nat.add_1_r.
    scrush.
Qed.

Lemma abstr_size_lb : forall (t : Term) (v : nat), NoLambdas t -> size (abstr v t) >= 2 * size t.
Proof.
  intros; induction t; qsimpl.
Qed.

Fixpoint long_app (n : nat) : Term :=
  match n with
    | 0 => LVar 0
    | S k => LApp (long_app k) (LVar n)
  end.

Fixpoint long_term (n m : nat) : Term :=
  match n with
    | 0 => LLam m (long_app m)
    | S k => LLam (m - n) (long_term k m)
  end.

Definition cex_term (n : nat) := long_term n n.

Lemma size_nonneg : forall (t : Term), size t > 0.
Proof.
  induction t; simpl; lia.
Qed.

Lemma transl_size_lb : forall (n : nat), size (transl (cex_term n)) >= 2^n.
Proof.
  assert (forall (n m : nat), size (transl (long_term n m)) >= 2^n).
  induction n; ssimpl.
  - scrush using (@Coq.Arith.PeanoNat.Nat.nlt_ge, @Coq.Arith.Gt.gt_le_S, @Coq.Arith.Compare_dec.not_ge, @size_nonneg).
  - assert (size (abstr (m - S n) (transl (long_term n m))) >= 2 * size (transl (long_term n m))).
    { hauto using (@abstr_size_lb, @no_lams_transl). }
    assert (size (abstr (m - S n) (transl (long_term n m))) >= 2 * 2 ^ n).
    { pose proof (IHn m); eauto with zarith. }
    scrush.
  - now unfold cex_term.
Qed.

Fixpoint occurs (v : nat) (t : Term) : bool :=
  match t with
    | LS | LK | LI => false
    | LVar n => if n =? v then true else false
    | LApp x y => occurs v x || occurs v y
    | LLam n b => if n =? v then false else occurs v b
  end.

Lemma occurs_spec : forall (v : nat) (t : Term), occurs v t <-> HasVar v t.
Proof.
  induction t; ssimpl; breflect in *; ssimpl.
Qed.

Fixpoint abstr2 (v : nat) (t : Term) : Term :=
  if occurs v t then
    match t with
      | LS | LK | LI => LApp LK t
      | LVar n => if n =? v then LI else LApp LK t
      | LApp x y => LApp (LApp LS (abstr2 v x)) (abstr2 v y)
      | LLam _ _ => t
    end
  else
    LApp LK t.

Fixpoint transl2 (t : Term) : Term :=
  match t with
    | LS | LK | LI | LVar _ => t
    | LApp x y => LApp (transl2 x) (transl2 y)
    | LLam v x => abstr2 v (transl2 x)
  end.

Lemma no_lams_abstr2 : forall (v : nat) (t : Term), NoLambdas t -> NoLambdas (abstr2 v t).
Proof.
  induction t; scrush.
Qed.

Lemma no_lams_transl2 : forall t : Term, NoLambdas (transl2 t).
Proof.
  induction t; sauto using no_lams_abstr2.
Qed.

Lemma vars_abstr2 :
  forall (t : Term) (n v : nat), n <> v -> (HasVar n t <-> HasVar n (abstr2 v t)).
Proof.
  induction t; scrush. (* 3.5 s *)
Qed.

Lemma novar_abstr2 : forall (v : nat) (t : Term), NoLambdas t -> ~(HasVar v (abstr2 v t)).
Proof.
  intros.
  pose (u := t).
  induction t; bdestruct (occurs v u); scrush using occurs_spec.
Qed.

Lemma vars_transl2 : forall (t : Term) (n : nat), HasVar n t <-> HasVar n (transl2 t).
Proof.
  induction t; qsimpl.
  - hauto using (@vars_abstr2).
  - hauto using (@no_lams_transl2, @vars_abstr2, @novar_abstr2, @hs_lem).
Qed.

Lemma hasvar_inv :
  forall (t1 t2 : Term) (v : nat), ~(HasVar v (t1 @ t2)) -> ~(HasVar v t1) /\ ~(HasVar v t2).
Proof.
  sauto.
Qed.

Lemma csubst_novar :
  forall (t s : Term) (v : nat), NoLambdas t -> ~(HasVar v t) -> csubst t v s = t.
Proof.
  intros; induction t; sauto.
Qed.

Lemma abstr2_correct :
  forall (t s : Term) (v : nat), NoLambdas t -> abstr2 v t @ s =w csubst t v s.
Proof.
  induction t; qsimpl.
  - sauto.
  - sauto.
  - pose proof occurs_spec.
    rewrite csubst_novar by ssimpl.
    rewrite csubst_novar by ssimpl.
    strivial.
Qed.

Lemma abstr2_size_ub :
  forall (t : Term) (v : nat), size (abstr2 v t) <= 3 * size t.
Proof.
  intros; induction t; qsimpl.
Qed.

Require Import String.

Inductive aexpr :=
| Nval : nat -> aexpr
| Vval : string -> aexpr
| Aplus : aexpr -> aexpr -> aexpr.

Definition state := string -> nat.

Fixpoint aval (s : state) (e : aexpr) :=
  match e with
  | Nval n => n
  | Vval x => s x
  | Aplus x y => aval s x + aval s y
  end.

Fixpoint plus (e1 e2 : aexpr) :=
  match e1, e2 with
  | Nval n1, Nval n2 => Nval (n1 + n2)
  | Nval 0, _ => e2
  | _, Nval 0 => e1
  | _, _ => Aplus e1 e2
  end.

Lemma lem_aval_plus : forall s e1 e2, aval s (plus e1 e2) = aval s e1 + aval s e2.
Proof.
  induction e1; sauto.
Qed.

Fixpoint asimp (e : aexpr) :=
  match e with
  | Aplus x y => plus (asimp x) (asimp y)
  | _ => e
  end.

Lemma lem_aval_asimp : forall s e, aval s (asimp e) = aval s e.
Proof.
  induction e; sauto using lem_aval_plus.
Qed.

Inductive bexpr :=
| Bval : bool -> bexpr
| Bnot : bexpr -> bexpr
| Band : bexpr -> bexpr -> bexpr
| Bless : aexpr -> aexpr -> bexpr.

Fixpoint bval (s : state) (e : bexpr) :=
  match e with
  | Bval b => b
  | Bnot e1 => negb (bval s e1)
  | Band e1 e2 => bval s e1 && bval s e2
  | Bless a1 a2 => aval s a1 <? aval s a2
  end.

Fixpoint not (e : bexpr) :=
  match e with
  | Bval true => Bval false
  | Bval false => Bval true
  | _ => Bnot e
  end.

Fixpoint and (e1 e2 : bexpr) :=
  match e1, e2 with
  | Bval true, _ => e2
  | _, Bval true => e1
  | Bval false, _ => Bval false
  | _, Bval false => Bval false
  | _, _ => Band e1 e2
  end.

Definition less (a1 a2 : aexpr) :=
  match a1, a2 with
  | Nval n1, Nval n2 => Bval (n1 <? n2)
  | _, _ => Bless a1 a2
  end.

Fixpoint bsimp (e : bexpr) :=
  match e with
  | Bnot e1 => not (bsimp e1)
  | Band e1 e2 => and (bsimp e1) (bsimp e2)
  | Bless a1 a2 => less a1 a2
  | _ => e
  end.

Lemma lem_bval_not : forall s e, bval s (not e) = negb (bval s e).
Proof.
  induction e; sauto.
Qed.

Lemma lem_bval_and : forall s e1 e2, bval s (and e1 e2) = bval s e1 && bval s e2.
Proof.
  induction e1; sauto.
Qed.

Lemma lem_bval_less : forall s a1 a2, bval s (less a1 a2) = (aval s a1 <? aval s a2).
Proof.
  induction a1; sauto.
Qed.

Lemma lem_bval_bsimp : forall s e, bval s (bsimp e) = bval s e.
Proof.
  induction e; sauto using (lem_bval_not, lem_bval_and, lem_bval_less).
Qed.

Inductive cmd :=
| Skip : cmd
| Assign : string -> aexpr -> cmd
| Seq : cmd -> cmd -> cmd
| If : bexpr -> cmd -> cmd -> cmd
| While : bexpr -> cmd -> cmd.

Definition update (s : state) x v y := if string_dec x y then v else s y.

Inductive big_step : cmd * state -> state -> Prop :=
| SkipSem : forall s, big_step (Skip, s) s
| AssignSem : forall s x a, big_step (Assign x a, s) (update s x (aval s a))
| SeqSem : forall c1 c2 s1 s2 s3, big_step (c1, s1) s2 -> big_step (c2, s2) s3 ->
                                  big_step (Seq c1 c2, s1) s3
| IfTrue : forall b c1 c2 s s', bval s b = true -> big_step (c1, s) s' ->
                                big_step (If b c1 c2, s) s'
| IfFalse : forall b c1 c2 s s', bval s b = false -> big_step (c2, s) s' ->
                                 big_step (If b c1 c2, s) s'
| WhileFalse : forall b c s, bval s b = false ->
                             big_step (While b c, s) s
| WhileTrue : forall b c s1 s2 s3,
    bval s1 b = true -> big_step (c, s1) s2 -> big_step (While b c, s2) s3 ->
    big_step (While b c, s1) s3.

Notation "A ==> B" := (big_step A B) (at level 80, no associativity).

Lemma lem_seq_assoc : forall c1 c2 c3 s s', (Seq c1 (Seq c2 c3), s) ==> s' <->
                                            (Seq (Seq c1 c2) c3, s) ==> s'.
Proof.
  sauto. (* 0.45s *)
Qed.

Definition equiv_cmd (c1 c2 : cmd) := forall s s', (c1, s) ==> s' <-> (c2, s) ==> s'.

Notation "A ~~ B" := (equiv_cmd A B) (at level 70, no associativity).

Lemma lem_unfold_loop : forall b c, While b c ~~ If b (Seq c (While b c)) Skip.
Proof.
  sauto unfolding equiv_cmd. (* 0.46s *)
Qed.

Lemma lem_while_cong_aux : forall b c c' s s', (While b c, s) ==> s' -> c ~~ c' ->
                                               (While b c', s) ==> s'.
Proof.
  enough (forall p s', p ==> s' -> forall b c c' s, p = (While b c, s) -> c ~~ c' -> (While b c', s) ==> s') by eauto.
  intros p s' H.
  induction H; sauto unfolding equiv_cmd.
Qed.

Lemma lem_while_cong : forall b c c', c ~~ c' -> While b c ~~ While b c'.
Proof.
  hauto using lem_while_cong_aux unfolding equiv_cmd.
Qed.

Lemma lem_big_step_deterministic :
  forall c s s1 s2, (c, s) ==> s1 -> (c, s) ==> s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H; revert s2.
  induction H; scrush. (* 2s *)
Qed.

Inductive small_step : cmd * state -> cmd * state -> Prop :=
| AssignSemS : forall x a s, small_step (Assign x a, s) (Skip, update s x (aval s a))
| SeqSemS1 : forall c s, small_step (Seq Skip c, s) (c, s)
| SeqSemS2 : forall c1 c2 s c1' s', small_step (c1, s) (c1', s') ->
                                    small_step (Seq c1 c2, s) (Seq c1' c2, s')
| IfTrueS : forall b c1 c2 s, bval s b = true ->
                              small_step (If b c1 c2, s) (c1, s)
| IfFalseS : forall b c1 c2 s, bval s b = false ->
                               small_step (If b c1 c2, s) (c2, s)
| WhileS : forall b c s, small_step (While b c, s) (If b (Seq c (While b c)) Skip, s).

Notation "A --> B" := (small_step A B) (at level 80, no associativity).

Require Import Relations.

Definition small_step_star := clos_refl_trans (cmd * state) small_step.

Tactics Hint Unfold small_step_star.

Notation "A -->* B" := (small_step_star A B) (at level 80, no associativity).

Lemma lem_small_step_deterministic :
  forall c s s1 s2, (c, s) --> s1 -> (c, s) --> s2 -> s1 = s2.
Proof.
  intros c s s1 s2 H; revert s2.
  induction H; sauto.
Qed.

Lemma lem_star_seq2 : forall c1 c2 s c1' s', (c1, s) -->* (c1', s') ->
                                             (Seq c1 c2, s) -->* (Seq c1' c2, s').
Proof.
  enough (forall p1 p2, p1 -->* p2 ->
                        forall c1 c2 s c1' s', p1 = (c1, s) -> p2 = (c1', s') ->
                                               (Seq c1 c2, s) -->* (Seq c1' c2, s')) by eauto.
  intros p1 p2 H.
  induction H; sauto.
Qed.

Lemma lem_seq_comp : forall c1 c2 s1 s2 s3, (c1, s1) -->* (Skip, s2) -> (c2, s2) -->* (Skip, s3) ->
                                            (Seq c1 c2, s1) -->* (Skip, s3).
Proof.
  intros c1 c2 s1 s2 s3 H1 H2.
  assert ((Seq c1 c2, s1) -->* (Seq Skip c2, s2)) by sauto using lem_star_seq2.
  scrush.
Qed.

Lemma lem_big_to_small : forall p s', p ==> s' -> p -->* (Skip, s').
Proof.
  intros p s' H.
  induction H as [ | | | | | | b c s1 s2 ]; ssimpl.
  - sauto using (@lem_seq_comp).
  - sauto using rt_trans.
  - sauto using rt_trans.
  - sauto using rt_trans.
  - assert ((While b c, s1) -->* (Seq c (While b c), s1)) by
        (eapply rt_trans; scrush).
    assert ((Seq c (While b c), s1) -->* (Seq Skip (While b c), s2)) by
        sauto using lem_star_seq2.
    sauto using rt_trans.
Qed.

Lemma lem_small_to_big_aux : forall p p', p --> p' -> forall s, p' ==> s -> p ==> s.
Proof.
  intros p p' H.
  induction H; ssimpl.
  hauto using lem_unfold_loop unfolding equiv_cmd.
Qed.

Lemma lem_small_to_big_aux_2 : forall p p', p -->* p' -> forall s, p' ==> s -> p ==> s.
Proof.
  intros p p' H.
  induction H; ssimpl.
  hauto using (@lem_small_to_big_aux).
Qed.

Lemma lem_small_to_big : forall p s, p -->* (Skip, s) -> p ==> s.
Proof.
  enough (forall p p', p -->* p' -> forall s, p' = (Skip, s) -> p ==> s) by eauto.
  intros p p' H.
  induction H; ssimpl.
  - sauto.
  - hauto using (@lem_small_to_big_aux_2) unfolding (@small_step_star).
Qed.

Corollary cor_big_iff_small : forall p s, p ==> s <-> p -->* (Skip, s).
Proof.
  hauto using (@lem_small_to_big, @lem_big_to_small).
Qed.
