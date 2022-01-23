From Hammer Require Import Tactics.

(* Basic tests *)

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
  sblast.
Qed.

Definition ff := False.

Lemma lem_test_def : (forall P : Prop, P \/ (P -> ff) -> ((P -> ff) -> False) -> P).
Proof.
  hauto.
Qed.

Definition feq (x y z : nat) : Prop := x + y + z = x * y + z.

Lemma lem_sym_feq : (forall x y z, feq x y z) -> forall x y z, x * y + z = x + y + z.
Proof.
  sauto.
Qed.

Lemma lem_implicit_arg {A} : forall l : list A, List.map id l = l.
Proof.
  sauto use: List.map_id.
Qed.

Lemma test_implicit_arg1 {A} : forall l : list A, List.map id l = l.
Proof.
  sauto use: lem_implicit_arg.
Qed.

Class Mere A := {
  mere : forall x y : A, x = y
}.

Lemma lem_implicit_arg2 {A} `{Mere A} {B} (f g : B -> A) :
  forall l : list B, List.map f l = List.map g l.
Proof.
  induction l; sauto.
Qed.

Global Instance mere_unit : Mere unit.
Proof.
  sauto.
Qed.

Lemma test_implicit_arg2 {B} :
  forall (l: list B) (f g : B -> unit), List.map f l = List.map g l.
Proof.
  sauto use: lem_implicit_arg2.
Qed.

(* Argument parsing test *)

Lemma lem_q (q: nat): q = q.
Proof.
  sauto q: on.
Qed.

Lemma lem_l (l: nat): l = l.
Proof.
  sauto l: on.
Qed.

Lemma lem_lq (lq: nat): lq = lq.
Proof.
  sauto lq: on.
Qed.

Lemma lem_depth (depth: nat): depth = depth.
Proof.
  sauto depth: 1.
Qed.

(* More tests *)

Require Import Arith.

Lemma lem_test_csplit : forall n, if n =? n then True else False.
Proof.
  sauto cases: bool.
Qed.

Lemma lem_odd : forall n : nat, Nat.Odd n \/ Nat.Odd (n + 1).
  hauto use: @Coq.Arith.PeanoNat.Nat.Odd_succ, @Coq.Arith.PeanoNat.Nat.Even_or_Odd, @Coq.Arith.PeanoNat.Nat.add_1_r.
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
  induction n; sintuition ered: off.
  exists (S p); strivial.
Qed.

Require Import ZArith.

Lemma le_mul : forall m n k : Z, (k > 0 -> k * m <= k * n -> m <= n)%Z.
Proof.
  hauto use: Coq.ZArith.BinInt.Z.mul_comm, Coq.ZArith.BinInt.Z.mul_le_mono_pos_r, Coq.ZArith.BinInt.Z.gt_lt_iff.
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
  sauto inv: list.
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

Inductive R_add : nat -> nat -> nat -> Prop :=
| R_add_0 : forall m, R_add 0 m m
| R_add_S : forall p m k, R_add p m k -> R_add (S p) m (S k).

Global Hint Constructors R_add : R_add_db.

Lemma lem_minus : exists x, R_add x 2 20.
Proof.
  hauto db: R_add_db.
Qed.

Require Import List.
Require Import Lia.

From Hammer Require Import Hints.

Section Lists.

Lemma lem_lst :
  forall {A} (x : A) l1 l2 (P : A -> Prop),
    In x (l1 ++ l2) -> (forall y, In y l1 -> P y) -> (forall y, In y l2 -> P y) ->
    P x.
Proof.
  sauto db: slist.
Qed.

Lemma lem_lst2 : forall {A} (y1 y2 y3 : A) l l' z, In z l \/ In z l' ->
                                                   In z (y1 :: y2 :: l ++ y3 :: l').
Proof.
  sauto db: slist.
Qed.

Lemma lem_lst3 : forall {A} (l : list A), length (tl l) <= length l.
Proof.
  hauto inv: list.
Qed.

Lemma lem_lst4 : forall {A} (l : list A), l <> nil -> length (tl l) < length l.
Proof.
  hauto inv: list.
Qed.

Lemma lem_lst5 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  induction l'.
  - hauto using (@Lists.List.app_nil_end).
  - hauto using (@Lists.List.NoDup_remove_1).
Qed.

End Lists.

Require Import Reals.
Require Import Lra.

Section Real.

Local Open Scope R_scope.

Lemma lem_real_1 : forall x y, x + y = y + x.
Proof.
  sauto solve: lra.
Qed.

Lemma lem_real_2 P : (forall a b, P a -> a = b -> P b) ->
                     forall x y, P (x + y) -> P (y + x).
Proof.
  qauto solve: lra.
Qed.

End Real.


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
  - hauto use: @no_lams_transl, @vars_abstr, @novar_abstr, @hs_lem.
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
  induction t; sintuition.
  - assert (size (transl t1) + size (transl t2) <= 3 ^ size t1 + 3 ^ size t2).
    { eauto using PeanoNat.Nat.add_le_mono. }
    assert (size (transl t1) + size (transl t2) + 1 <= 3 ^ size t1 + 3 ^ size t2 + 1).
    { auto with zarith. }
    hauto use: Nat.le_trans, lem_pow_3.
  - assert (size (abstr n (transl t)) <= 3 * size (transl t)).
    { eauto using abstr_size with zarith. }
    assert (size (abstr n (transl t)) <= 3 * 3 ^ size t).
    { eauto using Nat.le_trans with zarith. }
    assert (forall x : nat, 3 * 3 ^ x = 3 ^ (x + 1)) by hauto using Nat.add_1_r.
    congruence.
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
    | LVar n => n =? v
    | LApp x y => occurs v x || occurs v y
    | LLam n b => negb (n =? v) && occurs v b
  end.

Lemma occurs_spec : forall (v : nat) (t : Term), occurs v t <-> HasVar v t.
Proof.
  induction t; sauto b: on.
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
  induction t; scrush. (* 2.4s *)
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
  - use occurs_spec.
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

Definition plus (e1 e2 : aexpr) :=
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
  induction e; sauto use: lem_aval_plus.
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

Definition not (e : bexpr) :=
  match e with
  | Bval true => Bval false
  | Bval false => Bval true
  | _ => Bnot e
  end.

Definition and (e1 e2 : bexpr) :=
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
  induction e1; sauto db: sbool.
Qed.

Lemma lem_bval_less : forall s a1 a2, bval s (less a1 a2) = (aval s a1 <? aval s a2).
Proof.
  induction a1; sauto.
Qed.

Lemma lem_bval_bsimp : forall s e, bval s (bsimp e) = bval s e.
Proof.
  induction e; sauto use: lem_bval_not, lem_bval_and, lem_bval_less.
Qed.

Inductive cmd :=
| Nop : cmd
| Assign : string -> aexpr -> cmd
| Seq : cmd -> cmd -> cmd
| If : bexpr -> cmd -> cmd -> cmd
| While : bexpr -> cmd -> cmd.

Notation "A <- B" := (Assign A B) (at level 60).
Notation "A ;; B" := (Seq A B) (at level 70).
Notation "'If' A 'Then' B 'Else' C" := (If A B C) (at level 65).
Notation "'While' A 'Do' B" := (While A B) (at level 65).

Definition update (s : state) x v y :=
  if string_dec x y then v else s y.

Definition state_subst (s : state) (x : string) (a : aexpr) : state :=
  (update s x (aval s a)).

Notation "s [[ x := a ]]" := (state_subst s x a) (at level 5).

(* Big-step operational semantics *)

Inductive BigStep : cmd -> state -> state -> Prop :=
| NopSem : forall s, BigStep Nop s s
| AssignSem : forall s x a, BigStep (x <- a) s s[[x := a]]
| SeqSem : forall c1 c2 s1 s2 s3, BigStep c1 s1 s2 -> BigStep c2 s2 s3 ->
                                  BigStep (c1 ;; c2) s1 s3
| IfTrue : forall b c1 c2 s s', bval s b -> BigStep c1 s s' ->
                                BigStep (If b Then c1 Else c2) s s'
| IfFalse : forall b c1 c2 s s', negb (bval s b) -> BigStep c2 s s' ->
                                 BigStep (If b Then c1 Else c2) s s'
| WhileFalse : forall b c s, negb (bval s b) -> BigStep (While b Do c) s s
| WhileTrue : forall b c s1 s2 s3,
    bval s1 b -> BigStep c s1 s2 -> BigStep (While b Do c) s2 s3 ->
    BigStep (While b Do c) s1 s3.

Notation "A >> B ==> C" :=
  (BigStep A B C) (at level 80, no associativity).

Lemma lem_big_step_deterministic :
  forall c s s1, c >> s ==> s1 -> forall s2, c >> s ==> s2 -> s1 = s2.
Proof.
  induction 1; sauto brefl: on.
Qed.

(* Program equivalence *)

Definition equiv_cmd (c1 c2 : cmd) :=
  forall s s', c1 >> s ==> s' <-> c2 >> s ==> s'.

Notation "A ~~ B" := (equiv_cmd A B) (at level 75, no associativity).

Lemma lem_sim_refl : forall c, c ~~ c.
Proof.
  sauto.
Qed.

Lemma lem_sim_sym : forall c c', c ~~ c' -> c' ~~ c.
Proof.
  sauto unfold: equiv_cmd.
Qed.

Lemma lem_sim_trans : forall c1 c2 c3, c1 ~~ c2 -> c2 ~~ c3 -> c1 ~~ c3.
Proof.
  sauto unfold: equiv_cmd.
Qed.

Lemma lem_seq_assoc : forall c1 c2 c3, c1;; (c2;; c3) ~~ (c1;; c2);; c3.
Proof.
  sauto lazy: on unfold: equiv_cmd.
Qed.

Lemma lem_triv_if : forall b c, If b Then c Else c ~~ c.
Proof.
  unfold equiv_cmd.
  intros b c s s'.
  destruct (bval s b) eqn:?; sauto.
Qed.

Lemma lem_commute_if :
  forall b1 b2 c1 c2 c3,
    If b1 Then (If b2 Then c1 Else c2) Else c3 ~~
       If b2 Then (If b1 Then c1 Else c3) Else (If b1 Then c2 Else c3).
Proof.
  unfold equiv_cmd.
  intros *.
  destruct (bval s b1) eqn:?; destruct (bval s b2) eqn:?;
           sauto lq: on inv: BigStep ctrs: BigStep.
Qed.

Lemma lem_unfold_while : forall b c,
  While b Do c ~~ If b Then c;; While b Do c Else Nop.
Proof.
  sauto l: on unfold: equiv_cmd.
Qed.

Lemma lem_while_cong_aux : forall b c c' s s',
  While b Do c >> s ==> s' -> c ~~ c' -> While b Do c' >> s ==> s'.
Proof.
  intros *.
  remember (While b Do c).
  induction 1; sauto lq: on unfold: equiv_cmd.
Qed.

Lemma lem_while_cong : forall b c c',
  c ~~ c' -> While b Do c ~~ While b Do c'.
Proof.
  hauto use: lem_while_cong_aux unfold: equiv_cmd.
Qed.

(* Small-step operational semantics *)

Inductive SmallStep : cmd * state -> cmd * state -> Prop :=
| AssignSemS : forall x a s, SmallStep (x <- a, s) (Nop, s[[x := a]])
| SeqSemS1 : forall c s, SmallStep (Nop ;; c, s) (c, s)
| SeqSemS2 : forall c1 c2 s c1' s', SmallStep (c1, s) (c1', s') ->
                                    SmallStep (c1 ;; c2, s) (c1';; c2, s')
| IfTrueS : forall b c1 c2 s, bval s b ->
                              SmallStep (If b Then c1 Else c2, s) (c1, s)
| IfFalseS : forall b c1 c2 s, negb (bval s b) ->
                               SmallStep (If b Then c1 Else c2, s) (c2, s)
| WhileS : forall b c s, SmallStep (While b Do c, s)
                                   (If b Then c;; While b Do c Else Nop, s).

Notation "A --> B" := (SmallStep A B) (at level 80, no associativity).

Require Import Relations.

Definition SmallStepStar := clos_refl_trans (cmd * state) SmallStep.

Notation "A -->* B" := (SmallStepStar A B) (at level 80, no associativity).

Lemma lem_small_step_deterministic :
  forall p p1, p --> p1 -> forall p2, p --> p2 -> p1 = p2.
Proof.
  induction 1; sauto lq: on brefl: on.
Qed.

(* Equivalence between big-step and small-step operational semantics *)

Lemma lem_star_seq2 : forall c1 c2 s c1' s',
  (c1, s) -->* (c1', s') -> (c1;; c2, s) -->* (c1';; c2, s').
Proof.
  enough (forall p1 p2, p1 -->* p2 ->
          forall c1 c2 s c1' s', p1 = (c1, s) -> p2 = (c1', s') ->
                                 (c1;; c2, s) -->* (c1';; c2, s')).
  { eauto. }
  induction 1; sauto lq: on.
Qed.

Lemma lem_seq_comp : forall c1 c2 s1 s2 s3,
    (c1, s1) -->* (Nop, s2) ->
    (c2, s2) -->* (Nop, s3) ->
    (c1;; c2, s1) -->* (Nop, s3).
Proof.
  intros c1 c2 s1 s2 s3 H1 H2.
  assert ((c1;; c2, s1) -->* (Nop;; c2, s2)) by sauto use: lem_star_seq2.
  sauto.
Qed.

Lemma lem_big_to_small : forall c s s',
  c >> s ==> s' -> (c, s) -->* (Nop, s').
Proof.
  intros c s s' H.
  induction H as [ | | | | | | b c s1 s2 ].
  - sauto.
  - sauto.
  - sauto use: lem_seq_comp.
  - sauto.
  - sauto.
  - sauto.
  - assert ((While b Do c, s1) -->* (c;; While b Do c, s1)) by sauto.
    assert ((c;; While b Do c, s1) -->* (Nop;; While b Do c, s2)) by
        sauto use: lem_star_seq2.
    sauto.
Qed.

Lemma lem_small_to_big_aux : forall p p',
    p --> p' -> forall c1 s1 c2 s2 s,
      p = (c1, s1) -> p' = (c2, s2) -> c2 >> s2 ==> s ->
      c1 >> s1 ==> s.
Proof.
  induction 1; sauto lq: on.
Qed.

Lemma lem_small_to_big_aux_2 : forall p p',
    p -->* p' -> forall c1 s1 c2 s2 s,
      p = (c1, s1) -> p' = (c2, s2) -> c2 >> s2 ==> s ->
      c1 >> s1 ==> s.
Proof.
  induction 1; sauto use: lem_small_to_big_aux.
Qed.

Lemma lem_small_to_big : forall c s s',
  (c, s) -->* (Nop, s') -> c >> s ==> s'.
Proof.
  enough (forall p p', p -->* p' ->
                       forall c s s', p = (c, s) -> p' = (Nop, s') ->
                                      c >> s ==> s') by eauto.
  induction 1; sauto l: on use: lem_small_to_big_aux_2.
Qed.

Corollary cor_big_iff_small :
  forall c s s', c >> s ==> s' <-> (c, s) -->* (Nop, s').
Proof.
  sauto use: lem_small_to_big, lem_big_to_small.
Qed.

(* Hoare triples *)

Definition assn := state -> Prop.

Definition HoareValid (P : assn) (c : cmd) (Q : assn): Prop :=
  forall s s', c >> s ==> s' -> P s -> Q s'.

Notation "|= {{ P }} c {{ Q }}" := (HoareValid P c Q).

(* Hoare logic *)

Definition entails (P Q : assn) : Prop := forall s, P s -> Q s.

Inductive Hoare : assn -> cmd -> assn -> Prop :=
| Hoare_Nop : forall P, Hoare P Nop P
| Hoare_Assign : forall P a x,
    Hoare (fun s => P s[[x := a]]) (x <- a) P
| Hoare_Seq : forall P Q R c1 c2,
    Hoare P c1 Q -> Hoare Q c2 R -> Hoare P (c1 ;; c2) R
| Hoare_If : forall P Q b c1 c2,
    Hoare (fun s => P s /\ bval s b) c1 Q ->
    Hoare (fun s => P s /\ negb (bval s b)) c2 Q ->
    Hoare P (If b Then c1 Else c2) Q
| Hoare_While : forall P b c,
    Hoare (fun s => P s /\ bval s b) c P ->
    Hoare P (While b Do c) (fun s => P s /\ negb (bval s b))
| Hoare_conseq: forall P P' Q Q' c,
    Hoare P c Q -> entails P' P -> entails Q Q' -> Hoare P' c Q'.

Notation "|- {{ s | P }} c {{ s' | Q }}" :=
  (Hoare (fun s => P) c (fun s' => Q)).
Notation "|- {{ s | P }} c {{ Q }}" := (Hoare (fun s => P) c Q).
Notation "|- {{ P }} c {{ s' | Q }}" := (Hoare P c (fun s' => Q)).
Notation "|- {{ P }} c {{ Q }}" := (Hoare P c Q).

Lemma lem_hoare_strengthen_pre : forall P P' Q c,
    entails P' P -> |- {{P}} c {{Q}} -> |- {{P'}} c {{Q}}.
Proof.
  sauto unfold: entails.
Qed.

Lemma lem_hoare_weaken_post : forall P Q Q' c,
    entails Q Q' -> |- {{P}} c {{Q}} -> |- {{P}} c {{Q'}}.
Proof.
  sauto unfold: entails.
Qed.


Lemma hoare_assign : forall (P Q : assn) x a,
    (forall s, P s -> Q s[[x := a]]) -> |- {{P}} x <- a {{Q}}.
Proof.
  sauto use: lem_hoare_strengthen_pre unfold: entails.
Qed.

Lemma hoare_while : forall b (P Q: assn) c,
    |- {{s | P s /\ bval s b}} c {{P}} ->
       (forall s, P s /\ negb (bval s b) -> Q s) ->
    |- {{P}} (While b Do c) {{Q}}.
Proof.
  sauto use: lem_hoare_weaken_post unfold: entails.
Qed.

(* Soundness of Hoare logic *)

Theorem thm_hoare_correct : forall P Q c,
    |- {{P}} c {{Q}} -> |= {{P}} c {{Q}}.
Proof.
  unfold HoareValid.
  induction 1.
  - sauto.
  - sauto.
  - sauto inv: BigStep.
  - sauto inv: BigStep.
  - intros *.
    remember (While b Do c).
    induction 1; qauto inv: BigStep.
  - sauto unfold: entails.
Qed.

(************************************************************************************)
(* Insertion sort *)

Require List.
Import List.ListNotations.
Open Scope list_scope.

Inductive Sorted : list nat -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y, x <= y ->
                         forall l, Sorted (y :: l) ->
                                   Sorted (x :: y :: l).

Fixpoint insert (l : list nat) (x : nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: l else h :: insert t x
  end.

Fixpoint isort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert (isort t) h
  end.

Lemma lem_insert_sorted_hlp :
  forall l y z, y <= z -> Sorted (y :: l) -> Sorted (y :: insert l z).
Proof.
  induction l; qauto use: Sorted, Nat.lt_le_incl inv: Sorted.
Qed.

Lemma lem_insert_sorted (l : list nat) (x : nat) :
  Sorted l -> Sorted (insert l x).
Proof.
  destruct l; hauto use: Sorted, lem_insert_sorted_hlp db: arith.
Qed.

Lemma lem_isort_sorted : forall l, Sorted (isort l).
Proof.
  induction l; sauto use: lem_insert_sorted.
Qed.

Require Import Sorting.Permutation.

Lemma lem_insert_perm : forall l x, Permutation (insert l x) (x :: l).
Proof.
  induction l; sauto.
Qed.

Lemma lem_isort_perm : forall l, Permutation (isort l) l.
Proof.
  induction l; sauto use: lem_insert_perm.
Qed.

Fixpoint sortedb (l : list nat) : bool :=
  match l with
  | [] => true
  | [x] => true
  | x :: (y :: l') as t => (x <=? y) && sortedb t
  end.

Lemma lem_sortedb_iff_sorted : forall l, sortedb l <-> Sorted l.
Proof.
  induction l; sauto brefl: on.
Qed.

Lemma lem_insert_sortedb_hlp : forall l y z,
    y <= z -> sortedb (y :: l) -> sortedb (y :: insert l z).
Proof.
  induction l; sauto brefl: on inv: - ctrs: - db: arith.
Qed.

Lemma lem_insert_sortedb : forall l x,
    sortedb l -> sortedb (insert l x).
Proof.
  destruct l; hauto brefl: on use: lem_insert_sortedb_hlp db: arith.
Qed.

Lemma lem_isort_sortedb : forall l, sortedb (isort l).
Proof.
  induction l; sauto use: lem_insert_sortedb.
Qed.

Inductive LeLst : nat -> list nat -> Prop :=
| LeLst_0 : forall n, LeLst n []
| LeLst_1 : forall n m l, n <= m -> LeLst n l -> LeLst n (m :: l).

Lemma lem_lelst_insert :
  forall l n m, n <= m -> LeLst n l -> LeLst n (insert l m).
Proof.
  induction l; sauto.
Qed.

Lemma lem_lelst_sorted :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  induction l; sauto use: Nat.le_trans.
Qed.

Lemma lem_insert_sorted_2 :
  forall l x, Sorted l -> Sorted (insert l x).
Proof.
  induction l as [|y l IH].
  - sauto.
  - intros x H.
    simpl.
    destruct (Nat.leb_spec x y) as [H1|H1].
    + constructor; assumption.
    + qauto use: lem_lelst_sorted, lem_lelst_insert, Nat.lt_le_incl.
Qed.

(* Tail-recursive reverse *)

Fixpoint itrev {A} (lst acc : list A) :=
  match lst with
  | [] => acc
  | h :: t => itrev t (h :: acc)
  end.

Definition rev {A} (lst : list A) := itrev lst [].

Lemma lem_itrev {A} :
  forall lst acc : list A, itrev lst acc = itrev lst [] ++ acc.
Proof.
  induction lst as [| h t IH].
  - auto.
  - assert (H: itrev t [h] = itrev t [] ++ [h]).
    { rewrite IH; reflexivity. }
    sauto db: slist.
Qed.

Lemma lem_rev_app {A} :
  forall l1 l2 : list A, rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  unfold rev.
  induction l1; sauto use: @lem_itrev db: slist.
Qed.

Lemma lem_rev_rev {A} : forall l : list A, rev (rev l) = l.
Proof.
  unfold rev.
  induction l as [| x l IH].
  - reflexivity.
  - sauto use: (lem_itrev l [x]), (lem_rev_app (itrev l []) [x]).
Qed.

Lemma lem_rev_lst {A} : forall l : list A, rev l = List.rev l.
Proof.
  unfold rev.
  induction l; sauto use: @lem_itrev.
Qed.

(* Permutations *)

Lemma lem_perm_length {A} :
  forall l1 l2 : list A, Permutation l1 l2 ->
    List.length l1 = List.length l2.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_perm_sym {A} :
  forall l1 l2 : list A, Permutation l1 l2 -> Permutation l2 l1.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_perm_forall {A} (P : A -> Prop) :
  forall l1 l2, Permutation l1 l2 ->
    List.Forall P l1 -> List.Forall P l2.
Proof.
  induction 1; sauto.
Qed.

(* Dependent types *)

Inductive type := Nat | Bool.

Inductive expr : type -> Type :=
| Var : nat -> expr Nat
| Plus : expr Nat -> expr Nat -> expr Nat
| Equal : expr Nat -> expr Nat -> expr Bool.

Lemma lem_testdep : forall e : expr Nat, match e with Var n => n >= 0 | _ => e = e end.
Proof.
  sauto dep: on.
Qed.

Require Import Program.Equality.

Module DependentExpressions.

Inductive type := Nat | Bool | Prod (ty1 ty2 : type).

Fixpoint tyeval (ty : type) : Type :=
  match ty with
  | Nat => nat
  | Bool => bool
  | Prod ty1 ty2 => tyeval ty1 * tyeval ty2
  end.

Inductive expr : type -> Type :=
| Var : nat -> expr Nat
| Plus : expr Nat -> expr Nat -> expr Nat
| Equal : expr Nat -> expr Nat -> expr Bool
| Pair : forall {A B}, expr A -> expr B -> expr (Prod A B)
| Fst : forall {A B}, expr (Prod A B) -> expr A
| Snd : forall {A B}, expr (Prod A B) -> expr B
| Const : forall A, tyeval A -> expr A
| Ite : forall {A}, expr Bool -> expr A -> expr A -> expr A.

Definition store := nat -> nat.

Fixpoint eval {A} (s : store) (e : expr A) : tyeval A :=
  match e with
  | Var n => s n
  | Plus e1 e2 => eval s e1 + eval s e2
  | Equal e1 e2 => eval s e1 =? eval s e2
  | Pair e1 e2 => (eval s e1, eval s e2)
  | Fst e => fst (eval s e)
  | Snd e => snd (eval s e)
  | Const _ c => c
  | Ite b e1 e2 => if eval s b then eval s e1 else eval s e2
  end.

Definition simp_plus (e1 e2 : expr Nat) :=
  match e1, e2 with
  | Const Nat n1, Const Nat n2 => Const Nat (n1 + n2)
  | _, Const Nat 0 => e1
  | Const Nat 0, _ => e2
  | _, _ => Plus e1 e2
  end.

Lemma lem_plus : forall s e1 e2,
  eval s (simp_plus e1 e2) = eval s e1 + eval s e2.
Proof.
  depind e1; sauto dep: on.
Qed.

Global Hint Rewrite lem_plus : simp_db.

Definition simp_equal (e1 e2 : expr Nat) :=
  match e1, e2 with
  | Const Nat n1, Const Nat n2 => Const Bool (n1 =? n2)
  | _, _ => Equal e1 e2
  end.

Lemma lem_equal : forall s e1 e2,
  eval s (simp_equal e1 e2) = (eval s e1 =? eval s e2).
Proof.
  depind e1; sauto dep: on.
Qed.

Global Hint Rewrite lem_equal : simp_db.

Definition unpair_type (T : type) :=
  option (match T with Prod A B => expr A * expr B | _ => unit end).

Definition unpair {A B : type} (e : expr (Prod A B)) :
  option (expr A * expr B) :=
  match e in expr T return unpair_type T with
  | Pair e1 e2 => Some (e1, e2)
  | _ => None
  end.

Definition simp_fst {A B : type} (e : expr (Prod A B)) : expr A :=
  match unpair e with
  | Some (e1, e2) => e1
  | None => Fst e
  end.

Lemma lem_fst {A B} : forall s (e : expr (Prod A B)),
  eval s (simp_fst e) = fst (eval s e).
Proof.
  depind e; sauto.
Qed.

Global Hint Rewrite @lem_fst : simp_db.

Definition simp_snd {A B : type} (e : expr (Prod A B)) : expr B :=
  match unpair e with
  | Some (e1, e2) => e2
  | None => Snd e
  end.

Lemma lem_snd {A B} : forall s (e : expr (Prod A B)),
  eval s (simp_snd e) = snd (eval s e).
Proof.
  depind e; sauto.
Qed.

Global Hint Rewrite @lem_snd : simp_db.

Definition simp_ite {A} (e : expr Bool) (e1 e2 : expr A) : expr A :=
  match e with
  | Const Bool true => e1
  | Const Bool false => e2
  | _ => Ite e e1 e2
  end.

Lemma lem_ite {A} : forall s e (e1 e2 : expr A),
    eval s (simp_ite e e1 e2) =
    if eval s e then eval s e1 else eval s e2.
Proof.
  depind e; sauto.
Qed.

Global Hint Rewrite @lem_ite : simp_db.

Fixpoint simp {A} (e : expr A) : expr A :=
  match e with
  | Var n => Var n
  | Plus e1 e2 => simp_plus (simp e1) (simp e2)
  | Equal e1 e2 => simp_equal (simp e1) (simp e2)
  | Pair e1 e2 => Pair (simp e1) (simp e2)
  | Fst e => simp_fst (simp e)
  | Snd e => simp_snd (simp e)
  | Const t c => Const t c
  | Ite e e1 e2 => simp_ite (simp e) (simp e1) (simp e2)
  end.

Lemma lem_simp {A} : forall s (e : expr A),
  eval s (simp e) = eval s e.
Proof.
  depind e; sauto db: simp_db.
Qed.

End DependentExpressions.

Require Import Recdef.
Require Import Program.

Module MergeSort.

Class DecTotalOrder (A : Type) := {
  leb : A -> A -> bool;
  leb_total_dec : forall x y, {leb x y}+{leb y x};
  leb_antisym : forall x y, leb x y -> leb y x -> x = y;
  leb_trans : forall x y z, leb x y -> leb y z -> leb x z }.

Arguments leb {A _}.
Arguments leb_total_dec {A _}.
Arguments leb_antisym {A _}.
Arguments leb_trans {A _}.

Global Instance dto_nat : DecTotalOrder nat.
Proof.
  apply Build_DecTotalOrder with (leb := Nat.leb);
    induction x; sauto.
Defined.

Definition eq_dec {A} {dto : DecTotalOrder A} : forall x y : A, {x = y}+{x <> y}.
  intros x y.
  sdestruct (leb x y).
  - sdestruct (leb y x).
    + auto using leb_antisym.
    + sauto.
  - sdestruct (leb y x).
    + sauto.
    + destruct (leb_total_dec x y); auto.
Defined.

Function lexb {A} {dto : DecTotalOrder A} (l1 l2 : list A) : bool :=
  match l1 with
  | [] => true
  | x :: l1' =>
    match l2 with
    | [] => false
    | y :: l2' =>
      if eq_dec x y then
        lexb l1' l2'
      else
        leb x y
    end
  end.

Global Instance dto_list {A} {dto_a : DecTotalOrder A} : DecTotalOrder (list A).
Proof.
  apply Build_DecTotalOrder with (leb := lexb).
  - induction x; sauto.
  - intros x y.
    functional induction (lexb x y).
    + sauto inv: list.
    + sauto.
    + sauto.
    + sauto inv: - use: leb_antisym.
  - intros x y.
    functional induction (lexb x y); sauto.
Defined.

Inductive Sorted {A} {dto : DecTotalOrder A} : list A -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y l, Sorted (y :: l) -> leb x y ->
                           Sorted (x :: y :: l).

Lemma lem_sorted_tail {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) -> Sorted l.
Proof.
  sauto.
Qed.

Definition LeLst {A} {dto : DecTotalOrder A} (x : A) :=
  List.Forall (leb x).

Lemma lem_lelst_trans {A} {dto : DecTotalOrder A} :
  forall l y, LeLst y l -> forall x, leb x y -> LeLst x l.
Proof.
  induction 1; sauto.
Qed.

Lemma lem_lelst_sorted {A} {dto : DecTotalOrder A} :
  forall l x, Sorted (x :: l) <-> LeLst x l /\ Sorted l.
Proof.
  induction l; sauto l: on use: lem_lelst_trans inv: Sorted, List.Forall ctrs: Sorted.
Qed.

Lemma lem_lelst_perm_rev {A} {dto : DecTotalOrder A} :
  forall l1 l2, Permutation l1 l2 -> forall x, LeLst x l2 -> LeLst x l1.
Proof.
  induction 1; sauto inv: List.Forall ctrs: List.Forall.
Qed.

Lemma lem_lelst_app {A} {dto : DecTotalOrder A} :
  forall l1 l2 x, LeLst x l1 -> LeLst x l2 -> LeLst x (l1 ++ l2).
Proof.
  induction 1; sauto.
Qed.

Global Hint Resolve lem_lelst_trans lem_lelst_perm_rev lem_lelst_app : lelst.

Lemma lem_sorted_concat_1 {A} {dto : DecTotalOrder A} :
  forall (l l1 l2 : list A) x y,
    Permutation l (l1 ++ y :: l2) -> Sorted (x :: l1) -> leb x y ->
    Sorted (y :: l2) -> Sorted l -> Sorted (x :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto use: lem_lelst_trans, lem_lelst_perm_rev, lem_lelst_app inv: -.
Qed.

Lemma lem_lelst_nil {A} {dto : DecTotalOrder A} : forall x, LeLst x [].
Proof.
  sauto.
Qed.

Lemma lem_lelst_cons {A} {dto : DecTotalOrder A} :
  forall x y l, LeLst x l -> leb x y -> LeLst x (y :: l).
Proof.
  sauto.
Qed.

Global Hint Resolve lem_lelst_nil lem_lelst_cons : lelst.

Lemma lem_sorted_concat_2 {A} {dto : DecTotalOrder A} :
  forall (l l1 l2 : list A) x y,
    Permutation l (x :: l1 ++ l2) -> Sorted (x :: l1) -> leb y x ->
    Sorted (y :: l2) -> Sorted l -> Sorted (y :: l).
Proof.
  intros.
  rewrite lem_lelst_sorted in *.
  sauto db: lelst inv: -.
Qed.

Program Fixpoint merge {A} {dto : DecTotalOrder A}
  (l1 l2 : {l | Sorted l}) {measure (List.length l1 + List.length l2)} :
  {l | Sorted l /\ Permutation l (l1 ++ l2)} :=
  match l1 with
  | [] => l2
  | h1 :: t1 =>
    match l2 with
    | [] => l1
    | h2 :: t2 =>
      if leb_total_dec h1 h2 then
        h1 :: merge t1 l2
      else
        h2 :: merge l1 t2
    end
  end.
Next Obligation.
  sauto db: list.
Qed.
Next Obligation.
  eauto using lem_sorted_tail.
Qed.
Next Obligation.
  sauto use: lem_sorted_concat_1.
Qed.
Next Obligation.
  eauto using lem_sorted_tail.
Qed.
Next Obligation.
  simpl; lia.
Qed.
Next Obligation.
  split.
  - sauto use: lem_sorted_concat_2.
  - simpl_sigma.
    rewrite List.app_comm_cons.
    apply Permutation_cons_app.
    intuition.
Qed.

Program Fixpoint split {A} (l : list A) {measure (List.length l)} :
  { (l1, l2) : list A * list A |
    List.length l1 + List.length l2 = List.length l /\
    List.length l1 <= List.length l2 + 1 /\ List.length l2 <= List.length l1 + 1 /\
    Permutation l (l1 ++ l2) } :=
  match l with
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t =>
    match split t with
    | (l1, l2) => (x :: l1, y :: l2)
    end
  end.
Solve Obligations with sauto use: Permutation_cons_app.

Lemma lem_split {A} : forall l : list A,
    2 <= List.length l ->
    forall l1 l2, (l1, l2) = ` (split l) ->
    List.length l1 < List.length l /\
    List.length l2 < List.length l.
Proof.
  sauto.
Qed.

Ltac use_lem_split :=
  match goal with
  | [ H: (?l1, ?l2) = ` (split ?l) |- _ ] =>
    let Hl := fresh "H" in
    assert (Hl: 2 <= List.length l);
    [ destruct l as [|? [| ? ? ] ]; simpl |
      generalize (lem_split l Hl l1 l2) ];
    hauto
  end.

Obligation Tactic := idtac.

Program Fixpoint mergesort {A} {dto : DecTotalOrder A} (l : list A)
  {measure (List.length l)} : {l' | Sorted l' /\ Permutation l' l} :=
  match l with
  | [] => []
  | [x] => [x]
  | _ =>
    match split l with
    | (l1, l2) => merge (mergesort l1) (mergesort l2)
    end
  end.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl; use_lem_split.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl; use_lem_split.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  split.
  - sauto.
  - qauto use: Permutation_app, Permutation_sym, perm_trans.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  program_simpl.
Defined.

End MergeSort.
