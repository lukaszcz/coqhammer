From Hammer Require Import Hammer.
From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Arith.Wf_nat FSets.FMapAVL Lia Logic.Eqdep_dec Logic.ProofIrrelevance MSets.MSetAVL Program.Wf Structures.OrderedTypeEx Structures.OrdersEx Vectors.Fin Vectors.Vector.

Module NatMap := FMapAVL.Make(OrderedTypeEx.Nat_as_OT).
Module NatSet := MSetAVL.Make(OrdersEx.Nat_as_OT).

Definition eval_vhead {A n} (v : Vector.t A (S n)) : A :=
  match v with Vector.cons _ x _ _ => x end.

Lemma dep_vector_head_cons :
  forall A n (x : A) (v : Vector.t A n),
    eval_vhead (Vector.cons A x n v) = x.
Proof.
  hammer_hook "dependent-slice" "dep_vector_head_cons".
  reflexivity.
Qed.

(* [Nat.eqb_spec] exposes both indexed constructors of [reflect].  Keep an
   elimination through the reflected value and an introduction goal so the
   corpus exercises the family in both polarities. *)
Definition dep_reflect_value (P : Prop) (b : bool) (r : reflect P b) : bool :=
  match r with ReflectT _ _ => true | ReflectF _ _ => false end.

Lemma dep_reflect_elim :
  forall n m, dep_reflect_value _ _ (Nat.eqb_spec n m) = Nat.eqb n m.
Proof.
  hammer_hook "dependent-slice" "dep_reflect_elim".
  intros n m. destruct (Nat.eqb_spec n m); reflexivity.
Qed.

Lemma dep_reflect_intro :
  forall n m, exists r : reflect (n = m) (Nat.eqb n m),
    r = Nat.eqb_spec n m.
Proof.
  hammer_hook "dependent-slice" "dep_reflect_intro".
  intros n m. exists (Nat.eqb_spec n m). reflexivity.
Qed.

(* [Vector.hd] rules out the nil constructor at a successor index. *)
Lemma dep_vector_hd_cons :
  forall A n (x : A) (v : Vector.t A n),
    Vector.hd (Vector.cons A x n v) = x.
Proof.
  hammer_hook "dependent-slice" "dep_vector_hd_cons".
  reflexivity.
Qed.

(* Every constructor of [Fin.t] has a successor result index, so [case0]
   presents only rigidly clashing branches at index zero. *)
Lemma dep_fin_zero_elim : forall f : Fin.t 0, False.
Proof.
  hammer_hook "dependent-slice" "dep_fin_zero_elim".
  exact (Fin.case0 (fun _ => False)).
Qed.

Lemma dep_fin_f1_zero : proj1_sig (Fin.to_nat (@Fin.F1 0)) = 0.
Proof.
  hammer_hook "dependent-slice" "dep_fin_f1_zero".
  reflexivity.
Qed.

(* A user-defined equality match, independently of the stdlib transport
   constants, at one type and composed across three types. *)
Definition dep_cast {A B : Type} (e : A = B) (x : A) : B :=
  match e in (_ = T) return T with eq_refl => x end.

Lemma dep_cast_refl :
  forall (A : Type) (x : A) (e : A = A), dep_cast e x = x.
Proof.
  hammer_hook "dependent-slice" "dep_cast_refl".
  intros A x e. rewrite (proof_irrelevance _ e (eq_refl A)). reflexivity.
Qed.

Lemma dep_cast_compose :
  forall (A B C : Type) (e1 : A = B) (e2 : B = C) (x : A),
    dep_cast e2 (dep_cast e1 x) = dep_cast (eq_trans e1 e2) x.
Proof.
  hammer_hook "dependent-slice" "dep_cast_compose".
  intros A B C e1 e2 x. destruct e1. simpl in e2. destruct e2. reflexivity.
Qed.

(* The constructor forces the family index from [n] while the projection
   erases its proof payload and returns the indexed subset carrier [k].  Omit
   generated recursors so this fixture's premise set isolates that projection. *)
Unset Elimination Schemes.
Inductive dep_ibounded : nat -> Set :=
| DepIBounded : forall n k, k < n -> dep_ibounded n.
Set Elimination Schemes.

Definition dep_ibval n (b : dep_ibounded n) : nat :=
  match b with DepIBounded _ k _ => k end.

Lemma dep_ibval_bound : forall n (b : dep_ibounded n), dep_ibval n b < n.
Proof.
  hammer_hook "dependent-slice" "dep_ibval_bound".
  intros n [n' k H]. exact H.
Qed.

Lemma dep_fmap_empty : NatMap.Empty (NatMap.empty nat).
Proof.
  hammer_hook "dependent-slice" "dep_fmap_empty".
  apply NatMap.empty_1.
Qed.

Lemma dep_mset_empty : NatSet.Empty NatSet.empty.
Proof.
  hammer_hook "dependent-slice" "dep_mset_empty".
  apply NatSet.empty_spec.
Qed.

Definition dep_transport (P : nat -> Type) (a b : nat) (e : a = b) (x : P a) : P b :=
  eq_rect a P x b e.

Lemma dep_eq_rect_refl :
  forall (P : nat -> Type) (x : P 0) (p : 0 = 0), dep_transport P 0 0 p x = x.
Proof.
  hammer_hook "dependent-slice" "dep_eq_rect_refl".
  intros P x p; rewrite (UIP_refl_nat 0 p); reflexivity.
Qed.

Program Fixpoint dep_idiv (a b : nat) (p : b <> 0) {measure a} : nat :=
  if le_lt_dec b a then S (dep_idiv (a - b) b p) else 0.
Next Obligation.
  lia.
Qed.

Lemma dep_idiv_zero : forall b p, dep_idiv 0 (S b) p = 0.
Proof.
  hammer_hook "dependent-slice" "dep_idiv_zero".
  intros b p.
  unfold dep_idiv, dep_idiv_func.
  rewrite fix_sub_eq.
  - simpl. destruct (le_lt_dec (S b) 0); lia.
  - intros [a [b0 p0]] f g Hfg.
    simpl. destruct (le_lt_dec b0 a); auto.
Qed.
