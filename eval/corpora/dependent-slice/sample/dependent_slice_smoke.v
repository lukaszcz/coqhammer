From Hammer Require Import Hammer.
From Stdlib Require Import Arith.Compare_dec Arith.PeanoNat Arith.Wf_nat FSets.FMapAVL Lia Logic.Eqdep_dec MSets.MSetAVL Program.Wf Structures.OrderedTypeEx Structures.OrdersEx Vectors.Fin Vectors.Vector.

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

Lemma dep_fin_f1_zero : proj1_sig (Fin.to_nat (@Fin.F1 0)) = 0.
Proof.
  hammer_hook "dependent-slice" "dep_fin_f1_zero".
  reflexivity.
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
