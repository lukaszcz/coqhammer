(* Focused fixtures for guarded singleton-elimination premises. *)

From Hammer Require Import Hammer.
From Stdlib Require Import Arith.Wf_nat Logic.JMeq.

Inductive indexed_singleton : Type -> Prop :=
| indexed_nat : indexed_singleton nat.

(* N3: this singleton is indexed by a proof, and proposition-valued index
   formals are intentionally absent from the residual first-order equations. *)
Inductive prop_index_singleton (P : Prop) : P -> Prop :=
| prop_index_intro : forall p : P, prop_index_singleton P p.

Definition singleton_value (T : Type) (p : indexed_singleton T) : T :=
  match p in indexed_singleton U return U with
  | indexed_nat => 0
  end.

Definition prop_index_value
    (P : Prop) (p : P) (w : prop_index_singleton P p) : nat :=
  match w with
  | prop_index_intro _ _ => 3
  end.

Definition singleton_cast (A B : Type) (e : A = B) (x : A) : B :=
  match e in (_ = T) return T with
  | eq_refl => x
  end.

Definition singleton_jmeq
    (A B : Type) (x : A) (y : B) (e : JMeq x y) : A :=
  match e with
  | JMeq_refl => x
  end.

Hammer_transl "singleton_value".
Hammer_transl "prop_index_value".
Hammer_transl "singleton_cast".
Hammer_transl "singleton_jmeq".
Hammer_transl "eq_rect".
Hammer_transl "Acc_rect".
