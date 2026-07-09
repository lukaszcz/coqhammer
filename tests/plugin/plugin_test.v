From Hammer Require Import Hammer.

Hammer_version.
Hammer_objects.
Hammer_prover_parse_test.

Lemma lem_1 {A : Type} (P : A -> Prop) : forall x, P x -> P x.
Proof.
  hammer.
Qed.

Lemma lem_2 {A : Type} (P Q : A -> Prop) : forall x, P x \/ Q x -> Q x \/ P x.
Proof.
  hammer.
Qed.

Lemma lem_3 {A : Type} (P Q : A -> Prop) : forall x, (forall x, P x -> Q x) -> P x -> Q x.
Proof.
  hammer.
Qed.

Lemma mult_1 : forall m n k : nat, m * n + k = k + n * m.
Proof.
  predict 16.
  hammer.
Qed.

(* Issue #156 / #141: SProp support, end-to-end via hammer. *)

From Stdlib Require Import StrictProp.

Fixpoint s_eq_nat (n m : nat) : SProp :=
  match n with
  | O => match m with O => sUnit | _ => sEmpty end
  | S n' => match m with O => sEmpty | S m' => s_eq_nat n' m' end
  end.

(* An SProp goal is proved and reconstructed. *)
Goal sUnit.
Proof. hammer. Qed.

(* An SProp goal with an SProp hypothesis: translation + reconstruction. *)
Lemma lem_sprop_id : forall n m, s_eq_nat n m -> s_eq_nat n m.
Proof. hammer. Qed.

(* The original #156 example. On old Rocq this raised a kernel anomaly
   ("kernel/inductive.ml ... Assertion failed"). It is fixed upstream on Rocq
   9.1; hammer now fails gracefully -- the ATPs cannot prove it because the
   SProp-recursive s_eq_nat is translated proof-irrelevantly (its computational
   content is lost), which is a completeness limitation, not a crash. We only
   assert the absence of an anomaly: a real kernel anomaly is a critical
   exception that "try" cannot swallow, so it would fail this file. *)
Goal forall n m, s_eq_nat n m -> n = m.
Proof. intros n m. try hammer. Abort.
