(* Harness smoke for the selected external corpus adapter (Coq-Equations).
   It is intentionally dependency-light: the full external run is populated by
   prepare-corpus.sh --source from a local Coq-Equations checkout, while this
   sample exercises the same Program/WF proof shapes during dry-runs. *)
From Hammer Require Import Hammer.
From Stdlib Require Import Arith.PeanoNat Lia Program.Wf.

Program Definition bounded_pred (n : nat) : {m : nat | m <= n} :=
  match n with
  | 0 => 0
  | S k => k
  end.
Lemma external_program_bounded_pred : forall n, proj1_sig (bounded_pred n) <= n.
Proof.
  hammer_hook "external-equations" "external_program_bounded_pred".
  intros n; apply proj2_sig.
Qed.

Program Fixpoint fuel_drop (fuel n : nat) {measure fuel} : nat :=
  match fuel with
  | 0 => n
  | S fuel' => fuel_drop fuel' (Nat.pred n)
  end.
Lemma external_program_fuel_drop_zero : forall n, fuel_drop 0 n = n.
Proof.
  hammer_hook "external-equations" "external_program_fuel_drop_zero".
  reflexivity.
Qed.
