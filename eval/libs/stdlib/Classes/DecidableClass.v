From Hammer Require Import Hammer.













Class Decidable (P : Prop) := {
Decidable_witness : bool;
Decidable_spec : Decidable_witness = true <-> P
}.



Lemma Decidable_sound : forall P (H : Decidable P),
Decidable_witness = true -> P.
Proof. try hammer_hook "DecidableClass" "DecidableClass.Decidable_sound". Undo.  
intros P H Hp; apply -> Decidable_spec; assumption.
Qed.

Lemma Decidable_complete : forall P (H : Decidable P),
P -> Decidable_witness = true.
Proof. try hammer_hook "DecidableClass" "DecidableClass.Decidable_complete". Undo.  
intros P H Hp; apply <- Decidable_spec; assumption.
Qed.

Lemma Decidable_sound_alt : forall P (H : Decidable P),
~ P -> Decidable_witness = false.
Proof. try hammer_hook "DecidableClass" "DecidableClass.Decidable_sound_alt". Undo.  
intros P [wit spec] Hd; simpl; destruct wit; tauto.
Qed.

Lemma Decidable_complete_alt : forall P (H : Decidable P),
Decidable_witness = false -> ~ P.
Proof. try hammer_hook "DecidableClass" "DecidableClass.Decidable_complete_alt". Undo.  
intros P [wit spec] Hd Hc; simpl in *; intuition congruence.
Qed.



Definition decide P {H : Decidable P} := Decidable_witness (Decidable:=H).

Ltac _decide_ P H :=
let b := fresh "b" in
set (b := decide P) in *;
assert (H : decide P = b) by reflexivity;
clearbody b;
destruct b; [apply Decidable_sound in H|apply Decidable_complete_alt in H].

Tactic Notation "decide" constr(P) "as" ident(H) :=
_decide_ P H.

Tactic Notation "decide" constr(P) :=
let H := fresh "H" in _decide_ P H.



Require Import Bool Arith ZArith.

Program Instance Decidable_eq_bool : forall (x y : bool), Decidable (eq x y) := {
Decidable_witness := Bool.eqb x y
}.
Next Obligation.
apply eqb_true_iff.
Qed.

Program Instance Decidable_eq_nat : forall (x y : nat), Decidable (eq x y) := {
Decidable_witness := Nat.eqb x y
}.
Next Obligation.
apply Nat.eqb_eq.
Qed.

Program Instance Decidable_le_nat : forall (x y : nat), Decidable (x <= y) := {
Decidable_witness := Nat.leb x y
}.
Next Obligation.
apply Nat.leb_le.
Qed.

Program Instance Decidable_eq_Z : forall (x y : Z), Decidable (eq x y) := {
Decidable_witness := Z.eqb x y
}.
Next Obligation.
apply Z.eqb_eq.
Qed.
