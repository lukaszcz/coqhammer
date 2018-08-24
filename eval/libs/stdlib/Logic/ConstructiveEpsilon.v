From Hammer Require Import Hammer.























Section ConstructiveIndefiniteGroundDescription_Direct.

Variable P : nat -> Prop.

Hypothesis P_dec : forall n, {P n}+{~(P n)}.




Inductive before_witness (n:nat) : Prop :=
| stop : P n -> before_witness n
| next : before_witness (S n) -> before_witness n.


Fixpoint O_witness (n : nat) : before_witness n -> before_witness 0 :=
match n return (before_witness n -> before_witness 0) with
| 0 => fun b => b
| S n => fun b => O_witness n (next n b)
end.


Definition inv_before_witness :
forall n, before_witness n -> ~(P n) -> before_witness (S n) :=
fun n b =>
match b return ~ P n -> before_witness (S n) with
| stop _ p => fun not_p => match (not_p p) with end
| next _ b => fun _ => b
end.

Fixpoint linear_search m (b : before_witness m) : {n : nat | P n} :=
match P_dec m with
| left yes => exist (fun n => P n) m yes
| right no => linear_search (S m) (inv_before_witness m b no)
end.

Definition constructive_indefinite_ground_description_nat :
(exists n, P n) -> {n:nat | P n} :=
fun e => linear_search O (let (n, p) := e in O_witness n (stop n p)).

End ConstructiveIndefiniteGroundDescription_Direct.





Require Import Arith.

Section ConstructiveIndefiniteGroundDescription_Acc.

Variable P : nat -> Prop.

Hypothesis P_decidable : forall n : nat, {P n} + {~ P n}.



Let R (x y : nat) : Prop := x = S y /\ ~ P y.

Local Notation acc x := (Acc R x).

Lemma P_implies_acc : forall x : nat, P x -> acc x.
Proof. try hammer_hook "ConstructiveEpsilon" "ConstructiveEpsilon.P_implies_acc". Undo.  
intros x H. constructor.
intros y [_ not_Px]. absurd (P x); assumption.
Qed.

Lemma P_eventually_implies_acc : forall (x : nat) (n : nat), P (n + x) -> acc x.
Proof. try hammer_hook "ConstructiveEpsilon" "ConstructiveEpsilon.P_eventually_implies_acc". Undo.  
intros x n; generalize x; clear x; induction n as [|n IH]; simpl.
apply P_implies_acc.
intros x H. constructor. intros y [fxy _].
apply IH. rewrite fxy.
replace (n + S x) with (S (n + x)); auto with arith.
Defined.

Corollary P_eventually_implies_acc_ex : (exists n : nat, P n) -> acc 0.
Proof. try hammer_hook "ConstructiveEpsilon" "ConstructiveEpsilon.P_eventually_implies_acc_ex". Undo.  
intros H; elim H. intros x Px. apply P_eventually_implies_acc with (n := x).
replace (x + 0) with x; auto with arith.
Defined.



Theorem acc_implies_P_eventually : acc 0 -> {n : nat | P n}.
Proof. try hammer_hook "ConstructiveEpsilon" "ConstructiveEpsilon.acc_implies_P_eventually". Undo.  
intros Acc_0. pattern 0. apply Fix_F with (R := R); [| assumption].
clear Acc_0; intros x IH.
destruct (P_decidable x) as [Px | not_Px].
exists x; simpl; assumption.
set (y := S x).
assert (Ryx : R y x). unfold R; split; auto.
destruct (IH y Ryx) as [n Hn].
exists n; assumption.
Defined.

Theorem constructive_indefinite_ground_description_nat_Acc :
(exists n : nat, P n) -> {n : nat | P n}.
Proof. try hammer_hook "ConstructiveEpsilon" "ConstructiveEpsilon.constructive_indefinite_ground_description_nat_Acc". Undo.  
intros H; apply acc_implies_P_eventually.
apply P_eventually_implies_acc_ex; assumption.
Defined.

End ConstructiveIndefiniteGroundDescription_Acc.



Section ConstructiveGroundEpsilon_nat.

Variable P : nat -> Prop.

Hypothesis P_decidable : forall x : nat, {P x} + {~ P x}.

Definition constructive_ground_epsilon_nat (E : exists n : nat, P n) : nat
:= proj1_sig (constructive_indefinite_ground_description_nat P P_decidable E).

Definition constructive_ground_epsilon_spec_nat (E : (exists n, P n)) : P (constructive_ground_epsilon_nat E)
:= proj2_sig (constructive_indefinite_ground_description_nat P P_decidable E).

End ConstructiveGroundEpsilon_nat.



Section ConstructiveGroundEpsilon.



Variable A : Type.
Variable f : A -> nat.
Variable g : nat -> A.

Hypothesis gof_eq_id : forall x : A, g (f x) = x.

Variable P : A -> Prop.

Hypothesis P_decidable : forall x : A, {P x} + {~ P x}.

Definition P' (x : nat) : Prop := P (g x).

Lemma P'_decidable : forall n : nat, {P' n} + {~ P' n}.
Proof. try hammer_hook "ConstructiveEpsilon" "ConstructiveEpsilon.P'_decidable". Undo.  
intro n; unfold P'; destruct (P_decidable (g n)); auto.
Defined.

Lemma constructive_indefinite_ground_description : (exists x : A, P x) -> {x : A | P x}.
Proof. try hammer_hook "ConstructiveEpsilon" "ConstructiveEpsilon.constructive_indefinite_ground_description". Undo.  
intro H. assert (H1 : exists n : nat, P' n).
destruct H as [x Hx]. exists (f x); unfold P'. rewrite gof_eq_id; assumption.
apply (constructive_indefinite_ground_description_nat P' P'_decidable)  in H1.
destruct H1 as [n Hn]. exists (g n); unfold P' in Hn; assumption.
Defined.

Lemma constructive_definite_ground_description : (exists! x : A, P x) -> {x : A | P x}.
Proof. try hammer_hook "ConstructiveEpsilon" "ConstructiveEpsilon.constructive_definite_ground_description". Undo.  
intros; apply constructive_indefinite_ground_description; firstorder.
Defined.

Definition constructive_ground_epsilon (E : exists x : A, P x) : A
:= proj1_sig (constructive_indefinite_ground_description E).

Definition constructive_ground_epsilon_spec (E : (exists x, P x)) : P (constructive_ground_epsilon E)
:= proj2_sig (constructive_indefinite_ground_description E).

End ConstructiveGroundEpsilon.



Notation constructive_indefinite_description_nat :=
constructive_indefinite_ground_description_nat (only parsing).
Notation constructive_epsilon_spec_nat :=
constructive_ground_epsilon_spec_nat (only parsing).
Notation constructive_epsilon_nat :=
constructive_ground_epsilon_nat (only parsing).
Notation constructive_indefinite_description :=
constructive_indefinite_ground_description (only parsing).
Notation constructive_definite_description :=
constructive_definite_ground_description (only parsing).
Notation constructive_epsilon_spec :=
constructive_ground_epsilon_spec (only parsing).
Notation constructive_epsilon :=
constructive_ground_epsilon (only parsing).

