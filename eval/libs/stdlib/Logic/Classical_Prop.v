From Hammer Require Import Hammer.















Require Import ClassicalFacts.

Hint Unfold not: core.

Axiom classic : forall P:Prop, P \/ ~ P.

Lemma NNPP : forall p:Prop, ~ ~ p -> p.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.NNPP".  
unfold not; intros; elim (classic p); auto.
intro NP; elim (H NP).
Qed.



Lemma Peirce : forall P:Prop, ((P -> False) -> P) -> P.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.Peirce".  
intros P H; destruct (classic P); auto.
Qed.

Lemma not_imply_elim : forall P Q:Prop, ~ (P -> Q) -> P.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.not_imply_elim".  
intros; apply NNPP; red.
intro; apply H; intro; absurd P; trivial.
Qed.

Lemma not_imply_elim2 : forall P Q:Prop, ~ (P -> Q) -> ~ Q.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.not_imply_elim2".  
tauto.
Qed.

Lemma imply_to_or : forall P Q:Prop, (P -> Q) -> ~ P \/ Q.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.imply_to_or".  
intros; elim (classic P); auto.
Qed.

Lemma imply_to_and : forall P Q:Prop, ~ (P -> Q) -> P /\ ~ Q.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.imply_to_and".  
intros; split.
apply not_imply_elim with Q; trivial.
apply not_imply_elim2 with P; trivial.
Qed.

Lemma or_to_imply : forall P Q:Prop, ~ P \/ Q -> P -> Q.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.or_to_imply".  
tauto.
Qed.

Lemma not_and_or : forall P Q:Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.not_and_or".  
intros; elim (classic P); auto.
Qed.

Lemma or_not_and : forall P Q:Prop, ~ P \/ ~ Q -> ~ (P /\ Q).
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.or_not_and".  
simple induction 1; red; simple induction 2; auto.
Qed.

Lemma not_or_and : forall P Q:Prop, ~ (P \/ Q) -> ~ P /\ ~ Q.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.not_or_and".  
tauto.
Qed.

Lemma and_not_or : forall P Q:Prop, ~ P /\ ~ Q -> ~ (P \/ Q).
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.and_not_or".  
tauto.
Qed.

Lemma imply_and_or : forall P Q:Prop, (P -> Q) -> P \/ Q -> Q.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.imply_and_or".  
tauto.
Qed.

Lemma imply_and_or2 : forall P Q R:Prop, (P -> Q) -> P \/ R -> Q \/ R.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.imply_and_or2".  
tauto.
Qed.

Lemma proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.proof_irrelevance".  exact (proof_irrelevance_cci classic). Qed.




Ltac classical_right := match goal with
|- ?X \/ _ => (elim (classic X);intro;[left;trivial|right])
end.

Ltac classical_left := match goal with
|- _ \/ ?X => (elim (classic X);intro;[right;trivial|left])
end.

Require Export EqdepFacts.

Module Eq_rect_eq.

Lemma eq_rect_eq :
forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Proof. try hammer_hook "Classical_Prop" "Classical_Prop.Eq_rect_eq.eq_rect_eq".  
intros; rewrite proof_irrelevance with (p1:=h) (p2:=eq_refl p); reflexivity.
Qed.

End Eq_rect_eq.

Module EqdepTheory := EqdepTheory(Eq_rect_eq).
Export EqdepTheory.
