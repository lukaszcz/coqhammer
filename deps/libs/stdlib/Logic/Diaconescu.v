From Hammer Require Import Hammer.















Section PredExt_RelChoice_imp_EM.



Definition PredicateExtensionality :=
forall P Q:bool -> Prop, (forall b:bool, P b <-> Q b) -> P = Q.



Require Import ClassicalFacts.

Variable pred_extensionality : PredicateExtensionality.

Lemma prop_ext : forall A B:Prop, (A <-> B) -> A = B.
Proof. hammer_hook "Diaconescu" "Diaconescu.prop_ext".  
intros A B H.
change ((fun _ => A) true = (fun _ => B) true).
rewrite
pred_extensionality with (P := fun _:bool => A) (Q := fun _:bool => B).
reflexivity.
intros _; exact H.
Qed.

Lemma proof_irrel : forall (A:Prop) (a1 a2:A), a1 = a2.
Proof. hammer_hook "Diaconescu" "Diaconescu.proof_irrel".  
apply (ext_prop_dep_proof_irrel_cic prop_ext).
Qed.



Require Import ChoiceFacts.

Variable rel_choice : RelationalChoice.

Lemma guarded_rel_choice : GuardedRelationalChoice.
Proof. hammer_hook "Diaconescu" "Diaconescu.guarded_rel_choice".  
apply
(rel_choice_and_proof_irrel_imp_guarded_rel_choice rel_choice proof_irrel).
Qed.



Require Import Bool.

Lemma AC_bool_subset_to_bool :
exists R : (bool -> Prop) -> bool -> Prop,
(forall P:bool -> Prop,
(exists b : bool, P b) ->
exists b : bool, P b /\ R P b /\ (forall b':bool, R P b' -> b = b')).
Proof. hammer_hook "Diaconescu" "Diaconescu.AC_bool_subset_to_bool".  
destruct (guarded_rel_choice _ _
(fun Q:bool -> Prop =>  exists y : _, Q y)
(fun (Q:bool -> Prop) (y:bool) => Q y)) as (R,(HRsub,HR)).
exact (fun _ H => H).
exists R; intros P HP.
destruct (HR P HP) as (y,(Hy,Huni)).
exists y; firstorder.
Qed.




Theorem pred_ext_and_rel_choice_imp_EM : forall P:Prop, P \/ ~ P.
Proof. hammer_hook "Diaconescu" "Diaconescu.pred_ext_and_rel_choice_imp_EM".  
intro P.


destruct AC_bool_subset_to_bool as [R H].

set (class_of_true := fun b => b = true \/ P).
set (class_of_false := fun b => b = false \/ P).


destruct (H class_of_true) as [b0 [H0 [H0' H0'']]].
exists true; left; reflexivity.
destruct H0.


destruct (H class_of_false) as [b1 [H1 [H1' H1'']]].
exists false; left; reflexivity.
destruct H1.


right.
intro HP.
assert (Hequiv : forall b:bool, class_of_true b <-> class_of_false b).
intro b; split.
unfold class_of_false; right; assumption.
unfold class_of_true; right; assumption.
assert (Heq : class_of_true = class_of_false).
apply pred_extensionality with (1 := Hequiv).
apply diff_true_false.
rewrite <- H0.
rewrite <- H1.
rewrite <- H0''. reflexivity.
rewrite Heq.
assumption.


left; assumption.
left; assumption.

Qed.

End PredExt_RelChoice_imp_EM.






Section ProofIrrel_RelChoice_imp_EqEM.

Variable rel_choice : RelationalChoice.

Variable proof_irrelevance : forall P:Prop , forall x y:P, x=y.



Variable A :Type.
Variables a1 a2 : A.



Definition A' := @sigT A (fun x => x=a1 \/ x=a2).

Definition a1':A'.
exists a1 ; auto.
Defined.

Definition a2':A'.
exists a2 ; auto.
Defined.



Lemma projT1_injective : a1=a2 -> a1'=a2'.
Proof. hammer_hook "Diaconescu" "Diaconescu.projT1_injective".  
intro Heq ; unfold a1', a2', A'.
rewrite Heq.
replace (or_introl (a2=a2) (eq_refl a2))
with (or_intror (a2=a2) (eq_refl a2)).
reflexivity.
apply proof_irrelevance.
Qed.



Lemma decide : forall x:A', exists y:bool ,
(projT1 x = a1 /\ y = true ) \/ (projT1 x = a2 /\ y = false).
Proof. hammer_hook "Diaconescu" "Diaconescu.decide".  
intros [a [Ha1|Ha2]]; [exists true | exists false]; auto.
Qed.



Theorem proof_irrel_rel_choice_imp_eq_dec : a1=a2 \/ ~a1=a2.
Proof. hammer_hook "Diaconescu" "Diaconescu.proof_irrel_rel_choice_imp_eq_dec".  
destruct
(rel_choice A' bool
(fun x y =>  projT1 x = a1 /\ y = true \/ projT1 x = a2 /\ y = false))
as (R,(HRsub,HR)).
apply decide.
destruct (HR a1') as (b1,(Ha1'b1,_Huni1)).
destruct (HRsub a1' b1 Ha1'b1) as [(_, Hb1true)|(Ha1a2, _Hb1false)].
destruct (HR a2') as (b2,(Ha2'b2,Huni2)).
destruct (HRsub a2' b2 Ha2'b2) as [(Ha2a1, _Hb2true)|(_, Hb2false)].
left; symmetry; assumption.
right; intro H.
subst b1; subst b2.
rewrite (projT1_injective H) in Ha1'b1.
assert (false = true) by auto using Huni2.
discriminate.
left; assumption.
Qed.



Declare Implicit Tactic auto.

Lemma proof_irrel_rel_choice_imp_eq_dec' : a1=a2 \/ ~a1=a2.
Proof. hammer_hook "Diaconescu" "Diaconescu.proof_irrel_rel_choice_imp_eq_dec'".  
assert (decide: forall x:A, x=a1 \/ x=a2 ->
exists y:bool, x=a1 /\ y=true \/ x=a2 /\ y=false).
intros a [Ha1|Ha2]; [exists true | exists false]; auto.
assert (guarded_rel_choice :=
rel_choice_and_proof_irrel_imp_guarded_rel_choice
rel_choice
proof_irrelevance).
destruct
(guarded_rel_choice A bool
(fun x => x=a1 \/ x=a2)
(fun x y => x=a1 /\ y=true \/ x=a2 /\ y=false))
as (R,(HRsub,HR)).
apply decide.
destruct (HR a1) as (b1,(Ha1b1,_Huni1)). left; reflexivity.
destruct (HRsub a1 b1 Ha1b1) as [(_, Hb1true)|(Ha1a2, _Hb1false)].
destruct (HR a2) as (b2,(Ha2b2,Huni2)). right; reflexivity.
destruct (HRsub a2 b2 Ha2b2) as [(Ha2a1, _Hb2true)|(_, Hb2false)].
left; symmetry; assumption.
right; intro H.
subst b1; subst b2; subst a1.
assert (false = true) by auto using Huni2, Ha1b1.
discriminate.
left; assumption.
Qed.

End ProofIrrel_RelChoice_imp_EqEM.






Local Notation inhabited A := A (only parsing).

Section ExtensionalEpsilon_imp_EM.

Variable epsilon : forall A : Type, inhabited A -> (A -> Prop) -> A.

Hypothesis epsilon_spec :
forall (A:Type) (i:inhabited A) (P:A->Prop),
(exists x, P x) -> P (epsilon A i P).

Hypothesis epsilon_extensionality :
forall (A:Type) (i:inhabited A) (P Q:A->Prop),
(forall a, P a <-> Q a) -> epsilon A i P = epsilon A i Q.

Local Notation eps := (epsilon bool true) (only parsing).

Theorem extensional_epsilon_imp_EM : forall P:Prop, P \/ ~ P.
Proof. hammer_hook "Diaconescu" "Diaconescu.extensional_epsilon_imp_EM".  
intro P.
pose (B := fun y => y=false \/ P).
pose (C := fun y => y=true  \/ P).
assert (B (eps B)) as [Hfalse|HP]
by (apply epsilon_spec; exists false; left; reflexivity).
assert (C (eps C)) as [Htrue|HP]
by (apply epsilon_spec; exists true; left; reflexivity).
right; intro HP.
assert (forall y, B y <-> C y) by (intro y; split; intro; right; assumption).
rewrite epsilon_extensionality with (1:=H) in Hfalse.
rewrite Htrue in Hfalse.
discriminate.
auto.
auto.
Qed.

End ExtensionalEpsilon_imp_EM.
