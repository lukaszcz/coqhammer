From Hammer Require Import Hammer.











Set Implicit Arguments.

Require Import Notations.
Require Import Logic.
Require Import Datatypes.



Section Well_founded.

Variable A : Type.
Variable R : A -> A -> Prop.




Inductive Acc (x: A) : Prop :=
Acc_intro : (forall y:A, R y x -> Acc y) -> Acc x.

Lemma Acc_inv : forall x:A, Acc x -> forall y:A, R y x -> Acc y.
destruct 1; trivial.
Defined.

Global Arguments Acc_inv [x] _ [y] _, [x] _ y _.



Definition well_founded := forall a:A, Acc a.



Hypothesis Rwf : well_founded.

Theorem well_founded_induction_type :
forall P:A -> Type,
(forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
Proof. try hammer_hook "Wf" "Wf.well_founded_induction_type".  
intros; apply Acc_rect; auto.
Defined.

Theorem well_founded_induction :
forall P:A -> Set,
(forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
Proof. try hammer_hook "Wf" "Wf.well_founded_induction".  
exact (fun P:A -> Set => well_founded_induction_type P).
Defined.

Theorem well_founded_ind :
forall P:A -> Prop,
(forall x:A, (forall y:A, R y x -> P y) -> P x) -> forall a:A, P a.
Proof. try hammer_hook "Wf" "Wf.well_founded_ind".  
exact (fun P:A -> Prop => well_founded_induction_type P).
Defined.



Section FixPoint.

Variable P : A -> Type.
Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

Fixpoint Fix_F (x:A) (a:Acc x) : P x :=
F (fun (y:A) (h:R y x) => Fix_F (Acc_inv a h)).

Scheme Acc_inv_dep := Induction for Acc Sort Prop.

Lemma Fix_F_eq :
forall (x:A) (r:Acc x),
F (fun (y:A) (p:R y x) => Fix_F (x:=y) (Acc_inv r p)) = Fix_F (x:=x) r.
Proof. try hammer_hook "Wf" "Wf.Fix_F_eq".  
destruct r using Acc_inv_dep; auto.
Qed.

Definition Fix (x:A) := Fix_F (Rwf x).



Hypothesis
F_ext :
forall (x:A) (f g:forall y:A, R y x -> P y),
(forall (y:A) (p:R y x), f y p = g y p) -> F f = F g.

Lemma Fix_F_inv : forall (x:A) (r s:Acc x), Fix_F r = Fix_F s.
Proof. try hammer_hook "Wf" "Wf.Fix_F_inv".  
intro x; induction (Rwf x); intros.
rewrite <- (Fix_F_eq r); rewrite <- (Fix_F_eq s); intros.
apply F_ext; auto.
Qed.

Lemma Fix_eq : forall x:A, Fix x = F (fun (y:A) (p:R y x) => Fix y).
Proof. try hammer_hook "Wf" "Wf.Fix_eq".  
intro x; unfold Fix.
rewrite <- Fix_F_eq.
apply F_ext; intros.
apply Fix_F_inv.
Qed.

End FixPoint.

End Well_founded.



Section Well_founded_2.

Variables A B : Type.
Variable R : A * B -> A * B -> Prop.

Variable P : A -> B -> Type.

Section FixPoint_2.

Variable
F :
forall (x:A) (x':B),
(forall (y:A) (y':B), R (y, y') (x, x') -> P y y') -> P x x'.

Fixpoint Fix_F_2 (x:A) (x':B) (a:Acc R (x, x')) : P x x' :=
F
(fun (y:A) (y':B) (h:R (y, y') (x, x')) =>
Fix_F_2 (x:=y) (x':=y') (Acc_inv a (y,y') h)).

End FixPoint_2.

Hypothesis Rwf : well_founded R.

Theorem well_founded_induction_type_2 :
(forall (x:A) (x':B),
(forall (y:A) (y':B), R (y, y') (x, x') -> P y y') -> P x x') ->
forall (a:A) (b:B), P a b.
Proof. try hammer_hook "Wf" "Wf.well_founded_induction_type_2".  
intros; apply Fix_F_2; auto.
Defined.

End Well_founded_2.

Notation Acc_iter   := Fix_F   (only parsing).
Notation Acc_iter_2 := Fix_F_2 (only parsing).




Section Acc_generator.
Variable A : Type.
Variable R : A -> A -> Prop.


Fixpoint Acc_intro_generator n (wf : well_founded R)  :=
match n with
| O => wf
| S n => fun x => Acc_intro x (fun y _ => Acc_intro_generator n (Acc_intro_generator n wf) y)
end.


End Acc_generator.
