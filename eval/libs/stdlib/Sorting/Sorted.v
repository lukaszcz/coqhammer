From Hammer Require Import Hammer.













Require Import List Relations Relations_1.





Set Implicit Arguments.
Local Notation "[ ]" := nil (at level 0).
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) (at level 0).
Arguments Transitive [U] R.

Section defs.

Variable A : Type.
Variable R : A -> A -> Prop.



Inductive LocallySorted : list A -> Prop :=
| LSorted_nil : LocallySorted []
| LSorted_cons1 a : LocallySorted [a]
| LSorted_consn a b l :
LocallySorted (b :: l) -> R a b -> LocallySorted (a :: b :: l).



Inductive HdRel a : list A -> Prop :=
| HdRel_nil : HdRel a []
| HdRel_cons b l : R a b -> HdRel a (b :: l).

Inductive Sorted : list A -> Prop :=
| Sorted_nil : Sorted []
| Sorted_cons a l : Sorted l -> HdRel a l -> Sorted (a :: l).

Lemma HdRel_inv : forall a b l, HdRel a (b :: l) -> R a b.
Proof. hammer_hook "Sorted" "Sorted.HdRel_inv".  
inversion 1; auto.
Qed.

Lemma Sorted_inv :
forall a l, Sorted (a :: l) -> Sorted l /\ HdRel a l.
Proof. hammer_hook "Sorted" "Sorted.Sorted_inv".  
intros a l H; inversion H; auto.
Qed.

Lemma Sorted_rect :
forall P:list A -> Type,
P [] ->
(forall a l, Sorted l -> P l -> HdRel a l -> P (a :: l)) ->
forall l:list A, Sorted l -> P l.
Proof. hammer_hook "Sorted" "Sorted.Sorted_rect".  
induction l. firstorder using Sorted_inv. firstorder using Sorted_inv.
Qed.

Lemma Sorted_LocallySorted_iff : forall l, Sorted l <-> LocallySorted l.
Proof. hammer_hook "Sorted" "Sorted.Sorted_LocallySorted_iff".  
split; [induction 1 as [|a l [|]]| induction 1];
auto using Sorted, LocallySorted, HdRel.
inversion H1; subst; auto using LocallySorted.
Qed.



Inductive StronglySorted : list A -> Prop :=
| SSorted_nil : StronglySorted []
| SSorted_cons a l : StronglySorted l -> Forall (R a) l -> StronglySorted (a :: l).

Lemma StronglySorted_inv : forall a l, StronglySorted (a :: l) ->
StronglySorted l /\ Forall (R a) l.
Proof. hammer_hook "Sorted" "Sorted.StronglySorted_inv".  
intros; inversion H; auto.
Defined.

Lemma StronglySorted_rect :
forall P:list A -> Type,
P [] ->
(forall a l, StronglySorted l -> P l -> Forall (R a) l -> P (a :: l)) ->
forall l, StronglySorted l -> P l.
Proof. hammer_hook "Sorted" "Sorted.StronglySorted_rect".  
induction l; firstorder using StronglySorted_inv.
Defined.

Lemma StronglySorted_rec :
forall P:list A -> Type,
P [] ->
(forall a l, StronglySorted l -> P l -> Forall (R a) l -> P (a :: l)) ->
forall l, StronglySorted l -> P l.
Proof. hammer_hook "Sorted" "Sorted.StronglySorted_rec".  
firstorder using StronglySorted_rect.
Qed.

Lemma StronglySorted_Sorted : forall l, StronglySorted l -> Sorted l.
Proof. hammer_hook "Sorted" "Sorted.StronglySorted_Sorted".  
induction 1 as [|? ? ? ? HForall]; constructor; trivial.
destruct HForall; constructor; trivial.
Qed.

Lemma Sorted_extends :
Transitive R -> forall a l, Sorted (a::l) -> Forall (R a) l.
Proof. hammer_hook "Sorted" "Sorted.Sorted_extends".  
intros. change match a :: l with [] => True | a :: l => Forall (R a) l end.
induction H0 as [|? ? ? ? H1]; [trivial|].
destruct H1; constructor; trivial.
eapply Forall_impl; [|eassumption].
firstorder.
Qed.

Lemma Sorted_StronglySorted :
Transitive R -> forall l, Sorted l -> StronglySorted l.
Proof. hammer_hook "Sorted" "Sorted.Sorted_StronglySorted".  
induction 2; constructor; trivial.
apply Sorted_extends; trivial.
constructor; trivial.
Qed.

End defs.

Hint Constructors HdRel.
Hint Constructors Sorted.



Notation lelistA := HdRel (only parsing).
Notation nil_leA := HdRel_nil (only parsing).
Notation cons_leA := HdRel_cons (only parsing).

Notation sort := Sorted (only parsing).
Notation nil_sort := Sorted_nil (only parsing).
Notation cons_sort := Sorted_cons (only parsing).

Notation lelistA_inv := HdRel_inv (only parsing).
Notation sort_inv := Sorted_inv (only parsing).
Notation sort_rect := Sorted_rect (only parsing).

