From Hammer Require Import Hammer.









Set Implicit Arguments.

Require Import Notations.
Require Import Logic.
Declare ML Module "nat_syntax_plugin".






Inductive Empty_set : Set :=.



Inductive unit : Set :=
tt : unit.







Inductive bool : Set :=
| true : bool
| false : bool.

Add Printing If bool.

Delimit Scope bool_scope with bool.

Bind Scope bool_scope with bool.



Definition andb (b1 b2:bool) : bool := if b1 then b2 else false.

Definition orb (b1 b2:bool) : bool := if b1 then true else b2.

Definition implb (b1 b2:bool) : bool := if b1 then b2 else true.

Definition xorb (b1 b2:bool) : bool :=
match b1, b2 with
| true, true => false
| true, false => true
| false, true => true
| false, false => false
end.

Definition negb (b:bool) := if b then false else true.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.



Lemma andb_prop : forall a b:bool, andb a b = true -> a = true /\ b = true.
Proof. hammer_hook "Datatypes" "Datatypes.andb_prop".  
destruct a, b; repeat split; assumption.
Qed.
Hint Resolve andb_prop: bool.

Lemma andb_true_intro :
forall b1 b2:bool, b1 = true /\ b2 = true -> andb b1 b2 = true.
Proof. hammer_hook "Datatypes" "Datatypes.andb_true_intro".  
destruct b1; destruct b2; simpl; intros [? ?]; assumption.
Qed.
Hint Resolve andb_true_intro: bool.



Inductive eq_true : bool -> Prop := is_eq_true : eq_true true.

Hint Constructors eq_true : eq_true.



Definition is_true b := b = true.





Lemma eq_true_ind_r :
forall (P : bool -> Prop) (b : bool), P b -> eq_true b -> P true.
Proof. hammer_hook "Datatypes" "Datatypes.eq_true_ind_r".  
intros P b H H0; destruct H0 in H; assumption.
Defined.

Lemma eq_true_rec_r :
forall (P : bool -> Set) (b : bool), P b -> eq_true b -> P true.
Proof. hammer_hook "Datatypes" "Datatypes.eq_true_rec_r".  
intros P b H H0; destruct H0 in H; assumption.
Defined.

Lemma eq_true_rect_r :
forall (P : bool -> Type) (b : bool), P b -> eq_true b -> P true.
Proof. hammer_hook "Datatypes" "Datatypes.eq_true_rect_r".  
intros P b H H0; destruct H0 in H; assumption.
Defined.



Inductive BoolSpec (P Q : Prop) : bool -> Prop :=
| BoolSpecT : P -> BoolSpec P Q true
| BoolSpecF : Q -> BoolSpec P Q false.
Hint Constructors BoolSpec.







Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.









Inductive option (A:Type) : Type :=
| Some : A -> option A
| None : option A.

Arguments Some {A} a.
Arguments None {A}.

Definition option_map (A B:Type) (f:A->B) (o : option A) : option B :=
match o with
| Some a => @Some B (f a)
| None => @None B
end.



Inductive sum (A B:Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.



Inductive prod (A B:Type) : Type :=
pair : A -> B -> prod A B.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Arguments pair {A B} _ _.

Section projections.
Context {A : Type} {B : Type}.

Definition fst (p:A * B) := match p with
| (x, y) => x
end.
Definition snd (p:A * B) := match p with
| (x, y) => y
end.
End projections.

Hint Resolve pair inl inr: core.

Lemma surjective_pairing :
forall (A B:Type) (p:A * B), p = pair (fst p) (snd p).
Proof. hammer_hook "Datatypes" "Datatypes.surjective_pairing".  
destruct p; reflexivity.
Qed.

Lemma injective_projections :
forall (A B:Type) (p1 p2:A * B),
fst p1 = fst p2 -> snd p1 = snd p2 -> p1 = p2.
Proof. hammer_hook "Datatypes" "Datatypes.injective_projections".  
destruct p1; destruct p2; simpl; intros Hfst Hsnd.
rewrite Hfst; rewrite Hsnd; reflexivity.
Qed.

Definition prod_uncurry (A B C:Type) (f:prod A B -> C)
(x:A) (y:B) : C := f (pair x y).

Definition prod_curry (A B C:Type) (f:A -> B -> C)
(p:prod A B) : C := match p with
| pair x y => f x y
end.



Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.
Infix "::" := cons (at level 60, right associativity) : list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Local Open Scope list_scope.

Definition length (A : Type) : list A -> nat :=
fix length l :=
match l with
| nil => O
| _ :: l' => S (length l')
end.



Definition app (A : Type) : list A -> list A -> list A :=
fix app l m :=
match l with
| nil => m
| a :: l1 => a :: app l1 m
end.


Infix "++" := app (right associativity, at level 60) : list_scope.






Inductive comparison : Set :=
| Eq : comparison
| Lt : comparison
| Gt : comparison.

Lemma comparison_eq_stable : forall c c' : comparison, ~~ c = c' -> c = c'.
Proof. hammer_hook "Datatypes" "Datatypes.comparison_eq_stable".  
destruct c, c'; intro H; reflexivity || destruct H; discriminate.
Qed.

Definition CompOpp (r:comparison) :=
match r with
| Eq => Eq
| Lt => Gt
| Gt => Lt
end.

Lemma CompOpp_involutive : forall c, CompOpp (CompOpp c) = c.
Proof. hammer_hook "Datatypes" "Datatypes.CompOpp_involutive".  
destruct c; reflexivity.
Qed.

Lemma CompOpp_inj : forall c c', CompOpp c = CompOpp c' -> c = c'.
Proof. hammer_hook "Datatypes" "Datatypes.CompOpp_inj".  
destruct c; destruct c'; auto; discriminate.
Qed.

Lemma CompOpp_iff : forall c c', CompOpp c = c' <-> c = CompOpp c'.
Proof. hammer_hook "Datatypes" "Datatypes.CompOpp_iff".  
split; intros; apply CompOpp_inj; rewrite CompOpp_involutive; auto.
Qed.



Inductive CompareSpec (Peq Plt Pgt : Prop) : comparison -> Prop :=
| CompEq : Peq -> CompareSpec Peq Plt Pgt Eq
| CompLt : Plt -> CompareSpec Peq Plt Pgt Lt
| CompGt : Pgt -> CompareSpec Peq Plt Pgt Gt.
Hint Constructors CompareSpec.



Inductive CompareSpecT (Peq Plt Pgt : Prop) : comparison -> Type :=
| CompEqT : Peq -> CompareSpecT Peq Plt Pgt Eq
| CompLtT : Plt -> CompareSpecT Peq Plt Pgt Lt
| CompGtT : Pgt -> CompareSpecT Peq Plt Pgt Gt.
Hint Constructors CompareSpecT.

Lemma CompareSpec2Type : forall Peq Plt Pgt c,
CompareSpec Peq Plt Pgt c -> CompareSpecT Peq Plt Pgt c.
Proof. hammer_hook "Datatypes" "Datatypes.CompareSpec2Type".  
destruct c; intros H; constructor; inversion_clear H; auto.
Defined.



Definition CompSpec {A} (eq lt : A->A->Prop)(x y:A) : comparison -> Prop :=
CompareSpec (eq x y) (lt x y) (lt y x).

Definition CompSpecT {A} (eq lt : A->A->Prop)(x y:A) : comparison -> Type :=
CompareSpecT (eq x y) (lt x y) (lt y x).
Hint Unfold CompSpec CompSpecT.

Lemma CompSpec2Type : forall A (eq lt:A->A->Prop) x y c,
CompSpec eq lt x y c -> CompSpecT eq lt x y c.
Proof. hammer_hook "Datatypes" "Datatypes.CompSpec2Type".   intros. apply CompareSpec2Type; assumption. Defined.






Inductive identity (A:Type) (a:A) : A -> Type :=
identity_refl : identity a a.
Hint Resolve identity_refl: core.

Arguments identity_ind [A] a P f y i.
Arguments identity_rec [A] a P f y i.
Arguments identity_rect [A] a P f y i.



Definition ID := forall A:Type, A -> A.
Definition id : ID := fun A x => x.

Definition IDProp := forall A:Prop, A -> A.
Definition idProp : IDProp := fun A x => x.






Notation prodT := prod (compat "8.2").
Notation pairT := pair (compat "8.2").
Notation prodT_rect := prod_rect (compat "8.2").
Notation prodT_rec := prod_rec (compat "8.2").
Notation prodT_ind := prod_ind (compat "8.2").
Notation fstT := fst (compat "8.2").
Notation sndT := snd (compat "8.2").
Notation prodT_uncurry := prod_uncurry (compat "8.2").
Notation prodT_curry := prod_curry (compat "8.2").


