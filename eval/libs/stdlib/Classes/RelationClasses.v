From Hammer Require Import Hammer.












Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.



Section Defs.
Context {A : Type}.



Class Reflexive (R : relation A) :=
reflexivity : forall x : A, R x x.

Definition complement (R : relation A) : relation A := fun x y => R x y -> False.


Typeclasses Opaque complement.


Lemma complement_inverse R : complement (flip R) = flip (complement R).
Proof. hammer_hook "RelationClasses" "RelationClasses.complement_inverse". Restart.  reflexivity. Qed.

Class Irreflexive (R : relation A) :=
irreflexivity : Reflexive (complement R).

Class Symmetric (R : relation A) :=
symmetry : forall {x y}, R x y -> R y x.

Class Asymmetric (R : relation A) :=
asymmetry : forall {x y}, R x y -> R y x -> False.

Class Transitive (R : relation A) :=
transitivity : forall {x y z}, R x y -> R y z -> R x z.





Class PreOrder (R : relation A) : Prop := {
PreOrder_Reflexive :> Reflexive R | 2 ;
PreOrder_Transitive :> Transitive R | 2 }.



Class StrictOrder (R : relation A) : Prop := {
StrictOrder_Irreflexive :> Irreflexive R ;
StrictOrder_Transitive :> Transitive R }.


Global Instance StrictOrder_Asymmetric `(StrictOrder R) : Asymmetric R.
Proof. hammer_hook "RelationClasses" "RelationClasses.StrictOrder_Asymmetric". Restart.  firstorder. Qed.



Class PER (R : relation A) : Prop := {
PER_Symmetric :> Symmetric R | 3 ;
PER_Transitive :> Transitive R | 3 }.



Class Equivalence (R : relation A) : Prop := {
Equivalence_Reflexive :> Reflexive R ;
Equivalence_Symmetric :> Symmetric R ;
Equivalence_Transitive :> Transitive R }.



Global Instance Equivalence_PER {R} `(E:Equivalence R) : PER R | 10 :=
{ }.



Global Instance Equivalence_PreOrder {R} `(E:Equivalence R) : PreOrder R | 10 :=
{ }.



Class Antisymmetric eqA `{equ : Equivalence eqA} (R : relation A) :=
antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

Class subrelation (R R' : relation A) : Prop :=
is_subrelation : forall {x y}, R x y -> R' x y.



Lemma subrelation_symmetric R `(Symmetric R) : subrelation (flip R) R.
Proof. hammer_hook "RelationClasses" "RelationClasses.subrelation_symmetric". Restart.  hnf. intros. red in H0. apply symmetry. assumption. Qed.

Section flip.

Lemma flip_Reflexive `{Reflexive R} : Reflexive (flip R).
Proof. hammer_hook "RelationClasses" "RelationClasses.flip_Reflexive". Restart.  tauto. Qed.

Program Definition flip_Irreflexive `(Irreflexive R) : Irreflexive (flip R) :=
irreflexivity (R:=R).

Program Definition flip_Symmetric `(Symmetric R) : Symmetric (flip R) :=
fun x y H => symmetry (R:=R) H.

Program Definition flip_Asymmetric `(Asymmetric R) : Asymmetric (flip R) :=
fun x y H H' => asymmetry (R:=R) H H'.

Program Definition flip_Transitive `(Transitive R) : Transitive (flip R) :=
fun x y z H H' => transitivity (R:=R) H' H.

Program Definition flip_Antisymmetric `(Antisymmetric eqA R) :
Antisymmetric eqA (flip R).
Proof. hammer_hook "RelationClasses" "RelationClasses.flip_Antisymmetric". Restart.  firstorder. Qed.



Lemma flip_PreOrder `(PreOrder R) : PreOrder (flip R).
Proof. hammer_hook "RelationClasses" "RelationClasses.flip_PreOrder". Restart.  firstorder. Qed.

Lemma flip_StrictOrder `(StrictOrder R) : StrictOrder (flip R).
Proof. hammer_hook "RelationClasses" "RelationClasses.flip_StrictOrder". Restart.  firstorder. Qed.

Lemma flip_PER `(PER R) : PER (flip R).
Proof. hammer_hook "RelationClasses" "RelationClasses.flip_PER". Restart.  firstorder. Qed.

Lemma flip_Equivalence `(Equivalence R) : Equivalence (flip R).
Proof. hammer_hook "RelationClasses" "RelationClasses.flip_Equivalence". Restart.  firstorder. Qed.

End flip.

Section complement.

Definition complement_Irreflexive `(Reflexive R)
: Irreflexive (complement R).
Proof. hammer_hook "RelationClasses" "RelationClasses.complement_Irreflexive". Restart.  firstorder. Qed.

Definition complement_Symmetric `(Symmetric R) : Symmetric (complement R).
Proof. hammer_hook "RelationClasses" "RelationClasses.complement_Symmetric". Restart.  firstorder. Qed.
End complement.




Class RewriteRelation (RA : relation A).



Global Instance equivalence_rewrite_relation `(Equivalence eqA) : RewriteRelation eqA.


Section Leibniz.
Global Instance eq_Reflexive : Reflexive (@eq A) := @eq_refl A.
Global Instance eq_Symmetric : Symmetric (@eq A) := @eq_sym A.
Global Instance eq_Transitive : Transitive (@eq A) := @eq_trans A.



Global Program Instance eq_equivalence : Equivalence (@eq A) | 10.
End Leibniz.

End Defs.


Instance: RewriteRelation impl.
Instance: RewriteRelation iff.


Hint Extern 1 (Reflexive (complement _)) => class_apply @irreflexivity : typeclass_instances.
Hint Extern 3 (Symmetric (complement _)) => class_apply complement_Symmetric : typeclass_instances.
Hint Extern 3 (Irreflexive (complement _)) => class_apply complement_Irreflexive : typeclass_instances.

Hint Extern 3 (Reflexive (flip _)) => apply flip_Reflexive : typeclass_instances.
Hint Extern 3 (Irreflexive (flip _)) => class_apply flip_Irreflexive : typeclass_instances.
Hint Extern 3 (Symmetric (flip _)) => class_apply flip_Symmetric : typeclass_instances.
Hint Extern 3 (Asymmetric (flip _)) => class_apply flip_Asymmetric : typeclass_instances.
Hint Extern 3 (Antisymmetric (flip _)) => class_apply flip_Antisymmetric : typeclass_instances.
Hint Extern 3 (Transitive (flip _)) => class_apply flip_Transitive : typeclass_instances.
Hint Extern 3 (StrictOrder (flip _)) => class_apply flip_StrictOrder : typeclass_instances.
Hint Extern 3 (PreOrder (flip _)) => class_apply flip_PreOrder : typeclass_instances.

Hint Extern 4 (subrelation (flip _) _) =>
class_apply @subrelation_symmetric : typeclass_instances.

Arguments irreflexivity {A R Irreflexive} [x] _.
Arguments symmetry {A} {R} {_} [x] [y] _.
Arguments asymmetry {A} {R} {_} [x] [y] _ _.
Arguments transitivity {A} {R} {_} [x] [y] [z] _ _.
Arguments Antisymmetric A eqA {_} _.

Hint Resolve irreflexivity : ord.

Unset Implicit Arguments.



Ltac solve_relation :=
match goal with
| [ |- ?R ?x ?x ] => reflexivity
| [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry ; exact H
end.

Hint Extern 4 => solve_relation : relations.





Ltac reduce_hyp H :=
match type of H with
| context [ _ <-> _ ] => fail 1
| _ => red in H ; try reduce_hyp H
end.

Ltac reduce_goal :=
match goal with
| [ |- _ <-> _ ] => fail 1
| _ => red ; intros ; try reduce_goal
end.

Tactic Notation "reduce" "in" hyp(Hid) := reduce_hyp Hid.

Ltac reduce := reduce_goal.

Tactic Notation "apply" "*" constr(t) :=
first [ refine t | refine (t _) | refine (t _ _) | refine (t _ _ _) | refine (t _ _ _ _) |
refine (t _ _ _ _ _) | refine (t _ _ _ _ _ _) | refine (t _ _ _ _ _ _ _) ].

Ltac simpl_relation :=
unfold flip, impl, arrow ; try reduce ; program_simpl ;
try ( solve [ dintuition ]).

Local Obligation Tactic := simpl_relation.



Program Instance impl_Reflexive : Reflexive impl.
Program Instance impl_Transitive : Transitive impl.



Instance iff_Reflexive : Reflexive iff := iff_refl.
Instance iff_Symmetric : Symmetric iff := iff_sym.
Instance iff_Transitive : Transitive iff := iff_trans.



Program Instance iff_equivalence : Equivalence iff.



Local Open Scope list_scope.




Inductive Tlist : Type := Tnil : Tlist | Tcons : Type -> Tlist -> Tlist.
Local Infix "::" := Tcons.

Fixpoint arrows (l : Tlist) (r : Type) : Type :=
match l with
| Tnil => r
| A :: l' => A -> arrows l' r
end.



Definition unary_operation A := arrows (A::Tnil) A.
Definition binary_operation A := arrows (A::A::Tnil) A.
Definition ternary_operation A := arrows (A::A::A::Tnil) A.



Notation predicate l := (arrows l Prop).



Definition unary_predicate A := predicate (A::Tnil).



Definition binary_relation A := predicate (A::A::Tnil).



Fixpoint predicate_all (l : Tlist) : predicate l -> Prop :=
match l with
| Tnil => fun f => f
| A :: tl => fun f => forall x : A, predicate_all tl (f x)
end.

Fixpoint predicate_exists (l : Tlist) : predicate l -> Prop :=
match l with
| Tnil => fun f => f
| A :: tl => fun f => exists x : A, predicate_exists tl (f x)
end.



Fixpoint pointwise_extension {T : Type} (op : binary_operation T)
(l : Tlist) : binary_operation (arrows l T) :=
match l with
| Tnil => fun R R' => op R R'
| A :: tl => fun R R' =>
fun x => pointwise_extension op tl (R x) (R' x)
end.



Fixpoint pointwise_lifting (op : binary_relation Prop)  (l : Tlist) : binary_relation (predicate l) :=
match l with
| Tnil => fun R R' => op R R'
| A :: tl => fun R R' =>
forall x, pointwise_lifting op tl (R x) (R' x)
end.



Definition predicate_equivalence {l : Tlist} : binary_relation (predicate l) :=
pointwise_lifting iff l.



Definition predicate_implication {l : Tlist} :=
pointwise_lifting impl l.



Infix "<∙>" := predicate_equivalence (at level 95, no associativity) : predicate_scope.
Infix "-∙>" := predicate_implication (at level 70, right associativity) : predicate_scope.

Local Open Scope predicate_scope.



Definition predicate_intersection := pointwise_extension and.
Definition predicate_union := pointwise_extension or.

Infix "/∙\" := predicate_intersection (at level 80, right associativity) : predicate_scope.
Infix "\∙/" := predicate_union (at level 85, right associativity) : predicate_scope.



Fixpoint true_predicate {l : Tlist} : predicate l :=
match l with
| Tnil => True
| A :: tl => fun _ => @true_predicate tl
end.

Fixpoint false_predicate {l : Tlist} : predicate l :=
match l with
| Tnil => False
| A :: tl => fun _ => @false_predicate tl
end.

Notation "∙⊤∙" := true_predicate : predicate_scope.
Notation "∙⊥∙" := false_predicate : predicate_scope.



Program Instance predicate_equivalence_equivalence :
Equivalence (@predicate_equivalence l).

Next Obligation.
induction l ; firstorder.
Qed.
Next Obligation.
induction l ; firstorder.
Qed.
Next Obligation.
fold pointwise_lifting.
induction l. firstorder.
intros. simpl in *. pose (IHl (x x0) (y x0) (z x0)).
firstorder.
Qed.

Program Instance predicate_implication_preorder :
PreOrder (@predicate_implication l).
Next Obligation.
induction l ; firstorder.
Qed.
Next Obligation.
induction l. firstorder.
unfold predicate_implication in *. simpl in *.
intro. pose (IHl (x x0) (y x0) (z x0)). firstorder.
Qed.



Section Binary.
Context {A : Type}.

Definition relation_equivalence : relation (relation A) :=
@predicate_equivalence (_::_::Tnil).

Global Instance: RewriteRelation relation_equivalence.

Definition relation_conjunction (R : relation A) (R' : relation A) : relation A :=
@predicate_intersection (A::A::Tnil) R R'.

Definition relation_disjunction (R : relation A) (R' : relation A) : relation A :=
@predicate_union (A::A::Tnil) R R'.



Global Instance relation_equivalence_equivalence :
Equivalence relation_equivalence.
Proof. hammer_hook "RelationClasses" "RelationClasses.relation_equivalence_equivalence". Restart.  exact (@predicate_equivalence_equivalence (A::A::Tnil)). Qed.

Global Instance relation_implication_preorder : PreOrder (@subrelation A).
Proof. hammer_hook "RelationClasses" "RelationClasses.relation_implication_preorder". Restart.  exact (@predicate_implication_preorder (A::A::Tnil)). Qed.



Class PartialOrder eqA `{equ : Equivalence A eqA} R `{preo : PreOrder A R} :=
partial_order_equivalence : relation_equivalence eqA (relation_conjunction R (flip R)).



Global Instance partial_order_antisym `(PartialOrder eqA R) : ! Antisymmetric A eqA R.
Proof with auto. hammer_hook "RelationClasses" "RelationClasses.partial_order_antisym". Restart. 
reduce_goal.
pose proof partial_order_equivalence as poe. do 3 red in poe.
apply <- poe. firstorder.
Qed.


Lemma PartialOrder_inverse `(PartialOrder eqA R) : PartialOrder eqA (flip R).
Proof. hammer_hook "RelationClasses" "RelationClasses.PartialOrder_inverse". Restart.  firstorder. Qed.
End Binary.

Hint Extern 3 (PartialOrder (flip _)) => class_apply PartialOrder_inverse : typeclass_instances.



Program Instance subrelation_partial_order :
! PartialOrder (relation A) relation_equivalence subrelation.

Next Obligation.
Proof. hammer_hook "RelationClasses" "RelationClasses.subrelation_partial_order". Restart. 
unfold relation_equivalence in *. compute; firstorder.
Qed.

Typeclasses Opaque arrows predicate_implication predicate_equivalence
relation_equivalence pointwise_lifting.
