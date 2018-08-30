From Hammer Require Import Hammer.












Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Generalizable Variables A B C D R S T U l eqA eqB eqC eqD.

Set Universe Polymorphism.

Definition crelation (A : Type) := A -> A -> Type.

Definition arrow (A B : Type) := A -> B.

Definition flip {A B C : Type} (f : A -> B -> C) := fun x y => f y x.

Definition iffT (A B : Type) := ((A -> B) * (B -> A))%type.



Section Defs.
Context {A : Type}.



Class Reflexive (R : crelation A) :=
reflexivity : forall x : A, R x x.

Definition complement (R : crelation A) : crelation A :=
fun x y => R x y -> False.


Typeclasses Opaque complement iffT.


Lemma complement_inverse R : complement (flip R) = flip (complement R).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.complement_inverse".   reflexivity. Qed.

Class Irreflexive (R : crelation A) :=
irreflexivity : Reflexive (complement R).

Class Symmetric (R : crelation A) :=
symmetry : forall {x y}, R x y -> R y x.

Class Asymmetric (R : crelation A) :=
asymmetry : forall {x y}, R x y -> (complement R y x : Type).

Class Transitive (R : crelation A) :=
transitivity : forall {x y z}, R x y -> R y z -> R x z.





Class PreOrder (R : crelation A)  := {
PreOrder_Reflexive :> Reflexive R | 2 ;
PreOrder_Transitive :> Transitive R | 2 }.



Class StrictOrder (R : crelation A)  := {
StrictOrder_Irreflexive :> Irreflexive R ;
StrictOrder_Transitive :> Transitive R }.


Global Instance StrictOrder_Asymmetric `(StrictOrder R) : Asymmetric R.
Proof. hammer_hook "CRelationClasses" "CRelationClasses.StrictOrder_Asymmetric".   firstorder. Qed.



Class PER (R : crelation A)  := {
PER_Symmetric :> Symmetric R | 3 ;
PER_Transitive :> Transitive R | 3 }.



Class Equivalence (R : crelation A)  := {
Equivalence_Reflexive :> Reflexive R ;
Equivalence_Symmetric :> Symmetric R ;
Equivalence_Transitive :> Transitive R }.



Global Instance Equivalence_PER {R} `(Equivalence R) : PER R | 10 :=
{ PER_Symmetric := Equivalence_Symmetric ;
PER_Transitive := Equivalence_Transitive }.



Class Antisymmetric eqA `{equ : Equivalence eqA} (R : crelation A) :=
antisymmetry : forall {x y}, R x y -> R y x -> eqA x y.

Class subrelation (R R' : crelation A) :=
is_subrelation : forall {x y}, R x y -> R' x y.



Lemma subrelation_symmetric R `(Symmetric R) : subrelation (flip R) R.
Proof. hammer_hook "CRelationClasses" "CRelationClasses.subrelation_symmetric".   hnf. intros x y H'. red in H'. apply symmetry. assumption. Qed.

Section flip.

Lemma flip_Reflexive `{Reflexive R} : Reflexive (flip R).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.flip_Reflexive".   tauto. Qed.

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
Proof. hammer_hook "CRelationClasses" "CRelationClasses.flip_Antisymmetric".   firstorder. Qed.



Lemma flip_PreOrder `(PreOrder R) : PreOrder (flip R).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.flip_PreOrder".   firstorder. Qed.

Lemma flip_StrictOrder `(StrictOrder R) : StrictOrder (flip R).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.flip_StrictOrder".   firstorder. Qed.

Lemma flip_PER `(PER R) : PER (flip R).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.flip_PER".   firstorder. Qed.

Lemma flip_Equivalence `(Equivalence R) : Equivalence (flip R).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.flip_Equivalence".   firstorder. Qed.

End flip.

Section complement.

Definition complement_Irreflexive `(Reflexive R)
: Irreflexive (complement R).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.complement_Irreflexive".   firstorder. Qed.

Definition complement_Symmetric `(Symmetric R) : Symmetric (complement R).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.complement_Symmetric".   firstorder. Qed.
End complement.




Class RewriteRelation (RA : crelation A).



Global Instance equivalence_rewrite_crelation `(Equivalence eqA) : RewriteRelation eqA.


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

Hint Resolve irreflexivity : ord.

Unset Implicit Arguments.



Ltac solve_crelation :=
match goal with
| [ |- ?R ?x ?x ] => reflexivity
| [ H : ?R ?x ?y |- ?R ?y ?x ] => symmetry ; exact H
end.

Hint Extern 4 => solve_crelation : crelations.





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

Ltac simpl_crelation :=
unfold flip, impl, arrow ; try reduce ; program_simpl ;
try ( solve [ dintuition ]).

Local Obligation Tactic := simpl_crelation.



Program Instance impl_Reflexive : Reflexive impl.
Program Instance impl_Transitive : Transitive impl.



Instance iff_Reflexive : Reflexive iff := iff_refl.
Instance iff_Symmetric : Symmetric iff := iff_sym.
Instance iff_Transitive : Transitive iff := iff_trans.



Program Instance iff_equivalence : Equivalence iff.
Program Instance arrow_Reflexive : Reflexive arrow.
Program Instance arrow_Transitive : Transitive arrow.

Instance iffT_Reflexive : Reflexive iffT.
Proof. hammer_hook "CRelationClasses" "CRelationClasses.iffT_Reflexive".   firstorder. Defined.
Instance iffT_Symmetric : Symmetric iffT.
Proof. hammer_hook "CRelationClasses" "CRelationClasses.iffT_Symmetric".   firstorder. Defined.
Instance iffT_Transitive : Transitive iffT.
Proof. hammer_hook "CRelationClasses" "CRelationClasses.iffT_Transitive".   firstorder. Defined.



Local Open Scope list_scope.




Section Binary.
Context {A : Type}.

Definition relation_equivalence : crelation (crelation A) :=
fun R R' => forall x y, iffT (R x y) (R' x y).

Global Instance: RewriteRelation relation_equivalence.

Definition relation_conjunction (R : crelation A) (R' : crelation A) : crelation A :=
fun x y => prod (R x y) (R' x y).

Definition relation_disjunction (R : crelation A) (R' : crelation A) : crelation A :=
fun x y => sum (R x y) (R' x y).



Global Instance relation_equivalence_equivalence :
Equivalence relation_equivalence.
Proof. hammer_hook "CRelationClasses" "CRelationClasses.relation_equivalence_equivalence".   split; red; unfold relation_equivalence, iffT. firstorder.
firstorder.
intros. specialize (X x0 y0). specialize (X0 x0 y0). firstorder.
Qed.

Global Instance relation_implication_preorder : PreOrder (@subrelation A).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.relation_implication_preorder".   firstorder. Qed.



Class PartialOrder eqA `{equ : Equivalence A eqA} R `{preo : PreOrder A R} :=
partial_order_equivalence : relation_equivalence eqA (relation_conjunction R (flip R)).



Global Instance partial_order_antisym `(PartialOrder eqA R) : ! Antisymmetric A eqA R.
Proof with auto. hammer_hook "CRelationClasses" "CRelationClasses.partial_order_antisym".  
reduce_goal.
apply H. firstorder.
Qed.

Lemma PartialOrder_inverse `(PartialOrder eqA R) : PartialOrder eqA (flip R).
Proof. hammer_hook "CRelationClasses" "CRelationClasses.PartialOrder_inverse".   unfold flip; constructor; unfold flip. intros. apply H. apply symmetry. apply X.
unfold relation_conjunction. intros [H1 H2]. apply H. constructor; assumption. Qed.
End Binary.

Hint Extern 3 (PartialOrder (flip _)) => class_apply PartialOrder_inverse : typeclass_instances.












Typeclasses Opaque relation_equivalence.


