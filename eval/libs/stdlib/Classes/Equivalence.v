From Hammer Require Import Hammer.











Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Require Import Coq.Classes.Init.
Require Import Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A R eqA B S eqB.
Local Obligation Tactic := try solve [simpl_relation].

Local Open Scope signature_scope.

Definition equiv `{Equivalence A R} : relation A := R.



Notation " x === y " := (equiv x y) (at level 70, no associativity) : equiv_scope.

Notation " x =/= y " := (complement equiv x y) (at level 70, no associativity) : equiv_scope.

Local Open Scope equiv_scope.



Definition pequiv `{PER A R} : relation A := R.



Infix "=~=" := pequiv (at level 70, no associativity) : equiv_scope.



Program Instance equiv_reflexive `(sa : Equivalence A) : Reflexive equiv | 1.

Program Instance equiv_symmetric `(sa : Equivalence A) : Symmetric equiv | 1.

Program Instance equiv_transitive `(sa : Equivalence A) : Transitive equiv | 1.

Next Obligation.
Proof. try hammer_hook "Equivalence" "Equivalence.equiv_transitive".   intros A R sa x y z Hxy Hyz.
now transitivity y.
Qed.



Ltac setoid_subst H :=
match type of H with
?x === ?y => substitute H ; clear H x
end.

Ltac setoid_subst_nofail :=
match goal with
| [ H : ?x === ?y |- _ ] => setoid_subst H ; setoid_subst_nofail
| _ => idtac
end.



Tactic Notation "subst" "*" := subst_no_fail ; setoid_subst_nofail.



Ltac equiv_simplify_one :=
match goal with
| [ H : ?x === ?x |- _ ] => clear H
| [ H : ?x === ?y |- _ ] => setoid_subst H
| [ |- ?x =/= ?y ] => let name:=fresh "Hneq" in intro name
| [ |- ~ ?x === ?y ] => let name:=fresh "Hneq" in intro name
end.

Ltac equiv_simplify := repeat equiv_simplify_one.



Ltac equivify_tac :=
match goal with
| [ s : Equivalence ?A ?R, H : ?R ?x ?y |- _ ] => change R with (@equiv A R s) in H
| [ s : Equivalence ?A ?R |- context C [ ?R ?x ?y ] ] => change (R x y) with (@equiv A R s x y)
end.

Ltac equivify := repeat equivify_tac.

Section Respecting.



Definition respecting `(eqa : Equivalence A (R : relation A),
eqb : Equivalence B (R' : relation B)) : Type :=
{ morph : A -> B | respectful R R' morph morph }.

Program Instance respecting_equiv `(eqa : Equivalence A R, eqb : Equivalence B R') :
Equivalence (fun (f g : respecting eqa eqb) =>
forall (x y : A), R x y -> R' (proj1_sig f x) (proj1_sig g y)).

Solve Obligations with unfold respecting in * ; simpl_relation ; program_simpl.

Next Obligation.
Proof. try hammer_hook "Equivalence" "Equivalence.respecting_equiv".  
intros. intros f g h H H' x y Rxy.
unfold respecting in *. program_simpl. transitivity (g y); auto. firstorder.
Qed.

End Respecting.



Instance pointwise_reflexive {A} `(reflb : Reflexive B eqB) :
Reflexive (pointwise_relation A eqB) | 9.
Proof. try hammer_hook "Equivalence" "Equivalence.pointwise_reflexive".   firstorder. Qed.
Instance pointwise_symmetric {A} `(symb : Symmetric B eqB) :
Symmetric (pointwise_relation A eqB) | 9.
Proof. try hammer_hook "Equivalence" "Equivalence.pointwise_symmetric".   firstorder. Qed.
Instance pointwise_transitive {A} `(transb : Transitive B eqB) :
Transitive (pointwise_relation A eqB) | 9.
Proof. try hammer_hook "Equivalence" "Equivalence.pointwise_transitive".   firstorder. Qed.
Instance pointwise_equivalence {A} `(eqb : Equivalence B eqB) :
Equivalence (pointwise_relation A eqB) | 9.
Proof. try hammer_hook "Equivalence" "Equivalence.pointwise_equivalence".   split; apply _. Qed.
