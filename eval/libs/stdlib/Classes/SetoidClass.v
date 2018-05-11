From Hammer Require Import Hammer.











Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A.

Require Import Coq.Program.Program.

Require Import Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.



Class Setoid A := {
equiv : relation A ;
setoid_equiv :> Equivalence equiv }.








Definition setoid_refl `(sa : Setoid A) : Reflexive equiv.
Proof. try hammer_hook "SetoidClass" "SetoidClass.setoid_refl".   typeclasses eauto. Qed.

Definition setoid_sym `(sa : Setoid A) : Symmetric equiv.
Proof. try hammer_hook "SetoidClass" "SetoidClass.setoid_sym".   typeclasses eauto. Qed.

Definition setoid_trans `(sa : Setoid A) : Transitive equiv.
Proof. try hammer_hook "SetoidClass" "SetoidClass.setoid_trans".   typeclasses eauto. Qed.

Existing Instance setoid_refl.
Existing Instance setoid_sym.
Existing Instance setoid_trans.






Program Instance iff_setoid : Setoid Prop :=
{ equiv := iff ; setoid_equiv := iff_equivalence }.






Notation " x == y " := (equiv x y) (at level 70, no associativity) : type_scope.

Notation " x =/= y " := (complement equiv x y) (at level 70, no associativity) : type_scope.



Ltac clsubst H :=
lazymatch type of H with
?x == ?y => substitute H ; clear H x
end.

Ltac clsubst_nofail :=
match goal with
| [ H : ?x == ?y |- _ ] => clsubst H ; clsubst_nofail
| _ => idtac
end.



Tactic Notation "clsubst" "*" := clsubst_nofail.

Lemma nequiv_equiv_trans : forall `{Setoid A} (x y z : A), x =/= y -> y == z -> x =/= z.
Proof with auto. try hammer_hook "SetoidClass" "SetoidClass.nequiv_equiv_trans".  
intros; intro.
assert(z == y) by (symmetry ; auto).
assert(x == y) by (transitivity z ; eauto).
contradiction.
Qed.

Lemma equiv_nequiv_trans : forall `{Setoid A} (x y z : A), x == y -> y =/= z -> x =/= z.
Proof. try hammer_hook "SetoidClass" "SetoidClass.equiv_nequiv_trans".  
intros; intro.
assert(y == x) by (symmetry ; auto).
assert(y == z) by (transitivity x ; eauto).
contradiction.
Qed.

Ltac setoid_simplify_one :=
match goal with
| [ H : (?x == ?x)%type |- _ ] => clear H
| [ H : (?x == ?y)%type |- _ ] => clsubst H
| [ |- (?x =/= ?y)%type ] => let name:=fresh "Hneq" in intro name
end.

Ltac setoid_simplify := repeat setoid_simplify_one.

Ltac setoidify_tac :=
match goal with
| [ s : Setoid ?A, H : ?R ?x ?y |- _ ] => change R with (@equiv A R s) in H
| [ s : Setoid ?A |- context C [ ?R ?x ?y ] ] => change (R x y) with (@equiv A R s x y)
end.

Ltac setoidify := repeat setoidify_tac.



Program Instance setoid_morphism `(sa : Setoid A) : Proper (equiv ++> equiv ++> iff) equiv :=
proper_prf.

Program Instance setoid_partial_app_morphism `(sa : Setoid A) (x : A) : Proper (equiv ++> iff) (equiv x) :=
proper_prf.



Class PartialSetoid (A : Type) :=
{ pequiv : relation A ; pequiv_prf :> PER pequiv }.



Infix "=~=" := pequiv (at level 70, no associativity) : type_scope.



Obligation Tactic := program_simpl.
