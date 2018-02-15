From Hammer Require Import Hammer.











Require Coq.Classes.CRelationClasses Coq.Classes.CMorphisms.
Require Import Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Export Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Equivalence Coq.Program.Basics.

Generalizable Variables A R.

Export ProperNotations.

Set Implicit Arguments.
Unset Strict Implicit.



Class DefaultRelation A (R : relation A).



Definition default_relation `{DefaultRelation A R} := R.



Instance equivalence_default `(Equivalence A R) : DefaultRelation R | 4.



Ltac setoidreplace H t :=
let Heq := fresh "Heq" in
cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq ; clear Heq | t ].

Ltac setoidreplacein H H' t :=
let Heq := fresh "Heq" in
cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq in H' ; clear Heq | t ].

Ltac setoidreplaceinat H H' t occs :=
let Heq := fresh "Heq" in
cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq in H' at occs ; clear Heq | t ].

Ltac setoidreplaceat H t occs :=
let Heq := fresh "Heq" in
cut(H) ; unfold default_relation ; [ intro Heq ; setoid_rewrite Heq at occs ; clear Heq | t ].

Tactic Notation "setoid_replace" constr(x) "with" constr(y) :=
setoidreplace (default_relation x y) idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"at" int_or_var_list(o) :=
setoidreplaceat (default_relation x y) idtac o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"in" hyp(id) :=
setoidreplacein (default_relation x y) id idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"in" hyp(id)
"at" int_or_var_list(o) :=
setoidreplaceinat (default_relation x y) id idtac o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"by" tactic3(t) :=
setoidreplace (default_relation x y) ltac:(t).

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"at" int_or_var_list(o)
"by" tactic3(t) :=
setoidreplaceat (default_relation x y) ltac:(t) o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"in" hyp(id)
"by" tactic3(t) :=
setoidreplacein (default_relation x y) id ltac:(t).

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"in" hyp(id)
"at" int_or_var_list(o)
"by" tactic3(t) :=
setoidreplaceinat (default_relation x y) id ltac:(t) o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"using" "relation" constr(rel) :=
setoidreplace (rel x y) idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"using" "relation" constr(rel)
"at" int_or_var_list(o) :=
setoidreplaceat (rel x y) idtac o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"using" "relation" constr(rel)
"by" tactic3(t) :=
setoidreplace (rel x y) ltac:(t).

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"using" "relation" constr(rel)
"at" int_or_var_list(o)
"by" tactic3(t) :=
setoidreplaceat (rel x y) ltac:(t) o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"using" "relation" constr(rel)
"in" hyp(id) :=
setoidreplacein (rel x y) id idtac.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"using" "relation" constr(rel)
"in" hyp(id)
"at" int_or_var_list(o) :=
setoidreplaceinat (rel x y) id idtac o.

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"using" "relation" constr(rel)
"in" hyp(id)
"by" tactic3(t) :=
setoidreplacein (rel x y) id ltac:(t).

Tactic Notation "setoid_replace" constr(x) "with" constr(y)
"using" "relation" constr(rel)
"in" hyp(id)
"at" int_or_var_list(o)
"by" tactic3(t) :=
setoidreplaceinat (rel x y) id ltac:(t) o.



Require Import Coq.Program.Tactics.

Local Open Scope signature_scope.

Ltac red_subst_eq_morphism concl :=
match concl with
| @Logic.eq ?A ==> ?R' => red ; intros ; subst ; red_subst_eq_morphism R'
| ?R ==> ?R' => red ; intros ; red_subst_eq_morphism R'
| _ => idtac
end.

Ltac destruct_proper :=
match goal with
| [ |- @Proper ?A ?R ?m ] => red
end.

Ltac reverse_arrows x :=
match x with
| @Logic.eq ?A ==> ?R' => revert_last ; reverse_arrows R'
| ?R ==> ?R' => do 3 revert_last ; reverse_arrows R'
| _ => idtac
end.

Ltac default_add_morphism_tactic :=
unfold flip ; intros ;
(try destruct_proper) ;
match goal with
| [ |- (?x ==> ?y) _ _ ] => red_subst_eq_morphism (x ==> y) ; reverse_arrows (x ==> y)
end.

Ltac add_morphism_tactic := default_add_morphism_tactic.

Obligation Tactic := program_simpl.


