From Hammer Require Import Hammer.













Require Export Coq.Classes.Equivalence.



Require Import Coq.Logic.Decidable.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Program.Program.

Generalizable Variables A B R.

Open Scope equiv_scope.

Class DecidableEquivalence `(equiv : Equivalence A) :=
setoid_decidable : forall x y : A, decidable (x === y).



Class EqDec A R {equiv : Equivalence R} :=
equiv_dec : forall x y : A, { x === y } + { x =/= y }.



Notation " x == y " := (equiv_dec (x :>) (y :>)) (no associativity, at level 70) : equiv_scope.

Definition swap_sumbool {A B} (x : { A } + { B }) : { B } + { A } :=
match x with
| left H => @right _ _ H
| right H => @left _ _ H
end.

Local Open Scope program_scope.



Program Definition nequiv_dec `{EqDec A} (x y : A) : { x =/= y } + { x === y } :=
swap_sumbool (x == y).




Infix "<>" := nequiv_dec (no associativity, at level 70) : equiv_scope.



Definition equiv_decb `{EqDec A} (x y : A) : bool :=
if x == y then true else false.

Definition nequiv_decb `{EqDec A} (x y : A) : bool :=
negb (equiv_decb x y).

Infix "==b" := equiv_decb (no associativity, at level 70).
Infix "<>b" := nequiv_decb (no associativity, at level 70).





Program Instance nat_eq_eqdec : EqDec nat eq := eq_nat_dec.

Program Instance bool_eqdec : EqDec bool eq := bool_dec.

Program Instance unit_eqdec : EqDec unit eq := fun x y => in_left.

Next Obligation.
Proof. try hammer_hook "EquivDec" "EquivDec.unit_eqdec".  
destruct x ; destruct y.
reflexivity.
Qed.

Obligation Tactic := unfold complement, equiv ; program_simpl.

Program Instance prod_eqdec `(EqDec A eq, EqDec B eq) :
! EqDec (prod A B) eq :=
{ equiv_dec x y :=
let '(x1, x2) := x in
let '(y1, y2) := y in
if x1 == y1 then
if x2 == y2 then in_left
else in_right
else in_right }.

Program Instance sum_eqdec `(EqDec A eq, EqDec B eq) :
EqDec (sum A B) eq := {
equiv_dec x y :=
match x, y with
| inl a, inl b => if a == b then in_left else in_right
| inr a, inr b => if a == b then in_left else in_right
| inl _, inr _ | inr _, inl _ => in_right
end }.



Program Instance bool_function_eqdec `(EqDec A eq) : ! EqDec (bool -> A) eq :=
{ equiv_dec f g :=
if f true == g true then
if f false == g false then in_left
else in_right
else in_right }.

Next Obligation.
Proof. try hammer_hook "EquivDec" "EquivDec.bool_function_eqdec".  
extensionality x.
destruct x ; auto.
Qed.

Require Import List.

Program Instance list_eqdec `(eqa : EqDec A eq) : ! EqDec (list A) eq :=
{ equiv_dec :=
fix aux (x y : list A) :=
match x, y with
| nil, nil => in_left
| cons hd tl, cons hd' tl' =>
if hd == hd' then
if aux tl tl' then in_left else in_right
else in_right
| _, _ => in_right
end }.

Next Obligation. destruct y ; unfold not in *; eauto. Defined.

Solve Obligations with unfold equiv, complement in * ;
program_simpl ; intuition (discriminate || eauto).
