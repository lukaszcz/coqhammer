From Hammer Require Import Hammer.












Set Implicit Arguments.
Unset Strict Implicit.

Generalizable Variables A B .



Require Export Coq.Classes.SetoidClass.



Require Import Coq.Logic.Decidable.

Class DecidableSetoid `(S : Setoid A) :=
setoid_decidable : forall x y : A, decidable (x == y).



Class EqDec `(S : Setoid A) :=
equiv_dec : forall x y : A, { x == y } + { x =/= y }.



Notation " x == y " := (equiv_dec (x :>) (y :>)) (no associativity, at level 70).

Definition swap_sumbool {A B} (x : { A } + { B }) : { B } + { A } :=
match x with
| left H => @right _ _ H
| right H => @left _ _ H
end.

Require Import Coq.Program.Program.

Local Open Scope program_scope.



Program Definition nequiv_dec `{EqDec A} (x y : A) : { x =/= y } + { x == y } := swap_sumbool (x == y).



Infix "=/=" := nequiv_dec (no associativity, at level 70).



Definition equiv_decb `{EqDec A} (x y : A) : bool :=
if x == y then true else false.

Definition nequiv_decb `{EqDec A} (x y : A) : bool :=
negb (equiv_decb x y).

Infix "==b" := equiv_decb (no associativity, at level 70).
Infix "<>b" := nequiv_decb (no associativity, at level 70).



Require Import Coq.Arith.Arith.



Program Instance eq_setoid A : Setoid A | 10 :=
{ equiv := eq ; setoid_equiv := eq_equivalence }.

Program Instance nat_eq_eqdec : EqDec (eq_setoid nat) :=
eq_nat_dec.

Require Import Coq.Bool.Bool.

Program Instance bool_eqdec : EqDec (eq_setoid bool) :=
bool_dec.

Program Instance unit_eqdec : EqDec (eq_setoid unit) :=
fun x y => in_left.

Next Obligation.
Proof. hammer_hook "SetoidDec" "SetoidDec.unit_eqdec".  
destruct x ; destruct y.
reflexivity.
Qed.

Program Instance prod_eqdec `(! EqDec (eq_setoid A), ! EqDec (eq_setoid B))
: EqDec (eq_setoid (prod A B)) :=
fun x y =>
let '(x1, x2) := x in
let '(y1, y2) := y in
if x1 == y1 then
if x2 == y2 then in_left
else in_right
else in_right.

Solve Obligations with unfold complement ; program_simpl.



Program Instance bool_function_eqdec `(! EqDec (eq_setoid A))
: EqDec (eq_setoid (bool -> A)) :=
fun f g =>
if f true == g true then
if f false == g false then in_left
else in_right
else in_right.

Solve Obligations with try red ; unfold complement ; program_simpl.

Next Obligation.
Proof. hammer_hook "SetoidDec" "SetoidDec.bool_function_eqdec".  
extensionality x.
destruct x ; auto.
Qed.
