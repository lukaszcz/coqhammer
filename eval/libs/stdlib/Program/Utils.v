From Hammer Require Import Hammer.











Require Export Coq.Program.Tactics.

Set Implicit Arguments.



Notation "{ ( x , y )  :  A  |  P }" :=
(sig (fun anonymous : A => let (x,y) := anonymous in P))
(x ident, y ident, at level 10) : type_scope.



Notation " ! " := (False_rect _ _) : program_scope.

Delimit Scope program_scope with prg.



Notation " `  t " := (proj1_sig t) (at level 10, t at next level) : program_scope.



Notation " x '`=' y " := ((x :>) = (y :>)) (at level 70) : program_scope.

Require Import Coq.Bool.Sumbool.



Notation dec := sumbool_of_bool.





Notation in_left := (@left _ _ _).
Notation in_right := (@right _ _ _).



