From Hammer Require Import Hammer.









Require Import Rdefinitions.

Fixpoint pow (r:R) (n:nat) : R :=
match n with
| O => 1
| S n => Rmult r (pow r n)
end.
