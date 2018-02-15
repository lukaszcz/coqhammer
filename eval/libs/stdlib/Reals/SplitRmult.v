From Hammer Require Import Hammer.












Require Import Rbase.

Ltac split_Rmult :=
match goal with
|  |- ((?X1 * ?X2)%R <> 0%R) =>
apply Rmult_integral_contrapositive; split; try split_Rmult
end.
