From Hammer Require Import Hammer.









Require Import Rbasic_fun.

Ltac split_case_Rabs :=
match goal with
|  |- context [(Rcase_abs ?X1)] =>
destruct (Rcase_abs X1) as [?Hlt|?Hge]; try split_case_Rabs
end.


Ltac split_Rabs :=
match goal with
| id:context [(Rabs _)] |- _ => generalize id; clear id; try split_Rabs
|  |- context [(Rabs ?X1)] =>
unfold Rabs; try split_case_Rabs; intros
end.
