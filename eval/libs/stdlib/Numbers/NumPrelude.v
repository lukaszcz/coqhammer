From Hammer Require Import Hammer.











Require Export Setoid Morphisms Morphisms_Prop.

Set Implicit Arguments.



Ltac induction_maker n t :=
try intros until n; pattern n; t; clear n; [solve_proper | ..].

