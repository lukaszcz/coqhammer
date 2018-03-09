From Hammer Require Import Hammer.














Require Import FSetInterface ZArith Int.

Set Implicit Arguments.
Unset Strict Implicit.



Require FSetCompat MSetAVL Orders OrdersAlt.

Module IntMake (I:Int)(X: OrderedType) <: S with Module E := X.
Module X' := OrdersAlt.Update_OT X.
Module MSet := MSetAVL.IntMake I X'.
Include FSetCompat.Backport_Sets X MSet.
End IntMake.



Module Make (X: OrderedType) <: S with Module E := X
:=IntMake(Z_as_Int)(X).

