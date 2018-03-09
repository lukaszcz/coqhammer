From Hammer Require Import Hammer.













Require Export FSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.



Require FSetCompat MSetList Orders OrdersAlt.

Module Make (X: OrderedType) <: S with Module E := X.
Module X' := OrdersAlt.Update_OT X.
Module MSet := MSetList.Make X'.
Include FSetCompat.Backport_Sets X MSet.
End Make.
