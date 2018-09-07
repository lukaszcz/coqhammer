From Hammer Require Import Hammer.













Require Import FSetInterface.
Set Implicit Arguments.
Unset Strict Implicit.



Require Equalities FSetCompat MSetWeakList.

Module Make (X: DecidableType) <: WS with Module E := X.
Module E := X.
Module X' := Equalities.Update_DT X.
Module MSet := MSetWeakList.Make X'.
Include FSetCompat.Backport_WSets X MSet.
End Make.
