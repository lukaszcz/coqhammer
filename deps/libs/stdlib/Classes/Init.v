From Hammer Require Import Hammer.













Require Import Coq.Program.Basics.

Typeclasses Opaque id const flip compose arrow impl iff not all.



Ltac class_apply c := autoapply c using typeclass_instances.



Class Unconvertible (A : Type) (a b : A) := unconvertible : unit.

Ltac unconvertible :=
match goal with
| |- @Unconvertible _ ?x ?y => unify x y with typeclass_instances ; fail 1 "Convertible"
| |- _ => exact tt
end.

Hint Extern 0 (@Unconvertible _ _ _) => unconvertible : typeclass_instances.
