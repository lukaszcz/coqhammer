From Hammer Require Import Hammer.













Arguments id {A} x.



Definition compose {A B C} (g : B -> C) (f : A -> B) :=
fun x : A => g (f x).

Hint Unfold compose.

Notation " g ∘ f " := (compose g f)
(at level 40, left associativity) : program_scope.

Local Open Scope program_scope.



Definition arrow (A B : Type) := A -> B.



Definition impl (A B : Prop) : Prop := A -> B.



Definition const {A B} (a : A) := fun _ : B => a.



Definition flip {A B C} (f : A -> B -> C) x y := f y x.



Definition apply {A B} (f : A -> B) (x : A) := f x.



Arguments prod_curry   {A B C} f p.
Arguments prod_uncurry {A B C} f x y.
