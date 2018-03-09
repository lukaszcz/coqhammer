From Hammer Require Import Hammer.















Axiom extensional_function_representative :
forall A B, exists repr, forall (f : A -> B),
(forall x, f x = repr f x) /\
(forall g, (forall x, f x = g x) -> repr f = repr g).
