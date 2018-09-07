From Hammer Require Import Hammer.













Notation "∀  x .. y , P" := (forall x, .. (forall y, P) ..)
(at level 200, x binder, y binder, right associativity) : type_scope.
Notation "∃  x .. y , P" := (exists x, .. (exists y, P) ..)
(at level 200, x binder, y binder, right associativity) : type_scope.

Notation "x ∨ y" := (x \/ y) (at level 85, right associativity) : type_scope.
Notation "x ∧ y" := (x /\ y) (at level 80, right associativity) : type_scope.
Notation "x → y" := (x -> y)
(at level 99, y at level 200, right associativity): type_scope.

Notation "x ↔ y" := (x <-> y) (at level 95, no associativity): type_scope.
Notation "¬ x" := (~x) (at level 75, right associativity) : type_scope.
Notation "x ≠ y" := (x <> y) (at level 70) : type_scope.


Notation "'λ'  x .. y , t" := (fun x => .. (fun y => t) ..)
(at level 200, x binder, y binder, right associativity).
