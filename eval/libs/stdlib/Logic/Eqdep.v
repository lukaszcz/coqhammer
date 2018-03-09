From Hammer Require Import Hammer.















Require Export EqdepFacts.

Module Eq_rect_eq.

Axiom eq_rect_eq :
forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.

End Eq_rect_eq.

Module EqdepTheory := EqdepTheory(Eq_rect_eq).
Export EqdepTheory.



Hint Resolve eq_dep_eq: eqdep.
Hint Resolve inj_pair2 inj_pairT2: eqdep.
