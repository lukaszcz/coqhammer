From Hammer Require Import Hammer.











Require Import ProofIrrelevanceFacts.

Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

Module PI. Definition proof_irrelevance := proof_irrelevance. End PI.

Module ProofIrrelevanceTheory := ProofIrrelevanceTheory(PI).
Export ProofIrrelevanceTheory.
