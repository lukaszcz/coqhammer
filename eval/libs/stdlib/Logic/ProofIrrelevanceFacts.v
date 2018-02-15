From Hammer Require Import Hammer.











Require Export EqdepFacts.

Module Type ProofIrrelevance.

Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.

End ProofIrrelevance.

Module ProofIrrelevanceTheory (M:ProofIrrelevance).



Module Eq_rect_eq.
Lemma eq_rect_eq :
forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
x = eq_rect p Q x p h.
Proof. hammer_hook "ProofIrrelevanceFacts" "ProofIrrelevanceFacts.ProofIrrelevanceTheory.Eq_rect_eq.eq_rect_eq". Restart. 
intros; rewrite M.proof_irrelevance with (p1:=h) (p2:=eq_refl p).
reflexivity.
Qed.
End Eq_rect_eq.



Module EqdepTheory := EqdepTheory(Eq_rect_eq).
Export EqdepTheory.

Scheme eq_indd := Induction for eq Sort Prop.



Lemma subset_eq_compat :
forall (U:Type) (P:U->Prop) (x y:U) (p:P x) (q:P y),
x = y -> exist P x p = exist P y q.
Proof. hammer_hook "ProofIrrelevanceFacts" "ProofIrrelevanceFacts.ProofIrrelevanceTheory.subset_eq_compat". Restart. 
intros.
rewrite M.proof_irrelevance with (p1:=q) (p2:=eq_rect x P p y H).
elim H using eq_indd.
reflexivity.
Qed.

Lemma subsetT_eq_compat :
forall (U:Type) (P:U->Prop) (x y:U) (p:P x) (q:P y),
x = y -> existT P x p = existT P y q.
Proof. hammer_hook "ProofIrrelevanceFacts" "ProofIrrelevanceFacts.ProofIrrelevanceTheory.subsetT_eq_compat". Restart. 
intros.
rewrite M.proof_irrelevance with (p1:=q) (p2:=eq_rect x P p y H).
elim H using eq_indd.
reflexivity.
Qed.

End ProofIrrelevanceTheory.
