From Hammer Require Import Hammer.











Set Implicit Arguments.






Definition is_inverse A B f g := (forall a:A, g (f a) = a) /\ (forall b:B, f (g b) = b).



Record Delta A := { pi1:A; pi2:A; eq:pi1=pi2 }.

Definition delta {A} (a:A) := {|pi1 := a; pi2 := a; eq := eq_refl a |}.

Arguments pi1 {A} _.
Arguments pi2 {A} _.

Lemma diagonal_projs_same_behavior : forall A (x:Delta A), pi1 x = pi2 x.
Proof. hammer_hook "ExtensionalityFacts" "ExtensionalityFacts.diagonal_projs_same_behavior".  
destruct x as (a1,a2,Heq); assumption.
Qed.

Lemma diagonal_inverse1 : forall A, is_inverse (A:=A) delta pi1.
Proof. hammer_hook "ExtensionalityFacts" "ExtensionalityFacts.diagonal_inverse1".  
split; [trivial|]; destruct b as (a1,a2,[]); reflexivity.
Qed.

Lemma diagonal_inverse2 : forall A, is_inverse (A:=A) delta pi2.
Proof. hammer_hook "ExtensionalityFacts" "ExtensionalityFacts.diagonal_inverse2".  
split; [trivial|]; destruct b as (a1,a2,[]); reflexivity.
Qed.



Local Notation FunctionalExtensionality :=
(forall A B (f g : A -> B), (forall x, f x = g x) -> f = g).



Local Notation EqDeltaProjs := (forall A, pi1 = pi2 :> (Delta A -> A)).



Local Notation UniqueInverse := (forall A B (f:A->B) g1 g2, is_inverse f g1 -> is_inverse f g2 -> g1 = g2).



Definition action A B C (f:A->B) := (fun h:B->C => fun x => h (f x)).

Local Notation BijectivityBijectiveComp := (forall A B C (f:A->B) g,
is_inverse f g -> is_inverse (A:=B->C) (action f) (action g)).




Theorem FunctExt_iff_EqDeltaProjs : FunctionalExtensionality <-> EqDeltaProjs.
Proof. hammer_hook "ExtensionalityFacts" "ExtensionalityFacts.FunctExt_iff_EqDeltaProjs".  
split.
- intros FunExt *; apply FunExt, diagonal_projs_same_behavior.
- intros EqProjs **; change f with (fun x => pi1 {|pi1:=f x; pi2:=g x; eq:=H x|}).
rewrite EqProjs; reflexivity.
Qed.




Lemma FunctExt_UniqInverse : FunctionalExtensionality -> UniqueInverse.
Proof. hammer_hook "ExtensionalityFacts" "ExtensionalityFacts.FunctExt_UniqInverse".  
intros FunExt * (Hg1f,Hfg1) (Hg2f,Hfg2).
apply FunExt. intros; congruence.
Qed.

Lemma UniqInverse_EqDeltaProjs : UniqueInverse -> EqDeltaProjs.
Proof. hammer_hook "ExtensionalityFacts" "ExtensionalityFacts.UniqInverse_EqDeltaProjs".  
intros UniqInv *.
apply UniqInv with delta; [apply diagonal_inverse1 | apply diagonal_inverse2].
Qed.

Theorem FunctExt_iff_UniqInverse : FunctionalExtensionality <-> UniqueInverse.
Proof. hammer_hook "ExtensionalityFacts" "ExtensionalityFacts.FunctExt_iff_UniqInverse".  
split.
- apply FunctExt_UniqInverse.
- intro; apply FunctExt_iff_EqDeltaProjs, UniqInverse_EqDeltaProjs; trivial.
Qed.




Lemma FunctExt_BijComp : FunctionalExtensionality -> BijectivityBijectiveComp.
Proof. hammer_hook "ExtensionalityFacts" "ExtensionalityFacts.FunctExt_BijComp".  
intros FunExt * (Hgf,Hfg). split; unfold action.
- intros h; apply FunExt; intro b; rewrite Hfg; reflexivity.
- intros h; apply FunExt; intro a; rewrite Hgf; reflexivity.
Qed.

Lemma BijComp_FunctExt : BijectivityBijectiveComp -> FunctionalExtensionality.
Proof. hammer_hook "ExtensionalityFacts" "ExtensionalityFacts.BijComp_FunctExt".  
intros BijComp.
apply FunctExt_iff_UniqInverse. intros * H1 H2.
destruct BijComp with (C:=A) (1:=H2) as (Hg2f,_).
destruct BijComp with (C:=A) (1:=H1) as (_,Hfg1).
rewrite <- (Hg2f g1).
change g1 with (action g1 (fun x => x)).
rewrite -> (Hfg1 (fun x => x)).
reflexivity.
Qed.
