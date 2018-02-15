From Hammer Require Import Hammer.












Require Import SetoidList.
Require Import Relations Morphisms.


Local Notation Fst := (@fst _ _).
Local Notation Snd := (@snd _ _).

Arguments relation_conjunction A%type (R R')%signature _ _.
Arguments relation_equivalence A%type (_ _)%signature.
Arguments subrelation A%type (R R')%signature.
Arguments Reflexive A%type R%signature.
Arguments Irreflexive A%type R%signature.
Arguments Symmetric A%type R%signature.
Arguments Transitive A%type R%signature.
Arguments PER A%type R%signature.
Arguments Equivalence A%type R%signature.
Arguments StrictOrder A%type R%signature.

Generalizable Variables A B RA RB Ri Ro f.



Definition RelCompFun {A} {B : Type}(R:relation B)(f:A->B) : relation A :=
fun a a' => R (f a) (f a').


Typeclasses Opaque RelCompFun.

Infix "@@" := RelCompFun (at level 30, right associativity) : signature_scope.

Notation "R @@1" := (R @@ Fst)%signature (at level 30) : signature_scope.
Notation "R @@2" := (R @@ Snd)%signature (at level 30) : signature_scope.



Class Measure {A B} (f : A -> B).



Instance fst_measure : @Measure (A * B) A Fst.
Instance snd_measure : @Measure (A * B) B Snd.



Definition RelProd {A : Type} {B : Type} (RA:relation A)(RB:relation B) : relation (A*B) :=
relation_conjunction (@RelCompFun (A * B) A RA fst) (RB @@2).

Typeclasses Opaque RelProd.

Infix "*" := RelProd : signature_scope.

Section RelCompFun_Instances.
Context {A : Type} {B : Type} (R : relation B).

Global Instance RelCompFun_Reflexive
`(Measure A B f, Reflexive _ R) : Reflexive (R@@f).
Proof. hammer_hook "RelationPairs" "RelationPairs.RelCompFun_Reflexive". Restart.  firstorder. Qed.

Global Instance RelCompFun_Symmetric
`(Measure A B f, Symmetric _ R) : Symmetric (R@@f).
Proof. hammer_hook "RelationPairs" "RelationPairs.RelCompFun_Symmetric". Restart.  firstorder. Qed.

Global Instance RelCompFun_Transitive
`(Measure A B f, Transitive _ R) : Transitive (R@@f).
Proof. hammer_hook "RelationPairs" "RelationPairs.RelCompFun_Transitive". Restart.  firstorder. Qed.

Global Instance RelCompFun_Irreflexive
`(Measure A B f, Irreflexive _ R) : Irreflexive (R@@f).
Proof. hammer_hook "RelationPairs" "RelationPairs.RelCompFun_Irreflexive". Restart.  firstorder. Qed.

Global Program Instance RelCompFun_Equivalence
`(Measure A B f, Equivalence _ R) : Equivalence (R@@f).

Global Program Instance RelCompFun_StrictOrder
`(Measure A B f, StrictOrder _ R) : StrictOrder (R@@f).

End RelCompFun_Instances.

Section RelProd_Instances.

Context {A : Type} {B : Type} (RA : relation A) (RB : relation B).

Global Instance RelProd_Reflexive `(Reflexive _ RA, Reflexive _ RB) : Reflexive (RA*RB).
Proof. hammer_hook "RelationPairs" "RelationPairs.RelProd_Reflexive". Restart.  firstorder. Qed.

Global Instance RelProd_Symmetric `(Symmetric _ RA, Symmetric _ RB)
: Symmetric (RA*RB).
Proof. hammer_hook "RelationPairs" "RelationPairs.RelProd_Symmetric". Restart.  firstorder. Qed.

Global Instance RelProd_Transitive
`(Transitive _ RA, Transitive _ RB) : Transitive (RA*RB).
Proof. hammer_hook "RelationPairs" "RelationPairs.RelProd_Transitive". Restart.  firstorder. Qed.

Global Program Instance RelProd_Equivalence
`(Equivalence _ RA, Equivalence _ RB) : Equivalence (RA*RB).

Lemma FstRel_ProdRel :
relation_equivalence (RA @@1) (RA*(fun _ _ : B => True)).
Proof. hammer_hook "RelationPairs" "RelationPairs.FstRel_ProdRel". Restart.  firstorder. Qed.

Lemma SndRel_ProdRel :
relation_equivalence (RB @@2) ((fun _ _ : A =>True) * RB).
Proof. hammer_hook "RelationPairs" "RelationPairs.SndRel_ProdRel". Restart.  firstorder. Qed.

Global Instance FstRel_sub :
subrelation (RA*RB) (RA @@1).
Proof. hammer_hook "RelationPairs" "RelationPairs.FstRel_sub". Restart.  firstorder. Qed.

Global Instance SndRel_sub :
subrelation (RA*RB) (RB @@2).
Proof. hammer_hook "RelationPairs" "RelationPairs.SndRel_sub". Restart.  firstorder. Qed.

Global Instance pair_compat :
Proper (RA==>RB==> RA*RB) (@pair _ _).
Proof. hammer_hook "RelationPairs" "RelationPairs.pair_compat". Restart.  firstorder. Qed.

Global Instance fst_compat :
Proper (RA*RB ==> RA) Fst.
Proof. hammer_hook "RelationPairs" "RelationPairs.fst_compat". Restart. 
intros (x,y) (x',y') (Hx,Hy); compute in *; auto.
Qed.

Global Instance snd_compat :
Proper (RA*RB ==> RB) Snd.
Proof. hammer_hook "RelationPairs" "RelationPairs.snd_compat". Restart. 
intros (x,y) (x',y') (Hx,Hy); compute in *; auto.
Qed.

Global Instance RelCompFun_compat (f:A->B)
`(Proper _ (Ri==>Ri==>Ro) RB) :
Proper (Ri@@f==>Ri@@f==>Ro) (RB@@f)%signature.
Proof. hammer_hook "RelationPairs" "RelationPairs.RelCompFun_compat". Restart.  unfold RelCompFun; firstorder. Qed.
End RelProd_Instances.

Hint Unfold RelProd RelCompFun.
Hint Extern 2 (RelProd _ _ _ _) => split.

