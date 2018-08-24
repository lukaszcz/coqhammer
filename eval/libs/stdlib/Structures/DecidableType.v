From Hammer Require Import Hammer.









Require Export SetoidList.
Require Equalities.

Set Implicit Arguments.
Unset Strict Implicit.





Module Type EqualityType := Equalities.EqualityTypeOrig.



Module Type DecidableType := Equalities.DecidableTypeOrig.



Module KeyDecidableType(D:DecidableType).
Import D.

Section Elt.
Variable elt : Type.
Notation key:=t.

Definition eqk (p p':key*elt) := eq (fst p) (fst p').
Definition eqke (p p':key*elt) :=
eq (fst p) (fst p') /\ (snd p) = (snd p').

Hint Unfold eqk eqke.
Hint Extern 2 (eqke ?a ?b) => split.



Lemma eqke_eqk : forall x x', eqke x x' -> eqk x x'.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.eqke_eqk". Undo.  
unfold eqk, eqke; intuition.
Qed.



Lemma eqk_refl : forall e, eqk e e.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.eqk_refl". Undo.   auto. Qed.

Lemma eqke_refl : forall e, eqke e e.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.eqke_refl". Undo.   auto. Qed.

Lemma eqk_sym : forall e e', eqk e e' -> eqk e' e.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.eqk_sym". Undo.   auto. Qed.

Lemma eqke_sym : forall e e', eqke e e' -> eqke e' e.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.eqke_sym". Undo.   unfold eqke; intuition. Qed.

Lemma eqk_trans : forall e e' e'', eqk e e' -> eqk e' e'' -> eqk e e''.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.eqk_trans". Undo.   eauto. Qed.

Lemma eqke_trans : forall e e' e'', eqke e e' -> eqke e' e'' -> eqke e e''.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.eqke_trans". Undo.  
unfold eqke; intuition; [ eauto | congruence ].
Qed.

Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
Hint Immediate eqk_sym eqke_sym.

Global Instance eqk_equiv : Equivalence eqk.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.eqk_equiv". Undo.   split; eauto. Qed.

Global Instance eqke_equiv : Equivalence eqke.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.eqke_equiv". Undo.   split; eauto. Qed.

Lemma InA_eqke_eqk :
forall x m, InA eqke x m -> InA eqk x m.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.InA_eqke_eqk". Undo.  
unfold eqke; induction 1; intuition.
Qed.
Hint Resolve InA_eqke_eqk.

Lemma InA_eqk : forall p q m, eqk p q -> InA eqk p m -> InA eqk q m.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.InA_eqk". Undo.  
intros; apply InA_eqA with p; auto using eqk_equiv.
Qed.

Definition MapsTo (k:key)(e:elt):= InA eqke (k,e).
Definition In k m := exists e:elt, MapsTo k e m.

Hint Unfold MapsTo In.



Lemma In_alt : forall k l, In k l <-> exists e, InA eqk (k,e) l.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.In_alt". Undo.  
firstorder.
exists x; auto.
induction H.
destruct y.
exists e; auto.
destruct IHInA as [e H0].
exists e; auto.
Qed.

Lemma MapsTo_eq : forall l x y e, eq x y -> MapsTo x e l -> MapsTo y e l.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.MapsTo_eq". Undo.  
intros; unfold MapsTo in *; apply InA_eqA with (x,e); auto using eqke_equiv.
Qed.

Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.In_eq". Undo.  
destruct 2 as (e,E); exists e; eapply MapsTo_eq; eauto.
Qed.

Lemma In_inv : forall k k' e l, In k ((k',e) :: l) -> eq k k' \/ In k l.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.In_inv". Undo.  
inversion 1.
inversion_clear H0; eauto.
destruct H1; simpl in *; intuition.
Qed.

Lemma In_inv_2 : forall k k' e e' l,
InA eqk (k, e) ((k', e') :: l) -> ~ eq k k' -> InA eqk (k, e) l.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.In_inv_2". Undo.  
inversion_clear 1; compute in H0; intuition.
Qed.

Lemma In_inv_3 : forall x x' l,
InA eqke x (x' :: l) -> ~ eqk x x' -> InA eqke x l.
Proof. try hammer_hook "DecidableType" "DecidableType.KeyDecidableType.In_inv_3". Undo.  
inversion_clear 1; compute in H0; intuition.
Qed.

End Elt.

Hint Unfold eqk eqke.
Hint Extern 2 (eqke ?a ?b) => split.
Hint Resolve eqk_trans eqke_trans eqk_refl eqke_refl.
Hint Immediate eqk_sym eqke_sym.
Hint Resolve InA_eqke_eqk.
Hint Unfold MapsTo In.
Hint Resolve In_inv_2 In_inv_3.

End KeyDecidableType.





