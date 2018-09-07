From Hammer Require Import Hammer.









Require Export RelationClasses.
Require Import Bool Morphisms Setoid.

Set Implicit Arguments.
Unset Strict Implicit.



Module Type Nop.
End Nop.



Module Type Typ.
Parameter Inline(10) t : Type.
End Typ.



Module Type HasEq (Import T:Typ).
Parameter Inline(30) eq : t -> t -> Prop.
End HasEq.

Module Type Eq := Typ <+ HasEq.

Module Type EqNotation (Import E:Eq).
Infix "==" := eq (at level 70, no associativity).
Notation "x ~= y" := (~eq x y) (at level 70, no associativity).
End EqNotation.

Module Type Eq' := Eq <+ EqNotation.



Module Type IsEq (Import E:Eq).
Declare Instance eq_equiv : Equivalence eq.
End IsEq.



Module Type IsEqOrig (Import E:Eq').
Axiom eq_refl : forall x : t, x==x.
Axiom eq_sym : forall x y : t, x==y -> y==x.
Axiom eq_trans : forall x y z : t, x==y -> y==z -> x==z.
Hint Immediate eq_sym.
Hint Resolve eq_refl eq_trans.
End IsEqOrig.



Module Type HasEqDec (Import E:Eq').
Parameter eq_dec : forall x y : t, { x==y } + { ~ x==y }.
End HasEqDec.





Module Type HasEqb (Import T:Typ).
Parameter Inline eqb : t -> t -> bool.
End HasEqb.

Module Type EqbSpec (T:Typ)(X:HasEq T)(Y:HasEqb T).
Parameter eqb_eq : forall x y, Y.eqb x y = true <-> X.eq x y.
End EqbSpec.

Module Type EqbNotation (T:Typ)(E:HasEqb T).
Infix "=?" := E.eqb (at level 70, no associativity).
End EqbNotation.

Module Type HasEqBool (E:Eq) := HasEqb E <+ EqbSpec E E.



Module Type EqualityType := Eq <+ IsEq.

Module Type EqualityTypeOrig := Eq <+ IsEqOrig.

Module Type EqualityTypeBoth <: EqualityType <: EqualityTypeOrig
:= Eq <+ IsEq <+ IsEqOrig.

Module Type DecidableType <: EqualityType
:= Eq <+ IsEq <+ HasEqDec.

Module Type DecidableTypeOrig <: EqualityTypeOrig
:= Eq <+ IsEqOrig <+ HasEqDec.

Module Type DecidableTypeBoth <: DecidableType <: DecidableTypeOrig
:= EqualityTypeBoth <+ HasEqDec.

Module Type BooleanEqualityType <: EqualityType
:= Eq <+ IsEq <+ HasEqBool.

Module Type BooleanDecidableType <: DecidableType <: BooleanEqualityType
:= Eq <+ IsEq <+ HasEqDec <+ HasEqBool.

Module Type DecidableTypeFull <: DecidableTypeBoth <: BooleanDecidableType
:= Eq <+ IsEq <+ IsEqOrig <+ HasEqDec <+ HasEqBool.



Module Type EqualityType' := EqualityType <+ EqNotation.
Module Type EqualityTypeOrig' := EqualityTypeOrig <+ EqNotation.
Module Type EqualityTypeBoth' := EqualityTypeBoth <+ EqNotation.
Module Type DecidableType' := DecidableType <+ EqNotation.
Module Type DecidableTypeOrig' := DecidableTypeOrig <+ EqNotation.
Module Type DecidableTypeBoth' := DecidableTypeBoth <+ EqNotation.
Module Type BooleanEqualityType' :=
BooleanEqualityType <+ EqNotation <+ EqbNotation.
Module Type BooleanDecidableType' :=
BooleanDecidableType <+ EqNotation <+ EqbNotation.
Module Type DecidableTypeFull' := DecidableTypeFull <+ EqNotation.



Module BackportEq (E:Eq)(F:IsEq E) <: IsEqOrig E.
Definition eq_refl := F.eq_equiv.(@Equivalence_Reflexive _ _).
Definition eq_sym := F.eq_equiv.(@Equivalence_Symmetric _ _).
Definition eq_trans := F.eq_equiv.(@Equivalence_Transitive _ _).
End BackportEq.

Module UpdateEq (E:Eq)(F:IsEqOrig E) <: IsEq E.
Instance eq_equiv : Equivalence E.eq.
Proof. hammer_hook "Equalities" "Equalities.IsEq.eq_equiv".   exact (Build_Equivalence _ F.eq_refl F.eq_sym F.eq_trans). Qed.
End UpdateEq.

Module Backport_ET (E:EqualityType) <: EqualityTypeBoth
:= E <+ BackportEq.

Module Update_ET (E:EqualityTypeOrig) <: EqualityTypeBoth
:= E <+ UpdateEq.

Module Backport_DT (E:DecidableType) <: DecidableTypeBoth
:= E <+ BackportEq.

Module Update_DT (E:DecidableTypeOrig) <: DecidableTypeBoth
:= E <+ UpdateEq.




Module HasEqDec2Bool (E:Eq)(F:HasEqDec E) <: HasEqBool E.
Definition eqb x y := if F.eq_dec x y then true else false.
Lemma eqb_eq : forall x y, eqb x y = true <-> E.eq x y.
Proof. hammer_hook "Equalities" "Equalities.EqbSpec.eqb_eq".  
intros x y. unfold eqb. destruct F.eq_dec as [EQ|NEQ].
auto with *.
split. discriminate. intro EQ; elim NEQ; auto.
Qed.
End HasEqDec2Bool.

Module HasEqBool2Dec (E:Eq)(F:HasEqBool E) <: HasEqDec E.
Lemma eq_dec : forall x y, {E.eq x y}+{~E.eq x y}.
Proof. hammer_hook "Equalities" "Equalities.HasEqDec.eq_dec".  
intros x y. assert (H:=F.eqb_eq x y).
destruct (F.eqb x y); [left|right].
apply -> H; auto.
intro EQ. apply H in EQ. discriminate.
Defined.
End HasEqBool2Dec.

Module Dec2Bool (E:DecidableType) <: BooleanDecidableType
:= E <+ HasEqDec2Bool.

Module Bool2Dec (E:BooleanEqualityType) <: BooleanDecidableType
:= E <+ HasEqBool2Dec.




Module BoolEqualityFacts (Import E : BooleanEqualityType').



Instance eqb_compat : Proper (E.eq ==> E.eq ==> Logic.eq) eqb.
Proof. hammer_hook "Equalities" "Equalities.BoolEqualityFacts.eqb_compat".  
intros x x' Exx' y y' Eyy'.
apply eq_true_iff_eq.
now rewrite 2 eqb_eq, Exx', Eyy'.
Qed.



Lemma eqb_spec x y : reflect (x==y) (x =? y).
Proof. hammer_hook "Equalities" "Equalities.BoolEqualityFacts.eqb_spec".  
apply iff_reflect. symmetry. apply eqb_eq.
Defined.



Lemma eqb_neq x y : (x =? y) = false <-> x ~= y.
Proof. hammer_hook "Equalities" "Equalities.BoolEqualityFacts.eqb_neq".  
now rewrite <- not_true_iff_false, eqb_eq.
Qed.



Lemma eqb_refl x : (x =? x) = true.
Proof. hammer_hook "Equalities" "Equalities.BoolEqualityFacts.eqb_refl".  
now apply eqb_eq.
Qed.

Lemma eqb_sym x y : (x =? y) = (y =? x).
Proof. hammer_hook "Equalities" "Equalities.BoolEqualityFacts.eqb_sym".  
apply eq_true_iff_eq. now rewrite 2 eqb_eq.
Qed.



End BoolEqualityFacts.




Module Type HasUsualEq (Import T:Typ) <: HasEq T.
Definition eq := @Logic.eq t.
End HasUsualEq.

Module Type UsualEq <: Eq := Typ <+ HasUsualEq.

Module Type UsualIsEq (E:UsualEq) <: IsEq E.

Definition eq_equiv : Equivalence E.eq := eq_equivalence.
End UsualIsEq.

Module Type UsualIsEqOrig (E:UsualEq) <: IsEqOrig E.
Definition eq_refl := @Logic.eq_refl E.t.
Definition eq_sym := @Logic.eq_sym E.t.
Definition eq_trans := @Logic.eq_trans E.t.
End UsualIsEqOrig.

Module Type UsualEqualityType <: EqualityType
:= UsualEq <+ UsualIsEq.

Module Type UsualDecidableType <: DecidableType
:= UsualEq <+ UsualIsEq <+ HasEqDec.

Module Type UsualDecidableTypeOrig <: DecidableTypeOrig
:= UsualEq <+ UsualIsEqOrig <+ HasEqDec.

Module Type UsualDecidableTypeBoth <: DecidableTypeBoth
:= UsualEq <+ UsualIsEq <+ UsualIsEqOrig <+ HasEqDec.

Module Type UsualBoolEq := UsualEq <+ HasEqBool.

Module Type UsualDecidableTypeFull <: DecidableTypeFull
:= UsualEq <+ UsualIsEq <+ UsualIsEqOrig <+ HasEqDec <+ HasEqBool.




Module Type MiniDecidableType.
Include Typ.
Parameter eq_dec : forall x y : t, {x=y}+{~x=y}.
End MiniDecidableType.

Module Make_UDT (M:MiniDecidableType) <: UsualDecidableTypeBoth
:= M <+ HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

Module Make_UDTF (M:UsualBoolEq) <: UsualDecidableTypeFull
:= M <+ UsualIsEq <+ UsualIsEqOrig <+ HasEqBool2Dec.
