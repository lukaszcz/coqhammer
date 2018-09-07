From Hammer Require Import Hammer.









Require Import DecidableType OrderedType OrderedTypeEx.
Set Implicit Arguments.
Unset Strict Implicit.







Module Type UsualDecidableType := Equalities.UsualDecidableTypeOrig.



Module UDT_to_DT (U:UsualDecidableType) <: DecidableType := U.



Module Type MiniDecidableType := Equalities.MiniDecidableType.

Module Make_UDT (M:MiniDecidableType) <: UsualDecidableType
:= Equalities.Make_UDT M.



Module OT_as_DT (O:OrderedType) <: DecidableType := O.



Module Nat_as_DT <: UsualDecidableType := Nat_as_OT.
Module Positive_as_DT <: UsualDecidableType := Positive_as_OT.
Module N_as_DT <: UsualDecidableType := N_as_OT.
Module Z_as_DT <: UsualDecidableType := Z_as_OT.



Module PairDecidableType(D1 D2:DecidableType) <: DecidableType.

Definition t := prod D1.t D2.t.

Definition eq x y := D1.eq (fst x) (fst y) /\ D2.eq (snd x) (snd y).

Lemma eq_refl : forall x : t, eq x x.
Proof. hammer_hook "DecidableTypeEx" "DecidableTypeEx.PairDecidableType.eq_refl".  
intros (x1,x2); red; simpl; auto.
Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. hammer_hook "DecidableTypeEx" "DecidableTypeEx.PairDecidableType.eq_sym".  
intros (x1,x2) (y1,y2); unfold eq; simpl; intuition.
Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. hammer_hook "DecidableTypeEx" "DecidableTypeEx.PairDecidableType.eq_trans".  
intros (x1,x2) (y1,y2) (z1,z2); unfold eq; simpl; intuition eauto.
Qed.

Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
Proof. hammer_hook "DecidableTypeEx" "DecidableTypeEx.PairDecidableType.eq_dec".  
intros (x1,x2) (y1,y2); unfold eq; simpl.
destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2); intuition.
Defined.

End PairDecidableType.



Module PairUsualDecidableType(D1 D2:UsualDecidableType) <: UsualDecidableType.
Definition t := prod D1.t D2.t.
Definition eq := @eq t.
Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.
Definition eq_dec : forall x y, { eq x y }+{ ~eq x y }.
Proof. hammer_hook "DecidableTypeEx" "DecidableTypeEx.PairUsualDecidableType.eq_dec".  
intros (x1,x2) (y1,y2);
destruct (D1.eq_dec x1 y1); destruct (D2.eq_dec x2 y2);
unfold eq, D1.eq, D2.eq in *; simpl;
(left; f_equal; auto; fail) ||
(right; injection; auto).
Defined.

End PairUsualDecidableType.
