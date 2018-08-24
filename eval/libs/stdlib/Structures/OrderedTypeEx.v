From Hammer Require Import Hammer.









Require Import OrderedType.
Require Import ZArith.
Require Import Omega.
Require Import NArith Ndec.
Require Import Compare_dec.





Module Type UsualOrderedType.
Parameter Inline t : Type.
Definition eq := @eq t.
Parameter Inline lt : t -> t -> Prop.
Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.
Axiom lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Axiom lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Parameter compare : forall x y : t, Compare lt eq x y.
Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End UsualOrderedType.



Module UOT_to_OT (U:UsualOrderedType) <: OrderedType := U.



Module Nat_as_OT <: UsualOrderedType.

Definition t := nat.

Definition eq := @eq nat.
Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.

Definition lt := lt.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.UsualOrderedType.lt_trans". Undo.   unfold lt; intros; apply lt_trans with y; auto. Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.UsualOrderedType.lt_not_eq". Undo.   unfold lt, eq; intros; omega. Qed.

Definition compare x y : Compare lt eq x y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.UsualOrderedType.compare". Undo.  
case_eq (nat_compare x y); intro.
- apply EQ. now apply nat_compare_eq.
- apply LT. now apply nat_compare_Lt_lt.
- apply GT. now apply nat_compare_Gt_gt.
Defined.

Definition eq_dec := eq_nat_dec.

End Nat_as_OT.




Local Open Scope Z_scope.

Module Z_as_OT <: UsualOrderedType.

Definition t := Z.
Definition eq := @eq Z.
Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.

Definition lt (x y:Z) := (x<y).

Lemma lt_trans : forall x y z, x<y -> y<z -> x<z.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Nat_as_OT.lt_trans". Undo.   intros; omega. Qed.

Lemma lt_not_eq : forall x y, x<y -> ~ x=y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Nat_as_OT.lt_not_eq". Undo.   intros; omega. Qed.

Definition compare x y : Compare lt eq x y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Nat_as_OT.compare". Undo.  
case_eq (x ?= y); intro.
- apply EQ. now apply Z.compare_eq.
- apply LT. assumption.
- apply GT. now apply Z.gt_lt.
Defined.

Definition eq_dec := Z.eq_dec.

End Z_as_OT.



Local Open Scope positive_scope.

Module Positive_as_OT <: UsualOrderedType.
Definition t:=positive.
Definition eq:=@eq positive.
Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.

Definition lt := Pos.lt.

Definition lt_trans := Pos.lt_trans.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Z_as_OT.lt_not_eq". Undo.  
intros x y H. contradict H. rewrite H. apply Pos.lt_irrefl.
Qed.

Definition compare x y : Compare lt eq x y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Z_as_OT.compare". Undo.  
case_eq (x ?= y); intros H.
- apply EQ. now apply Pos.compare_eq.
- apply LT; assumption.
- apply GT. now apply Pos.gt_lt.
Defined.

Definition eq_dec := Pos.eq_dec.

End Positive_as_OT.




Module N_as_OT <: UsualOrderedType.
Definition t:=N.
Definition eq:=@eq N.
Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.

Definition lt := N.lt.
Definition lt_trans := N.lt_trans.
Definition lt_not_eq := N.lt_neq.

Definition compare x y : Compare lt eq x y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Positive_as_OT.compare". Undo.  
case_eq (x ?= y)%N; intro.
- apply EQ. now apply N.compare_eq.
- apply LT. assumption.
- apply GT. now apply N.gt_lt.
Defined.

Definition eq_dec := N.eq_dec.

End N_as_OT.




Module PairOrderedType(O1 O2:OrderedType) <: OrderedType.
Module MO1:=OrderedTypeFacts(O1).
Module MO2:=OrderedTypeFacts(O2).

Definition t := prod O1.t O2.t.

Definition eq x y := O1.eq (fst x) (fst y) /\ O2.eq (snd x) (snd y).

Definition lt x y :=
O1.lt (fst x) (fst y) \/
(O1.eq (fst x) (fst y) /\ O2.lt (snd x) (snd y)).

Lemma eq_refl : forall x : t, eq x x.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.UsualOrderedType.eq_refl". Undo.  
intros (x1,x2); red; simpl; auto.
Qed.

Lemma eq_sym : forall x y : t, eq x y -> eq y x.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.UsualOrderedType.eq_sym". Undo.  
intros (x1,x2) (y1,y2); unfold eq; simpl; intuition.
Qed.

Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.UsualOrderedType.eq_trans". Undo.  
intros (x1,x2) (y1,y2) (z1,z2); unfold eq; simpl; intuition eauto.
Qed.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Z_as_OT.lt_trans". Undo.  
intros (x1,x2) (y1,y2) (z1,z2); unfold eq, lt; simpl; intuition.
left; eauto.
left; eapply MO1.lt_eq; eauto.
left; eapply MO1.eq_lt; eauto.
right; split; eauto.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Positive_as_OT.lt_not_eq". Undo.  
intros (x1,x2) (y1,y2); unfold eq, lt; simpl; intuition.
apply (O1.lt_not_eq H0 H1).
apply (O2.lt_not_eq H3 H2).
Qed.

Definition compare : forall x y : t, Compare lt eq x y.
intros (x1,x2) (y1,y2).
destruct (O1.compare x1 y1).
apply LT; unfold lt; auto.
destruct (O2.compare x2 y2).
apply LT; unfold lt; auto.
apply EQ; unfold eq; auto.
apply GT; unfold lt; auto.
apply GT; unfold lt; auto.
Defined.

Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.UsualOrderedType.eq_dec". Undo.  
intros; elim (compare x y); intro H; [ right | left | right ]; auto.
auto using lt_not_eq.
assert (~ eq y x); auto using lt_not_eq, eq_sym.
Defined.

End PairOrderedType.




Module PositiveOrderedTypeBits <: UsualOrderedType.
Definition t:=positive.
Definition eq:=@eq positive.
Definition eq_refl := @eq_refl t.
Definition eq_sym := @eq_sym t.
Definition eq_trans := @eq_trans t.

Fixpoint bits_lt (p q:positive) : Prop :=
match p, q with
| xH, xI _ => True
| xH, _ => False
| xO p, xO q => bits_lt p q
| xO _, _ => True
| xI p, xI q => bits_lt p q
| xI _, _ => False
end.

Definition lt:=bits_lt.

Lemma bits_lt_trans :
forall x y z : positive, bits_lt x y -> bits_lt y z -> bits_lt x z.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.PositiveOrderedTypeBits.bits_lt_trans". Undo.  
induction x.
induction y; destruct z; simpl; eauto; intuition.
induction y; destruct z; simpl; eauto; intuition.
induction y; destruct z; simpl; eauto; intuition.
Qed.

Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Positive_as_OT.lt_trans". Undo.  
exact bits_lt_trans.
Qed.

Lemma bits_lt_antirefl : forall x : positive, ~ bits_lt x x.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.PositiveOrderedTypeBits.bits_lt_antirefl". Undo.  
induction x; simpl; auto.
Qed.

Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.N_as_OT.lt_not_eq". Undo.  
intros; intro.
rewrite <- H0 in H; clear H0 y.
unfold lt in H.
exact (bits_lt_antirefl x H).
Qed.

Definition compare : forall x y : t, Compare lt eq x y.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.N_as_OT.compare". Undo.  
induction x; destruct y.
-
destruct (IHx y) as [l|e|g].
apply LT; auto.
apply EQ; rewrite e; red; auto.
apply GT; auto.
-
apply GT; simpl; auto.
-
apply GT; simpl; auto.
-
apply LT; simpl; auto.
-
destruct (IHx y) as [l|e|g].
apply LT; auto.
apply EQ; rewrite e; red; auto.
apply GT; auto.
-
apply LT; simpl; auto.
-
apply LT; simpl; auto.
-
apply GT; simpl; auto.
-
apply EQ; red; auto.
Qed.

Lemma eq_dec (x y: positive): {x = y} + {x <> y}.
Proof. try hammer_hook "OrderedTypeEx" "OrderedTypeEx.Nat_as_OT.eq_dec". Undo.  
intros. case_eq (x ?= y); intros.
- left. now apply Pos.compare_eq.
- right. intro. subst y. now rewrite (Pos.compare_refl x) in *.
- right. intro. subst y. now rewrite (Pos.compare_refl x) in *.
Qed.

End PositiveOrderedTypeBits.
