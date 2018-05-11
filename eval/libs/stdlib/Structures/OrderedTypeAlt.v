From Hammer Require Import Hammer.








Require Import OrderedType.





Module Type OrderedTypeAlt.

Parameter t : Type.

Parameter compare : t -> t -> comparison.

Infix "?=" := compare (at level 70, no associativity).

Parameter compare_sym :
forall x y, (y?=x) = CompOpp (x?=y).
Parameter compare_trans :
forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.

End OrderedTypeAlt.



Module OrderedType_from_Alt (O:OrderedTypeAlt) <: OrderedType.
Import O.

Definition t := t.

Definition eq x y := (x?=y) = Eq.
Definition lt x y := (x?=y) = Lt.

Lemma eq_refl : forall x, eq x x.
Proof. try hammer_hook "OrderedTypeAlt" "OrderedTypeAlt.OrderedType_from_Alt.eq_refl".  
intro x.
unfold eq.
assert (H:=compare_sym x x).
destruct (x ?= x); simpl in *; try discriminate; auto.
Qed.

Lemma eq_sym : forall x y, eq x y -> eq y x.
Proof. try hammer_hook "OrderedTypeAlt" "OrderedTypeAlt.OrderedType_from_Alt.eq_sym".  
unfold eq; intros.
rewrite compare_sym.
rewrite H; simpl; auto.
Qed.

Definition eq_trans := (compare_trans Eq).

Definition lt_trans := (compare_trans Lt).

Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
Proof. try hammer_hook "OrderedTypeAlt" "OrderedTypeAlt.OrderedType_from_Alt.lt_not_eq".  
unfold eq, lt; intros.
rewrite H; discriminate.
Qed.

Definition compare : forall x y, Compare lt eq x y.
Proof. try hammer_hook "OrderedTypeAlt" "OrderedTypeAlt.OrderedTypeAlt.compare".  
intros.
case_eq (x ?= y); intros.
apply EQ; auto.
apply LT; auto.
apply GT; red.
rewrite compare_sym; rewrite H; auto.
Defined.

Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
Proof. try hammer_hook "OrderedTypeAlt" "OrderedTypeAlt.OrderedType_from_Alt.eq_dec".  
intros; unfold eq.
case (x ?= y); [ left | right | right ]; auto; discriminate.
Defined.

End OrderedType_from_Alt.



Module OrderedType_to_Alt (O:OrderedType) <: OrderedTypeAlt.
Import O.
Module MO:=OrderedTypeFacts(O).
Import MO.

Definition t := t.

Definition compare x y := match compare x y with
| LT _ => Lt
| EQ _ => Eq
| GT _ => Gt
end.

Infix "?=" := compare (at level 70, no associativity).

Lemma compare_sym :
forall x y, (y?=x) = CompOpp (x?=y).
Proof. try hammer_hook "OrderedTypeAlt" "OrderedTypeAlt.OrderedTypeAlt.compare_sym".  
intros x y; unfold compare.
destruct O.compare; elim_comp; simpl; auto.
Qed.

Lemma compare_trans :
forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
Proof. try hammer_hook "OrderedTypeAlt" "OrderedTypeAlt.OrderedTypeAlt.compare_trans".  
intros c x y z.
destruct c; unfold compare;
do 2 (destruct O.compare; intros; try discriminate);
elim_comp; auto.
Qed.

End OrderedType_to_Alt.


