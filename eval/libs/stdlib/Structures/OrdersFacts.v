From Hammer Require Import Hammer.









Require Import Bool Basics OrdersTac.
Require Export Orders.

Set Implicit Arguments.
Unset Strict Implicit.



Module Type CompareFacts (Import O:DecStrOrder').

Local Infix "?=" := compare (at level 70, no associativity).

Lemma compare_eq_iff x y : (x ?= y) = Eq <-> x==y.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareFacts.compare_eq_iff". Undo.  
case compare_spec; intro H; split; try easy; intro EQ;
contradict H; rewrite EQ; apply irreflexivity.
Qed.

Lemma compare_eq x y : (x ?= y) = Eq -> x==y.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareFacts.compare_eq". Undo.  
apply compare_eq_iff.
Qed.

Lemma compare_lt_iff x y : (x ?= y) = Lt <-> x<y.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareFacts.compare_lt_iff". Undo.  
case compare_spec; intro H; split; try easy; intro LT;
contradict LT; rewrite H; apply irreflexivity.
Qed.

Lemma compare_gt_iff x y : (x ?= y) = Gt <-> y<x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareFacts.compare_gt_iff". Undo.  
case compare_spec; intro H; split; try easy; intro LT;
contradict LT; rewrite H; apply irreflexivity.
Qed.

Lemma compare_nlt_iff x y : (x ?= y) <> Lt <-> ~(x<y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareFacts.compare_nlt_iff". Undo.  
rewrite compare_lt_iff; intuition.
Qed.

Lemma compare_ngt_iff x y : (x ?= y) <> Gt <-> ~(y<x).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareFacts.compare_ngt_iff". Undo.  
rewrite compare_gt_iff; intuition.
Qed.

Hint Rewrite compare_eq_iff compare_lt_iff compare_gt_iff : order.

Instance compare_compat : Proper (eq==>eq==>Logic.eq) compare.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareFacts.compare_compat". Undo.  
intros x x' Hxx' y y' Hyy'.
case (compare_spec x' y'); autorewrite with order; now rewrite Hxx', Hyy'.
Qed.

Lemma compare_refl x : (x ?= x) = Eq.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareFacts.compare_refl". Undo.  
case compare_spec; intros; trivial; now elim irreflexivity with x.
Qed.

Lemma compare_antisym x y : (y ?= x) = CompOpp (x ?= y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareFacts.compare_antisym". Undo.  
case (compare_spec x y); simpl; autorewrite with order;
trivial; now symmetry.
Qed.

End CompareFacts.




Module Type OrderedTypeFullFacts (Import O:OrderedTypeFull').

Module OrderTac := OTF_to_OrderTac O.
Ltac order := OrderTac.order.
Ltac iorder := intuition order.

Instance le_compat : Proper (eq==>eq==>iff) le.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.le_compat". Undo.   repeat red; iorder. Qed.

Instance le_preorder : PreOrder le.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.le_preorder". Undo.   split; red; order. Qed.

Instance le_order : PartialOrder eq le.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.le_order". Undo.   compute; iorder. Qed.

Instance le_antisym : Antisymmetric _ eq le.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.le_antisym". Undo.   apply partial_order_antisym; auto with *. Qed.

Lemma le_not_gt_iff : forall x y, x<=y <-> ~y<x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.le_not_gt_iff". Undo.   iorder. Qed.

Lemma lt_not_ge_iff : forall x y, x<y <-> ~y<=x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.lt_not_ge_iff". Undo.   iorder. Qed.

Lemma le_or_gt : forall x y, x<=y \/ y<x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.le_or_gt". Undo.   intros. rewrite le_lteq; destruct (O.compare_spec x y); auto. Qed.

Lemma lt_or_ge : forall x y, x<y \/ y<=x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.lt_or_ge". Undo.   intros. rewrite le_lteq; destruct (O.compare_spec x y); iorder. Qed.

Lemma eq_is_le_ge : forall x y, x==y <-> x<=y /\ y<=x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.eq_is_le_ge". Undo.   iorder. Qed.

Include CompareFacts O.

Lemma compare_le_iff x y : compare x y <> Gt <-> x<=y.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.compare_le_iff". Undo.  
rewrite le_not_gt_iff. apply compare_ngt_iff.
Qed.

Lemma compare_ge_iff x y : compare x y <> Lt <-> y<=x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFullFacts.compare_ge_iff". Undo.  
rewrite le_not_gt_iff. apply compare_nlt_iff.
Qed.

End OrderedTypeFullFacts.




Module OrderedTypeFacts (Import O: OrderedType').

Module OrderTac := OT_to_OrderTac O.
Ltac order := OrderTac.order.

Notation "x <= y" := (~lt y x) : order.
Infix "?=" := compare (at level 70, no associativity) : order.

Local Open Scope order.

Tactic Notation "elim_compare" constr(x) constr(y) :=
destruct (compare_spec x y).

Tactic Notation "elim_compare" constr(x) constr(y) "as" ident(h) :=
destruct (compare_spec x y) as [h|h|h].



Definition eq_refl (x:t) : x==x := Equivalence_Reflexive x.

Definition eq_sym (x y:t) : x==y -> y==x := Equivalence_Symmetric x y.

Definition eq_trans (x y z:t) : x==y -> y==z -> x==z :=
Equivalence_Transitive x y z.

Definition lt_trans (x y z:t) : x<y -> y<z -> x<z :=
StrictOrder_Transitive x y z.

Definition lt_irrefl (x:t) : ~x<x := StrictOrder_Irreflexive x.

Include CompareFacts O.
Notation compare_le_iff := compare_ngt_iff (only parsing).
Notation compare_ge_iff := compare_nlt_iff (only parsing).


Definition eq_dec := eq_dec.

Lemma lt_dec : forall x y : t, {lt x y} + {~ lt x y}.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFacts.lt_dec". Undo.  
intros x y; destruct (CompSpec2Type (compare_spec x y));
[ right | left | right ]; order.
Defined.

Definition eqb x y : bool := if eq_dec x y then true else false.

Lemma if_eq_dec : forall x y (B:Type)(b b':B),
(if eq_dec x y then b else b') =
(match compare x y with Eq => b | _ => b' end).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFacts.if_eq_dec". Undo.  
intros; destruct eq_dec; elim_compare x y; auto; order.
Qed.

Lemma eqb_alt :
forall x y, eqb x y = match compare x y with Eq => true | _ => false end.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFacts.eqb_alt". Undo.  
unfold eqb; intros; apply if_eq_dec.
Qed.

Instance eqb_compat : Proper (eq==>eq==>Logic.eq) eqb.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFacts.eqb_compat". Undo.  
intros x x' Hxx' y y' Hyy'.
rewrite 2 eqb_alt, Hxx', Hyy'; auto.
Qed.

End OrderedTypeFacts.




Module OrderedTypeTest (Import O:OrderedType').
Module Import MO := OrderedTypeFacts O.
Local Open Scope order.
Lemma lt_not_eq x y : x<y -> ~x==y.  Proof. order. Qed.
Lemma lt_eq x y z : x<y -> y==z -> x<z. Proof. order. Qed.
Lemma eq_lt x y z : x==y -> y<z -> x<z. Proof. order. Qed.
Lemma le_eq x y z : x<=y -> y==z -> x<=z. Proof. order. Qed.
Lemma eq_le x y z : x==y -> y<=z -> x<=z. Proof. order. Qed.
Lemma neq_eq x y z : ~x==y -> y==z -> ~x==z. Proof. order. Qed.
Lemma eq_neq x y z : x==y -> ~y==z -> ~x==z. Proof. order. Qed.
Lemma le_lt_trans x y z : x<=y -> y<z -> x<z. Proof. order. Qed.
Lemma lt_le_trans x y z : x<y -> y<=z -> x<z. Proof. order. Qed.
Lemma le_trans x y z : x<=y -> y<=z -> x<=z. Proof. order. Qed.
Lemma le_antisym x y : x<=y -> y<=x -> x==y. Proof. order. Qed.
Lemma le_neq x y : x<=y -> ~x==y -> x<y. Proof. order. Qed.
Lemma neq_sym x y : ~x==y -> ~y==x. Proof. order. Qed.
Lemma lt_le x y : x<y -> x<=y. Proof. order. Qed.
Lemma gt_not_eq x y : y<x -> ~x==y. Proof. order. Qed.
Lemma eq_not_lt x y : x==y -> ~x<y. Proof. order. Qed.
Lemma eq_not_gt x y : x==y -> ~ y<x. Proof. order. Qed.
Lemma lt_not_gt x y : x<y -> ~ y<x. Proof. order. Qed.
Lemma eq_is_nlt_ngt x y : x==y <-> ~x<y /\ ~y<x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeTest.eq_is_nlt_ngt". Undo.   intuition; order. Qed.
End OrderedTypeTest.





Module OrderedTypeRev (O:OrderedTypeFull) <: OrderedTypeFull.

Definition t := O.t.
Definition eq := O.eq.
Program Instance eq_equiv : Equivalence eq.
Definition eq_dec := O.eq_dec.

Definition lt := flip O.lt.
Definition le := flip O.le.

Instance lt_strorder: StrictOrder lt.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeRev.lt_strorder". Undo.   unfold lt; auto with *. Qed.
Instance lt_compat : Proper (eq==>eq==>iff) lt.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeRev.lt_compat". Undo.   unfold lt; auto with *. Qed.

Lemma le_lteq : forall x y, le x y <-> lt x y \/ eq x y.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeRev.le_lteq". Undo.   intros; unfold le, lt, flip. rewrite O.le_lteq; intuition. Qed.

Definition compare := flip O.compare.

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeRev.compare_spec". Undo.  
intros; unfold compare, eq, lt, flip.
destruct (O.compare_spec y x); auto with relations.
Qed.

End OrderedTypeRev.

Unset Implicit Arguments.



Module Type CompareBasedOrder (Import E:EqLtLe')(Import C:HasCmp E).
Include CmpNotation E C.
Include IsEq E.
Axiom compare_eq_iff : forall x y, (x ?= y) = Eq <-> x == y.
Axiom compare_lt_iff : forall x y, (x ?= y) = Lt <-> x < y.
Axiom compare_le_iff : forall x y, (x ?= y) <> Gt <-> x <= y.
Axiom compare_antisym : forall x y, (y ?= x) = CompOpp (x ?= y).
End CompareBasedOrder.

Module Type CompareBasedOrderFacts
(Import E:EqLtLe')
(Import C:HasCmp E)
(Import O:CompareBasedOrder E C).

Lemma compare_spec x y : CompareSpec (x==y) (x<y) (y<x) (x?=y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareBasedOrderFacts.compare_spec". Undo.  
case_eq (compare x y); intros H; constructor.
now apply compare_eq_iff.
now apply compare_lt_iff.
rewrite compare_antisym, CompOpp_iff in H. now apply compare_lt_iff.
Qed.

Lemma compare_eq x y : (x ?= y) = Eq -> x==y.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareBasedOrderFacts.compare_eq". Undo.  
apply compare_eq_iff.
Qed.

Lemma compare_refl x : (x ?= x) = Eq.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareBasedOrderFacts.compare_refl". Undo.  
now apply compare_eq_iff.
Qed.

Lemma compare_gt_iff x y : (x ?= y) = Gt <-> y<x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareBasedOrderFacts.compare_gt_iff". Undo.  
now rewrite <- compare_lt_iff, compare_antisym, CompOpp_iff.
Qed.

Lemma compare_ge_iff x y : (x ?= y) <> Lt <-> y<=x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFacts.compare_ge_iff". Undo.  
now rewrite <- compare_le_iff, compare_antisym, CompOpp_iff.
Qed.

Lemma compare_ngt_iff x y : (x ?= y) <> Gt <-> ~(y<x).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareBasedOrderFacts.compare_ngt_iff". Undo.  
rewrite compare_gt_iff; intuition.
Qed.

Lemma compare_nlt_iff x y : (x ?= y) <> Lt <-> ~(x<y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareBasedOrderFacts.compare_nlt_iff". Undo.  
rewrite compare_lt_iff; intuition.
Qed.

Lemma compare_nle_iff x y : (x ?= y) = Gt <-> ~(x<=y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareBasedOrderFacts.compare_nle_iff". Undo.  
rewrite <- compare_le_iff.
destruct compare; split; easy || now destruct 1.
Qed.

Lemma compare_nge_iff x y : (x ?= y) = Lt <-> ~(y<=x).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareBasedOrderFacts.compare_nge_iff". Undo.  
now rewrite <- compare_nle_iff, compare_antisym, CompOpp_iff.
Qed.

Lemma lt_irrefl x : ~ (x<x).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.OrderedTypeFacts.lt_irrefl". Undo.  
now rewrite <- compare_lt_iff, compare_refl.
Qed.

Lemma lt_eq_cases n m : n <= m <-> n < m \/ n==m.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.CompareBasedOrderFacts.lt_eq_cases". Undo.  
rewrite <- compare_lt_iff, <- compare_le_iff, <- compare_eq_iff.
destruct (n ?= m); now intuition.
Qed.

End CompareBasedOrderFacts.



Module Type BoolOrderFacts
(Import E:EqLtLe')
(Import C:HasCmp E)
(Import F:HasBoolOrdFuns' E)
(Import O:CompareBasedOrder E C)
(Import S:BoolOrdSpecs E F).

Include CompareBasedOrderFacts E C O.





Lemma leb_spec0 x y : reflect (x<=y) (x<=?y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.leb_spec0". Undo.  
apply iff_reflect. symmetry. apply leb_le.
Defined.

Lemma leb_spec x y : BoolSpec (x<=y) (y<x) (x<=?y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.leb_spec". Undo.  
case leb_spec0; constructor; trivial.
now rewrite <- compare_lt_iff, compare_nge_iff.
Qed.

Lemma ltb_spec0 x y : reflect (x<y) (x<?y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.ltb_spec0". Undo.  
apply iff_reflect. symmetry. apply ltb_lt.
Defined.

Lemma ltb_spec x y : BoolSpec (x<y) (y<=x) (x<?y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.ltb_spec". Undo.  
case ltb_spec0; constructor; trivial.
now rewrite <- compare_le_iff, compare_ngt_iff.
Qed.



Lemma leb_nle x y : x <=? y = false <-> ~ (x <= y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.leb_nle". Undo.  
now rewrite <- not_true_iff_false, leb_le.
Qed.

Lemma leb_gt x y : x <=? y = false <-> y < x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.leb_gt". Undo.  
now rewrite leb_nle, <- compare_lt_iff, compare_nge_iff.
Qed.

Lemma ltb_nlt x y : x <? y = false <-> ~ (x < y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.ltb_nlt". Undo.  
now rewrite <- not_true_iff_false, ltb_lt.
Qed.

Lemma ltb_ge x y : x <? y = false <-> y <= x.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.ltb_ge". Undo.  
now rewrite ltb_nlt, <- compare_le_iff, compare_ngt_iff.
Qed.



Lemma leb_refl x : x <=? x = true.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.leb_refl". Undo.  
apply leb_le. apply lt_eq_cases. now right.
Qed.

Lemma leb_antisym x y : y <=? x = negb (x <? y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.leb_antisym". Undo.  
apply eq_true_iff_eq. now rewrite negb_true_iff, leb_le, ltb_ge.
Qed.

Lemma ltb_irrefl x : x <? x = false.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.ltb_irrefl". Undo.  
apply ltb_ge. apply lt_eq_cases. now right.
Qed.

Lemma ltb_antisym x y : y <? x = negb (x <=? y).
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.ltb_antisym". Undo.  
apply eq_true_iff_eq. now rewrite negb_true_iff, ltb_lt, leb_gt.
Qed.



Lemma eqb_compare x y :
(x =? y) = match compare x y with Eq => true | _ => false end.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.eqb_compare". Undo.  
apply eq_true_iff_eq. rewrite eqb_eq, <- compare_eq_iff.
now destruct compare.
Qed.

Lemma ltb_compare x y :
(x <? y) = match compare x y with Lt => true | _ => false end.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.ltb_compare". Undo.  
apply eq_true_iff_eq. rewrite ltb_lt, <- compare_lt_iff.
now destruct compare.
Qed.

Lemma leb_compare x y :
(x <=? y) = match compare x y with Gt => false | _ => true end.
Proof. try hammer_hook "OrdersFacts" "OrdersFacts.BoolOrderFacts.leb_compare". Undo.  
apply eq_true_iff_eq. rewrite leb_le, <- compare_le_iff.
now destruct compare.
Qed.

End BoolOrderFacts.
