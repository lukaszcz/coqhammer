From Hammer Require Import Hammer.













Ltac destr_bool :=
intros; destruct_all bool; simpl in *; trivial; try discriminate.



Definition Is_true (b:bool) :=
match b with
| true => True
| false => False
end.





Lemma bool_dec : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}.
Proof. hammer_hook "Bool" "Bool.bool_dec". Restart. 
decide equality.
Defined.





Lemma diff_true_false : true <> false.
Proof. hammer_hook "Bool" "Bool.diff_true_false". Restart. 
discriminate.
Qed.
Hint Resolve diff_true_false : bool.

Lemma diff_false_true : false <> true.
Proof. hammer_hook "Bool" "Bool.diff_false_true". Restart. 
discriminate.
Qed.
Hint Resolve diff_false_true : bool.
Hint Extern 1 (false <> true) => exact diff_false_true.

Lemma eq_true_false_abs : forall b:bool, b = true -> b = false -> False.
Proof. hammer_hook "Bool" "Bool.eq_true_false_abs". Restart. 
destr_bool.
Qed.

Lemma not_true_is_false : forall b:bool, b <> true -> b = false.
Proof. hammer_hook "Bool" "Bool.not_true_is_false". Restart. 
destr_bool; intuition.
Qed.

Lemma not_false_is_true : forall b:bool, b <> false -> b = true.
Proof. hammer_hook "Bool" "Bool.not_false_is_true". Restart. 
destr_bool; intuition.
Qed.

Lemma not_true_iff_false : forall b, b <> true <-> b = false.
Proof. hammer_hook "Bool" "Bool.not_true_iff_false". Restart. 
destr_bool; intuition.
Qed.

Lemma not_false_iff_true : forall b, b <> false <-> b = true.
Proof. hammer_hook "Bool" "Bool.not_false_iff_true". Restart. 
destr_bool; intuition.
Qed.





Definition leb (b1 b2:bool) :=
match b1 with
| true => b2 = true
| false => True
end.
Hint Unfold leb: bool.

Lemma leb_implb : forall b1 b2, leb b1 b2 <-> implb b1 b2 = true.
Proof. hammer_hook "Bool" "Bool.leb_implb". Restart. 
destr_bool; intuition.
Qed.







Definition eqb (b1 b2:bool) : bool :=
match b1, b2 with
| true, true => true
| true, false => false
| false, true => false
| false, false => true
end.

Lemma eqb_subst :
forall (P:bool -> Prop) (b1 b2:bool), eqb b1 b2 = true -> P b1 -> P b2.
Proof. hammer_hook "Bool" "Bool.eqb_subst". Restart. 
destr_bool.
Qed.

Lemma eqb_reflx : forall b:bool, eqb b b = true.
Proof. hammer_hook "Bool" "Bool.eqb_reflx". Restart. 
destr_bool.
Qed.

Lemma eqb_prop : forall a b:bool, eqb a b = true -> a = b.
Proof. hammer_hook "Bool" "Bool.eqb_prop". Restart. 
destr_bool.
Qed.

Lemma eqb_true_iff : forall a b:bool, eqb a b = true <-> a = b.
Proof. hammer_hook "Bool" "Bool.eqb_true_iff". Restart. 
destr_bool; intuition.
Qed.

Lemma eqb_false_iff : forall a b:bool, eqb a b = false <-> a <> b.
Proof. hammer_hook "Bool" "Bool.eqb_false_iff". Restart. 
destr_bool; intuition.
Qed.





Definition ifb (b1 b2 b3:bool) : bool :=
match b1 with
| true => b2
| false => b3
end.

Open Scope bool_scope.





Lemma negb_orb : forall b1 b2:bool, negb (b1 || b2) = negb b1 && negb b2.
Proof. hammer_hook "Bool" "Bool.negb_orb". Restart. 
destr_bool.
Qed.

Lemma negb_andb : forall b1 b2:bool, negb (b1 && b2) = negb b1 || negb b2.
Proof. hammer_hook "Bool" "Bool.negb_andb". Restart. 
destr_bool.
Qed.





Lemma negb_involutive : forall b:bool, negb (negb b) = b.
Proof. hammer_hook "Bool" "Bool.negb_involutive". Restart. 
destr_bool.
Qed.

Lemma negb_involutive_reverse : forall b:bool, b = negb (negb b).
Proof. hammer_hook "Bool" "Bool.negb_involutive_reverse". Restart. 
destr_bool.
Qed.

Notation negb_elim := negb_involutive (only parsing).
Notation negb_intro := negb_involutive_reverse (only parsing).

Lemma negb_sym : forall b b':bool, b' = negb b -> b = negb b'.
Proof. hammer_hook "Bool" "Bool.negb_sym". Restart. 
destr_bool.
Qed.

Lemma no_fixpoint_negb : forall b:bool, negb b <> b.
Proof. hammer_hook "Bool" "Bool.no_fixpoint_negb". Restart. 
destr_bool.
Qed.

Lemma eqb_negb1 : forall b:bool, eqb (negb b) b = false.
Proof. hammer_hook "Bool" "Bool.eqb_negb1". Restart. 
destr_bool.
Qed.

Lemma eqb_negb2 : forall b:bool, eqb b (negb b) = false.
Proof. hammer_hook "Bool" "Bool.eqb_negb2". Restart. 
destr_bool.
Qed.

Lemma if_negb :
forall (A:Type) (b:bool) (x y:A),
(if negb b then x else y) = (if b then y else x).
Proof. hammer_hook "Bool" "Bool.if_negb". Restart. 
destr_bool.
Qed.

Lemma negb_true_iff : forall b, negb b = true <-> b = false.
Proof. hammer_hook "Bool" "Bool.negb_true_iff". Restart. 
destr_bool; intuition.
Qed.

Lemma negb_false_iff : forall b, negb b = false <-> b = true.
Proof. hammer_hook "Bool" "Bool.negb_false_iff". Restart. 
destr_bool; intuition.
Qed.






Lemma orb_true_iff :
forall b1 b2, b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof. hammer_hook "Bool" "Bool.orb_true_iff". Restart. 
destr_bool; intuition.
Qed.

Lemma orb_false_iff :
forall b1 b2, b1 || b2 = false <-> b1 = false /\ b2 = false.
Proof. hammer_hook "Bool" "Bool.orb_false_iff". Restart. 
destr_bool; intuition.
Qed.

Lemma orb_true_elim :
forall b1 b2:bool, b1 || b2 = true -> {b1 = true} + {b2 = true}.
Proof. hammer_hook "Bool" "Bool.orb_true_elim". Restart. 
destruct b1; simpl; auto.
Defined.

Lemma orb_prop : forall a b:bool, a || b = true -> a = true \/ b = true.
Proof. hammer_hook "Bool" "Bool.orb_prop". Restart. 
intros; apply orb_true_iff; trivial.
Qed.

Lemma orb_true_intro :
forall b1 b2:bool, b1 = true \/ b2 = true -> b1 || b2 = true.
Proof. hammer_hook "Bool" "Bool.orb_true_intro". Restart. 
intros; apply orb_true_iff; trivial.
Qed.
Hint Resolve orb_true_intro: bool.

Lemma orb_false_intro :
forall b1 b2:bool, b1 = false -> b2 = false -> b1 || b2 = false.
Proof. hammer_hook "Bool" "Bool.orb_false_intro". Restart. 
intros. subst. reflexivity.
Qed.
Hint Resolve orb_false_intro: bool.

Lemma orb_false_elim :
forall b1 b2:bool, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof. hammer_hook "Bool" "Bool.orb_false_elim". Restart. 
intros. apply orb_false_iff; trivial.
Qed.

Lemma orb_diag : forall b, b || b = b.
Proof. hammer_hook "Bool" "Bool.orb_diag". Restart. 
destr_bool.
Qed.



Lemma orb_true_r : forall b:bool, b || true = true.
Proof. hammer_hook "Bool" "Bool.orb_true_r". Restart. 
destr_bool.
Qed.
Hint Resolve orb_true_r: bool.

Lemma orb_true_l : forall b:bool, true || b = true.
Proof. hammer_hook "Bool" "Bool.orb_true_l". Restart. 
reflexivity.
Qed.

Notation orb_b_true := orb_true_r (only parsing).
Notation orb_true_b := orb_true_l (only parsing).



Lemma orb_false_r : forall b:bool, b || false = b.
Proof. hammer_hook "Bool" "Bool.orb_false_r". Restart. 
destr_bool.
Qed.
Hint Resolve orb_false_r: bool.

Lemma orb_false_l : forall b:bool, false || b = b.
Proof. hammer_hook "Bool" "Bool.orb_false_l". Restart. 
destr_bool.
Qed.
Hint Resolve orb_false_l: bool.

Notation orb_b_false := orb_false_r (only parsing).
Notation orb_false_b := orb_false_l (only parsing).



Lemma orb_negb_r : forall b:bool, b || negb b = true.
Proof. hammer_hook "Bool" "Bool.orb_negb_r". Restart. 
destr_bool.
Qed.
Hint Resolve orb_negb_r: bool.

Notation orb_neg_b := orb_negb_r (only parsing).



Lemma orb_comm : forall b1 b2:bool, b1 || b2 = b2 || b1.
Proof. hammer_hook "Bool" "Bool.orb_comm". Restart. 
destr_bool.
Qed.



Lemma orb_assoc : forall b1 b2 b3:bool, b1 || (b2 || b3) = b1 || b2 || b3.
Proof. hammer_hook "Bool" "Bool.orb_assoc". Restart. 
destr_bool.
Qed.
Hint Resolve orb_comm orb_assoc: bool.





Lemma andb_true_iff :
forall b1 b2:bool, b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof. hammer_hook "Bool" "Bool.andb_true_iff". Restart. 
destr_bool; intuition.
Qed.

Lemma andb_false_iff :
forall b1 b2:bool, b1 && b2 = false <-> b1 = false \/ b2 = false.
Proof. hammer_hook "Bool" "Bool.andb_false_iff". Restart. 
destr_bool; intuition.
Qed.

Lemma andb_true_eq :
forall a b:bool, true = a && b -> true = a /\ true = b.
Proof. hammer_hook "Bool" "Bool.andb_true_eq". Restart. 
destr_bool. auto.
Defined.

Lemma andb_false_intro1 : forall b1 b2:bool, b1 = false -> b1 && b2 = false.
Proof. hammer_hook "Bool" "Bool.andb_false_intro1". Restart. 
intros. apply andb_false_iff. auto.
Qed.

Lemma andb_false_intro2 : forall b1 b2:bool, b2 = false -> b1 && b2 = false.
Proof. hammer_hook "Bool" "Bool.andb_false_intro2". Restart. 
intros. apply andb_false_iff. auto.
Qed.



Lemma andb_false_r : forall b:bool, b && false = false.
Proof. hammer_hook "Bool" "Bool.andb_false_r". Restart. 
destr_bool.
Qed.

Lemma andb_false_l : forall b:bool, false && b = false.
Proof. hammer_hook "Bool" "Bool.andb_false_l". Restart. 
reflexivity.
Qed.

Notation andb_b_false := andb_false_r (only parsing).
Notation andb_false_b := andb_false_l (only parsing).

Lemma andb_diag : forall b, b && b = b.
Proof. hammer_hook "Bool" "Bool.andb_diag". Restart. 
destr_bool.
Qed.



Lemma andb_true_r : forall b:bool, b && true = b.
Proof. hammer_hook "Bool" "Bool.andb_true_r". Restart. 
destr_bool.
Qed.

Lemma andb_true_l : forall b:bool, true && b = b.
Proof. hammer_hook "Bool" "Bool.andb_true_l". Restart. 
reflexivity.
Qed.

Notation andb_b_true := andb_true_r (only parsing).
Notation andb_true_b := andb_true_l (only parsing).

Lemma andb_false_elim :
forall b1 b2:bool, b1 && b2 = false -> {b1 = false} + {b2 = false}.
Proof. hammer_hook "Bool" "Bool.andb_false_elim". Restart. 
destruct b1; simpl; auto.
Defined.
Hint Resolve andb_false_elim: bool.



Lemma andb_negb_r : forall b:bool, b && negb b = false.
Proof. hammer_hook "Bool" "Bool.andb_negb_r". Restart. 
destr_bool.
Qed.
Hint Resolve andb_negb_r: bool.

Notation andb_neg_b := andb_negb_r (only parsing).



Lemma andb_comm : forall b1 b2:bool, b1 && b2 = b2 && b1.
Proof. hammer_hook "Bool" "Bool.andb_comm". Restart. 
destr_bool.
Qed.



Lemma andb_assoc : forall b1 b2 b3:bool, b1 && (b2 && b3) = b1 && b2 && b3.
Proof. hammer_hook "Bool" "Bool.andb_assoc". Restart. 
destr_bool.
Qed.

Hint Resolve andb_comm andb_assoc: bool.







Lemma andb_orb_distrib_r :
forall b1 b2 b3:bool, b1 && (b2 || b3) = b1 && b2 || b1 && b3.
Proof. hammer_hook "Bool" "Bool.andb_orb_distrib_r". Restart. 
destr_bool.
Qed.

Lemma andb_orb_distrib_l :
forall b1 b2 b3:bool, (b1 || b2) && b3 = b1 && b3 || b2 && b3.
Proof. hammer_hook "Bool" "Bool.andb_orb_distrib_l". Restart. 
destr_bool.
Qed.

Lemma orb_andb_distrib_r :
forall b1 b2 b3:bool, b1 || b2 && b3 = (b1 || b2) && (b1 || b3).
Proof. hammer_hook "Bool" "Bool.orb_andb_distrib_r". Restart. 
destr_bool.
Qed.

Lemma orb_andb_distrib_l :
forall b1 b2 b3:bool, b1 && b2 || b3 = (b1 || b3) && (b2 || b3).
Proof. hammer_hook "Bool" "Bool.orb_andb_distrib_l". Restart. 
destr_bool.
Qed.


Notation demorgan1 := andb_orb_distrib_r (only parsing).
Notation demorgan2 := andb_orb_distrib_l (only parsing).
Notation demorgan3 := orb_andb_distrib_r (only parsing).
Notation demorgan4 := orb_andb_distrib_l (only parsing).



Lemma absorption_andb : forall b1 b2:bool, b1 && (b1 || b2) = b1.
Proof. hammer_hook "Bool" "Bool.absorption_andb". Restart. 
destr_bool.
Qed.

Lemma absorption_orb : forall b1 b2:bool, b1 || b1 && b2 = b1.
Proof. hammer_hook "Bool" "Bool.absorption_orb". Restart. 
destr_bool.
Qed.



Notation absoption_andb := absorption_andb (only parsing).
Notation absoption_orb := absorption_orb (only parsing).








Lemma xorb_false_r : forall b:bool, xorb b false = b.
Proof. hammer_hook "Bool" "Bool.xorb_false_r". Restart. 
destr_bool.
Qed.

Lemma xorb_false_l : forall b:bool, xorb false b = b.
Proof. hammer_hook "Bool" "Bool.xorb_false_l". Restart. 
destr_bool.
Qed.

Notation xorb_false := xorb_false_r (only parsing).
Notation false_xorb := xorb_false_l (only parsing).



Lemma xorb_true_r : forall b:bool, xorb b true = negb b.
Proof. hammer_hook "Bool" "Bool.xorb_true_r". Restart. 
reflexivity.
Qed.

Lemma xorb_true_l : forall b:bool, xorb true b = negb b.
Proof. hammer_hook "Bool" "Bool.xorb_true_l". Restart. 
reflexivity.
Qed.

Notation xorb_true := xorb_true_r (only parsing).
Notation true_xorb := xorb_true_l (only parsing).



Lemma xorb_nilpotent : forall b:bool, xorb b b = false.
Proof. hammer_hook "Bool" "Bool.xorb_nilpotent". Restart. 
destr_bool.
Qed.



Lemma xorb_comm : forall b b':bool, xorb b b' = xorb b' b.
Proof. hammer_hook "Bool" "Bool.xorb_comm". Restart. 
destr_bool.
Qed.



Lemma xorb_assoc_reverse :
forall b b' b'':bool, xorb (xorb b b') b'' = xorb b (xorb b' b'').
Proof. hammer_hook "Bool" "Bool.xorb_assoc_reverse". Restart. 
destr_bool.
Qed.

Notation xorb_assoc := xorb_assoc_reverse (only parsing).

Lemma xorb_eq : forall b b':bool, xorb b b' = false -> b = b'.
Proof. hammer_hook "Bool" "Bool.xorb_eq". Restart. 
destr_bool.
Qed.

Lemma xorb_move_l_r_1 :
forall b b' b'':bool, xorb b b' = b'' -> b' = xorb b b''.
Proof. hammer_hook "Bool" "Bool.xorb_move_l_r_1". Restart. 
destr_bool.
Qed.

Lemma xorb_move_l_r_2 :
forall b b' b'':bool, xorb b b' = b'' -> b = xorb b'' b'.
Proof. hammer_hook "Bool" "Bool.xorb_move_l_r_2". Restart. 
destr_bool.
Qed.

Lemma xorb_move_r_l_1 :
forall b b' b'':bool, b = xorb b' b'' -> xorb b' b = b''.
Proof. hammer_hook "Bool" "Bool.xorb_move_r_l_1". Restart. 
destr_bool.
Qed.

Lemma xorb_move_r_l_2 :
forall b b' b'':bool, b = xorb b' b'' -> xorb b b'' = b'.
Proof. hammer_hook "Bool" "Bool.xorb_move_r_l_2". Restart. 
destr_bool.
Qed.

Lemma negb_xorb_l : forall b b', negb (xorb b b') = xorb (negb b) b'.
Proof. hammer_hook "Bool" "Bool.negb_xorb_l". Restart. 
destruct b,b'; trivial.
Qed.

Lemma negb_xorb_r : forall b b', negb (xorb b b') = xorb b (negb b').
Proof. hammer_hook "Bool" "Bool.negb_xorb_r". Restart. 
destruct b,b'; trivial.
Qed.

Lemma xorb_negb_negb : forall b b', xorb (negb b) (negb b') = xorb b b'.
Proof. hammer_hook "Bool" "Bool.xorb_negb_negb". Restart. 
destruct b,b'; trivial.
Qed.



Lemma eq_iff_eq_true : forall b1 b2, b1 = b2 <-> (b1 = true <-> b2 = true).
Proof. hammer_hook "Bool" "Bool.eq_iff_eq_true". Restart. 
destr_bool; intuition.
Qed.

Lemma eq_true_iff_eq : forall b1 b2, (b1 = true <-> b2 = true) -> b1 = b2.
Proof. hammer_hook "Bool" "Bool.eq_true_iff_eq". Restart. 
apply eq_iff_eq_true.
Qed.

Notation bool_1 := eq_true_iff_eq (only parsing).

Lemma eq_true_negb_classical : forall b:bool, negb b <> true -> b = true.
Proof. hammer_hook "Bool" "Bool.eq_true_negb_classical". Restart. 
destr_bool; intuition.
Qed.

Notation bool_3 := eq_true_negb_classical (only parsing).

Lemma eq_true_not_negb : forall b:bool, b <> true -> negb b = true.
Proof. hammer_hook "Bool" "Bool.eq_true_not_negb". Restart. 
destr_bool; intuition.
Qed.

Notation bool_6 := eq_true_not_negb (only parsing).

Hint Resolve eq_true_not_negb : bool.



Lemma absurd_eq_bool : forall b b':bool, False -> b = b'.
Proof. hammer_hook "Bool" "Bool.absurd_eq_bool". Restart. 
contradiction.
Qed.



Lemma absurd_eq_true : forall b, False -> b = true.
Proof. hammer_hook "Bool" "Bool.absurd_eq_true". Restart. 
contradiction.
Qed.
Hint Resolve absurd_eq_true.



Lemma trans_eq_bool : forall x y z:bool, x = y -> y = z -> x = z.
Proof. hammer_hook "Bool" "Bool.trans_eq_bool". Restart. 
apply eq_trans.
Qed.
Hint Resolve trans_eq_bool.







Hint Unfold Is_true: bool.

Lemma Is_true_eq_true : forall x:bool, Is_true x -> x = true.
Proof. hammer_hook "Bool" "Bool.Is_true_eq_true". Restart. 
destr_bool; tauto.
Qed.

Lemma Is_true_eq_left : forall x:bool, x = true -> Is_true x.
Proof. hammer_hook "Bool" "Bool.Is_true_eq_left". Restart. 
intros; subst; auto with bool.
Qed.

Lemma Is_true_eq_right : forall x:bool, true = x -> Is_true x.
Proof. hammer_hook "Bool" "Bool.Is_true_eq_right". Restart. 
intros; subst; auto with bool.
Qed.

Notation Is_true_eq_true2 := Is_true_eq_right (only parsing).

Hint Immediate Is_true_eq_right Is_true_eq_left: bool.

Lemma eqb_refl : forall x:bool, Is_true (eqb x x).
Proof. hammer_hook "Bool" "Bool.eqb_refl". Restart. 
destr_bool.
Qed.

Lemma eqb_eq : forall x y:bool, Is_true (eqb x y) -> x = y.
Proof. hammer_hook "Bool" "Bool.eqb_eq". Restart. 
destr_bool; tauto.
Qed.



Lemma orb_prop_elim :
forall a b:bool, Is_true (a || b) -> Is_true a \/ Is_true b.
Proof. hammer_hook "Bool" "Bool.orb_prop_elim". Restart. 
destr_bool; tauto.
Qed.

Notation orb_prop2 := orb_prop_elim (only parsing).

Lemma orb_prop_intro :
forall a b:bool, Is_true a \/ Is_true b -> Is_true (a || b).
Proof. hammer_hook "Bool" "Bool.orb_prop_intro". Restart. 
destr_bool; tauto.
Qed.

Lemma andb_prop_intro :
forall b1 b2:bool, Is_true b1 /\ Is_true b2 -> Is_true (b1 && b2).
Proof. hammer_hook "Bool" "Bool.andb_prop_intro". Restart. 
destr_bool; tauto.
Qed.
Hint Resolve andb_prop_intro: bool.

Notation andb_true_intro2 :=
(fun b1 b2 H1 H2 => andb_prop_intro b1 b2 (conj H1 H2))
(only parsing).

Lemma andb_prop_elim :
forall a b:bool, Is_true (a && b) -> Is_true a /\ Is_true b.
Proof. hammer_hook "Bool" "Bool.andb_prop_elim". Restart. 
destr_bool; auto.
Qed.
Hint Resolve andb_prop_elim: bool.

Notation andb_prop2 := andb_prop_elim (only parsing).

Lemma eq_bool_prop_intro :
forall b1 b2, (Is_true b1 <-> Is_true b2) -> b1 = b2.
Proof. hammer_hook "Bool" "Bool.eq_bool_prop_intro". Restart. 
destr_bool; tauto.
Qed.

Lemma eq_bool_prop_elim : forall b1 b2, b1 = b2 -> (Is_true b1 <-> Is_true b2).
Proof. hammer_hook "Bool" "Bool.eq_bool_prop_elim". Restart. 
destr_bool; tauto.
Qed.

Lemma negb_prop_elim : forall b, Is_true (negb b) -> ~ Is_true b.
Proof. hammer_hook "Bool" "Bool.negb_prop_elim". Restart. 
destr_bool; tauto.
Qed.

Lemma negb_prop_intro : forall b, ~ Is_true b -> Is_true (negb b).
Proof. hammer_hook "Bool" "Bool.negb_prop_intro". Restart. 
destr_bool; tauto.
Qed.

Lemma negb_prop_classical : forall b, ~ Is_true (negb b) -> Is_true b.
Proof. hammer_hook "Bool" "Bool.negb_prop_classical". Restart. 
destr_bool; tauto.
Qed.

Lemma negb_prop_involutive : forall b, Is_true b -> ~ Is_true (negb b).
Proof. hammer_hook "Bool" "Bool.negb_prop_involutive". Restart. 
destr_bool; tauto.
Qed.



Lemma andb_if : forall (A:Type)(a a':A)(b b' : bool),
(if b && b' then a else a') =
(if b then if b' then a else a' else a').
Proof. hammer_hook "Bool" "Bool.andb_if". Restart. 
destr_bool.
Qed.

Lemma negb_if : forall (A:Type)(a a':A)(b:bool),
(if negb b then a else a') =
(if b then a' else a).
Proof. hammer_hook "Bool" "Bool.negb_if". Restart. 
destr_bool.
Qed.





Notation "a &&& b" := (if a then b else false)
(at level 40, left associativity) : lazy_bool_scope.
Notation "a ||| b" := (if a then true else b)
(at level 50, left associativity) : lazy_bool_scope.

Local Open Scope lazy_bool_scope.

Lemma andb_lazy_alt : forall a b : bool, a && b = a &&& b.
Proof. hammer_hook "Bool" "Bool.andb_lazy_alt". Restart. 
reflexivity.
Qed.

Lemma orb_lazy_alt : forall a b : bool, a || b = a ||| b.
Proof. hammer_hook "Bool" "Bool.orb_lazy_alt". Restart. 
reflexivity.
Qed.





Inductive reflect (P : Prop) : bool -> Set :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.
Hint Constructors reflect : bool.





Lemma reflect_iff : forall P b, reflect P b -> (P<->b=true).
Proof. hammer_hook "Bool" "Bool.reflect_iff". Restart. 
destruct 1; intuition; discriminate.
Qed.

Lemma iff_reflect : forall P b, (P<->b=true) -> reflect P b.
Proof. hammer_hook "Bool" "Bool.iff_reflect". Restart. 
destr_bool; intuition.
Defined.





Lemma reflect_dec : forall P b, reflect P b -> {P}+{~P}.
Proof. hammer_hook "Bool" "Bool.reflect_dec". Restart. 
destruct 1; auto.
Defined.


