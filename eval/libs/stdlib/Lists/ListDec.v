From Hammer Require Import Hammer.











Require Import List Decidable.
Set Implicit Arguments.

Definition decidable_eq A := forall x y:A, decidable (x=y).

Section Dec_in_Prop.
Variables (A:Type)(dec:decidable_eq A).

Lemma In_decidable x (l:list A) : decidable (In x l).
Proof using A dec. try hammer_hook "ListDec" "ListDec.In_decidable".  
induction l as [|a l IH].
- now right.
- destruct (dec a x).
+ left. now left.
+ destruct IH; simpl; [left|right]; tauto.
Qed.

Lemma incl_decidable (l l':list A) : decidable (incl l l').
Proof using A dec. try hammer_hook "ListDec" "ListDec.incl_decidable".  
induction l as [|a l IH].
- left. inversion 1.
- destruct (In_decidable a l') as [IN|IN].
+ destruct IH as [IC|IC].
* left. destruct 1; subst; auto.
* right. contradict IC. intros x H. apply IC; now right.
+ right. contradict IN. apply IN; now left.
Qed.

Lemma NoDup_decidable (l:list A) : decidable (NoDup l).
Proof using A dec. try hammer_hook "ListDec" "ListDec.NoDup_decidable".  
induction l as [|a l IH].
- left; now constructor.
- destruct (In_decidable a l).
+ right. inversion_clear 1. tauto.
+ destruct IH.
* left. now constructor.
* right. inversion_clear 1. tauto.
Qed.

End Dec_in_Prop.

Section Dec_in_Type.
Variables (A:Type)(dec : forall x y:A, {x=y}+{x<>y}).

Definition In_dec := List.In_dec dec.

Lemma incl_dec (l l':list A) : {incl l l'}+{~incl l l'}.
Proof using A dec. try hammer_hook "ListDec" "ListDec.incl_dec".  
induction l as [|a l IH].
- left. inversion 1.
- destruct (In_dec a l') as [IN|IN].
+ destruct IH as [IC|IC].
* left. destruct 1; subst; auto.
* right. contradict IC. intros x H. apply IC; now right.
+ right. contradict IN. apply IN; now left.
Qed.

Lemma NoDup_dec (l:list A) : {NoDup l}+{~NoDup l}.
Proof using A dec. try hammer_hook "ListDec" "ListDec.NoDup_dec".  
induction l as [|a l IH].
- left; now constructor.
- destruct (In_dec a l).
+ right. inversion_clear 1. tauto.
+ destruct IH.
* left. now constructor.
* right. inversion_clear 1. tauto.
Qed.

End Dec_in_Type.



Lemma uniquify_map A B (d:decidable_eq B)(f:A->B)(l:list A) :
exists l', NoDup (map f l') /\ incl (map f l) (map f l').
Proof. try hammer_hook "ListDec" "ListDec.uniquify_map".  
induction l.
- exists nil. simpl. split; [now constructor | red; trivial].
- destruct IHl as (l' & N & I).
destruct (In_decidable d (f a) (map f l')).
+ exists l'; simpl; split; trivial.
intros x [Hx|Hx]. now subst. now apply I.
+ exists (a::l'); simpl; split.
* now constructor.
* intros x [Hx|Hx]. subst; now left. right; now apply I.
Qed.

Lemma uniquify A (d:decidable_eq A)(l:list A) :
exists l', NoDup l' /\ incl l l'.
Proof. try hammer_hook "ListDec" "ListDec.uniquify".  
destruct (uniquify_map d id l) as (l',H).
exists l'. now rewrite !map_id in H.
Qed.
