From Hammer Require Import Hammer.











Require Import List.
Import ListNotations.



Inductive inductively_barred P : list bool -> Prop :=
| now l : P l -> inductively_barred P l
| propagate l :
inductively_barred P (true::l) ->
inductively_barred P (false::l) ->
inductively_barred P l.



Fixpoint approx X (l:list bool) :=
match l with
| [] => True
| b::l => approx X l /\ (if b then X (length l) else ~ X (length l))
end.



Definition barred P :=
forall (X:nat -> Prop), exists l, approx X l /\ P l.



Fixpoint Y P (l:list bool) :=
match l with
| [] => True
| b::l =>
Y P l /\
if b then inductively_barred P (false::l) else ~ inductively_barred P (false::l)
end.

Lemma Y_unique : forall P l1 l2, length l1 = length l2 -> Y P l1 -> Y P l2 -> l1 = l2.
Proof. try hammer_hook "WeakFan" "WeakFan.Y_unique".  
induction l1, l2.
- trivial.
- discriminate.
- discriminate.
- intros H (HY1,H1) (HY2,H2).
injection H as H.
pose proof (IHl1 l2 H HY1 HY2). clear HY1 HY2 H IHl1.
subst l1.
f_equal.
destruct a, b; firstorder.
Qed.



Definition X P n := exists l, length l = n /\ Y P (true::l).

Lemma Y_approx : forall P l, approx (X P) l -> Y P l.
Proof. try hammer_hook "WeakFan" "WeakFan.Y_approx".  
induction l.
- trivial.
- intros (H,Hb). split.
+ auto.
+ unfold X in Hb.
destruct a.
* destruct Hb as (l',(Hl',(HYl',HY))).
rewrite <- (Y_unique P l' l Hl'); auto.
* firstorder.
Qed.

Theorem WeakFanTheorem : forall P, barred P -> inductively_barred P [].
Proof. try hammer_hook "WeakFan" "WeakFan.WeakFanTheorem".  
intros P Hbar.
destruct Hbar with (X P) as (l,(Hd%Y_approx,HP)).
assert (inductively_barred P l) by (apply (now P l), HP).
clear Hbar HP.
induction l as [|a l].
- assumption.
- destruct Hd as (Hd,HX).
apply (IHl Hd). clear IHl.
destruct a; unfold X in HX; simpl in HX.
+ apply propagate; assumption.
+ exfalso; destruct (HX H).
Qed.
