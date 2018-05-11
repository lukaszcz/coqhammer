From Hammer Require Import Hammer.









Require Import ZArithRing.
Require Import ZArith_base.
Require Export Omega.
Require Import Wf_nat.
Local Open Scope Z_scope.





Notation two_or_two_plus_one := Z_modulo_2 (only parsing).




Fixpoint floor_pos (a:positive) : positive :=
match a with
| xH => 1%positive
| xO a' => xO (floor_pos a')
| xI b' => xO (floor_pos b')
end.

Definition floor (a:positive) := Zpos (floor_pos a).

Lemma floor_gt0 : forall p:positive, floor p > 0.
Proof. try hammer_hook "Zcomplements" "Zcomplements.floor_gt0".   reflexivity. Qed.

Lemma floor_ok : forall p:positive, floor p <= Zpos p < 2 * floor p.
Proof. try hammer_hook "Zcomplements" "Zcomplements.floor_ok".  
unfold floor. induction p; simpl.
- rewrite !Pos2Z.inj_xI, (Pos2Z.inj_xO (xO _)), Pos2Z.inj_xO. omega.
- rewrite (Pos2Z.inj_xO (xO _)), (Pos2Z.inj_xO p), Pos2Z.inj_xO. omega.
- omega.
Qed.




Theorem Z_lt_abs_rec :
forall P:Z -> Set,
(forall n:Z, (forall m:Z, Z.abs m < Z.abs n -> P m) -> P n) ->
forall n:Z, P n.
Proof. try hammer_hook "Zcomplements" "Zcomplements.Z_lt_abs_rec".  
intros P HP p.
set (Q := fun z => 0 <= z -> P z * P (- z)).
enough (H:Q (Z.abs p)) by
(destruct (Zabs_dec p) as [-> | ->]; elim H; auto with zarith).
apply (Z_lt_rec Q); auto with zarith.
subst Q; intros x H.
split; apply HP.
- rewrite Z.abs_eq; auto; intros.
destruct (H (Z.abs m)); auto with zarith.
destruct (Zabs_dec m) as [-> | ->]; trivial.
- rewrite Z.abs_neq, Z.opp_involutive; auto with zarith; intros.
destruct (H (Z.abs m)); auto with zarith.
destruct (Zabs_dec m) as [-> | ->]; trivial.
Qed.

Theorem Z_lt_abs_induction :
forall P:Z -> Prop,
(forall n:Z, (forall m:Z, Z.abs m < Z.abs n -> P m) -> P n) ->
forall n:Z, P n.
Proof. try hammer_hook "Zcomplements" "Zcomplements.Z_lt_abs_induction".  
intros P HP p.
set (Q := fun z => 0 <= z -> P z /\ P (- z)) in *.
enough (Q (Z.abs p)) by
(destruct (Zabs_dec p) as [-> | ->]; elim H; auto with zarith).
apply (Z_lt_induction Q); auto with zarith.
subst Q; intros.
split; apply HP.
- rewrite Z.abs_eq; auto; intros.
elim (H (Z.abs m)); intros; auto with zarith.
elim (Zabs_dec m); intro eq; rewrite eq; trivial.
- rewrite Z.abs_neq, Z.opp_involutive; auto with zarith; intros.
destruct (H (Z.abs m)); auto with zarith.
destruct (Zabs_dec m) as [-> | ->]; trivial.
Qed.



Lemma Zcase_sign :
forall (n:Z) (P:Prop), (n = 0 -> P) -> (n > 0 -> P) -> (n < 0 -> P) -> P.
Proof. try hammer_hook "Zcomplements" "Zcomplements.Zcase_sign".  
intros x P Hzero Hpos Hneg.
destruct x; [apply Hzero|apply Hpos|apply Hneg]; easy.
Qed.

Lemma sqr_pos n : n * n >= 0.
Proof. try hammer_hook "Zcomplements" "Zcomplements.sqr_pos".  
Z.swap_greater. apply Z.square_nonneg.
Qed.




Require Import List.

Fixpoint Zlength_aux (acc:Z) (A:Type) (l:list A) : Z :=
match l with
| nil => acc
| _ :: l => Zlength_aux (Z.succ acc) A l
end.

Definition Zlength := Zlength_aux 0.
Arguments Zlength [A] l.

Section Zlength_properties.

Variable A : Type.

Implicit Type l : list A.

Lemma Zlength_correct l : Zlength l = Z.of_nat (length l).
Proof. try hammer_hook "Zcomplements" "Zcomplements.Zlength_correct".  
assert (H : forall l acc, Zlength_aux acc A l = acc + Z.of_nat (length l)).
clear l. induction l.
auto with zarith.
intros. simpl length; simpl Zlength_aux.
rewrite IHl, Nat2Z.inj_succ; auto with zarith.
unfold Zlength. now rewrite H.
Qed.

Lemma Zlength_nil : Zlength (A:=A) nil = 0.
Proof. try hammer_hook "Zcomplements" "Zcomplements.Zlength_nil".   reflexivity. Qed.

Lemma Zlength_cons (x:A) l : Zlength (x :: l) = Z.succ (Zlength l).
Proof. try hammer_hook "Zcomplements" "Zcomplements.Zlength_cons".  
intros. now rewrite !Zlength_correct, <- Nat2Z.inj_succ.
Qed.

Lemma Zlength_nil_inv l : Zlength l = 0 -> l = nil.
Proof. try hammer_hook "Zcomplements" "Zcomplements.Zlength_nil_inv".  
rewrite Zlength_correct.
destruct l as [|x l]; auto.
now rewrite <- Nat2Z.inj_0, Nat2Z.inj_iff.
Qed.

End Zlength_properties.

Arguments Zlength_correct [A] l.
Arguments Zlength_cons [A] x l.
Arguments Zlength_nil_inv [A] l _.
