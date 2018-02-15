From Hammer Require Import Hammer.









Require Import Bool.
Require Import Sumbool.
Require Import Arith.
Require Import BinPos.
Require Import BinNat.
Require Import Pnat.
Require Import Nnat.
Require Import Ndigits.

Local Open Scope N_scope.



Notation Peqb := Pos.eqb (compat "8.3").
Notation Neqb := N.eqb (compat "8.3").
Notation Peqb_correct := Pos.eqb_refl (compat "8.3").
Notation Neqb_correct := N.eqb_refl (compat "8.3").
Notation Neqb_comm := N.eqb_sym (compat "8.3").

Lemma Peqb_complete p p' : Pos.eqb p p' = true -> p = p'.
Proof. hammer_hook "Ndec" "Ndec.Peqb_complete". Restart.  now apply Pos.eqb_eq. Qed.

Lemma Peqb_Pcompare p p' : Pos.eqb p p' = true -> Pos.compare p p' = Eq.
Proof. hammer_hook "Ndec" "Ndec.Peqb_Pcompare". Restart.  now rewrite Pos.compare_eq_iff, <- Pos.eqb_eq. Qed.

Lemma Pcompare_Peqb p p' : Pos.compare p p' = Eq -> Pos.eqb p p' = true.
Proof. hammer_hook "Ndec" "Ndec.Pcompare_Peqb". Restart.  now rewrite Pos.eqb_eq, <- Pos.compare_eq_iff. Qed.

Lemma Neqb_Ncompare n n' : N.eqb n n' = true -> N.compare n n' = Eq.
Proof. hammer_hook "Ndec" "Ndec.Neqb_Ncompare". Restart.  now rewrite N.compare_eq_iff, <- N.eqb_eq. Qed.

Lemma Ncompare_Neqb n n' : N.compare n n' = Eq -> N.eqb n n' = true.
Proof. hammer_hook "Ndec" "Ndec.Ncompare_Neqb". Restart.  now rewrite N.eqb_eq, <- N.compare_eq_iff. Qed.

Lemma Neqb_complete n n' : N.eqb n n' = true -> n = n'.
Proof. hammer_hook "Ndec" "Ndec.Neqb_complete". Restart.  now apply N.eqb_eq. Qed.

Lemma Nxor_eq_true n n' : N.lxor n n' = 0 -> N.eqb n n' = true.
Proof. hammer_hook "Ndec" "Ndec.Nxor_eq_true". Restart. 
intro H. apply N.lxor_eq in H. subst. apply N.eqb_refl.
Qed.

Ltac eqb2eq := rewrite <- ?not_true_iff_false in *; rewrite ?N.eqb_eq in *.

Lemma Nxor_eq_false n n' p :
N.lxor n n' = N.pos p -> N.eqb n n' = false.
Proof. hammer_hook "Ndec" "Ndec.Nxor_eq_false". Restart. 
intros. eqb2eq. intro. subst. now rewrite N.lxor_nilpotent in *.
Qed.

Lemma Nodd_not_double a :
Nodd a -> forall a0, N.eqb (N.double a0) a = false.
Proof. hammer_hook "Ndec" "Ndec.Nodd_not_double". Restart. 
intros. eqb2eq. intros <-.
unfold Nodd in *. now rewrite Ndouble_bit0 in *.
Qed.

Lemma Nnot_div2_not_double a a0 :
N.eqb (N.div2 a) a0 = false -> N.eqb a (N.double a0) = false.
Proof. hammer_hook "Ndec" "Ndec.Nnot_div2_not_double". Restart. 
intros H. eqb2eq. contradict H. subst. apply N.div2_double.
Qed.

Lemma Neven_not_double_plus_one a :
Neven a -> forall a0, N.eqb (N.succ_double a0) a = false.
Proof. hammer_hook "Ndec" "Ndec.Neven_not_double_plus_one". Restart. 
intros. eqb2eq. intros <-.
unfold Neven in *. now rewrite Ndouble_plus_one_bit0 in *.
Qed.

Lemma Nnot_div2_not_double_plus_one a a0 :
N.eqb (N.div2 a) a0 = false -> N.eqb (N.succ_double a0) a = false.
Proof. hammer_hook "Ndec" "Ndec.Nnot_div2_not_double_plus_one". Restart. 
intros H. eqb2eq. contradict H. subst. apply N.div2_succ_double.
Qed.

Lemma Nbit0_neq a a' :
N.odd a = false -> N.odd a' = true -> N.eqb a a' = false.
Proof. hammer_hook "Ndec" "Ndec.Nbit0_neq". Restart. 
intros. eqb2eq. now intros <-.
Qed.

Lemma Ndiv2_eq a a' :
N.eqb a a' = true -> N.eqb (N.div2 a) (N.div2 a') = true.
Proof. hammer_hook "Ndec" "Ndec.Ndiv2_eq". Restart. 
intros. eqb2eq. now subst.
Qed.

Lemma Ndiv2_neq a a' :
N.eqb (N.div2 a) (N.div2 a') = false -> N.eqb a a' = false.
Proof. hammer_hook "Ndec" "Ndec.Ndiv2_neq". Restart. 
intros H. eqb2eq. contradict H. now subst.
Qed.

Lemma Ndiv2_bit_eq a a' :
N.odd a = N.odd a' -> N.div2 a = N.div2 a' -> a = a'.
Proof. hammer_hook "Ndec" "Ndec.Ndiv2_bit_eq". Restart. 
intros H H'; now rewrite (N.div2_odd a), (N.div2_odd a'), H, H'.
Qed.

Lemma Ndiv2_bit_neq a a' :
N.eqb a a' = false ->
N.odd a = N.odd a' -> N.eqb (N.div2 a) (N.div2 a') = false.
Proof. hammer_hook "Ndec" "Ndec.Ndiv2_bit_neq". Restart. 
intros H H'. eqb2eq. contradict H. now apply Ndiv2_bit_eq.
Qed.

Lemma Nneq_elim a a' :
N.eqb a a' = false ->
N.odd a = negb (N.odd a') \/
N.eqb (N.div2 a) (N.div2 a') = false.
Proof. hammer_hook "Ndec" "Ndec.Nneq_elim". Restart. 
intros.
enough (N.odd a = N.odd a' \/ N.odd a = negb (N.odd a')) as [].
- right. apply Ndiv2_bit_neq; assumption.
- left. assumption.
- case (N.odd a), (N.odd a'); auto.
Qed.

Lemma Ndouble_or_double_plus_un a :
{a0 : N | a = N.double a0} + {a1 : N | a = N.succ_double a1}.
Proof. hammer_hook "Ndec" "Ndec.Ndouble_or_double_plus_un". Restart. 
elim (sumbool_of_bool (N.odd a)); intros H; [right|left];
exists (N.div2 a); symmetry;
apply Ndiv2_double_plus_one || apply Ndiv2_double; auto.
Qed.



Definition Nleb (a b:N) := leb (N.to_nat a) (N.to_nat b).

Lemma Nleb_alt a b : Nleb a b = N.leb a b.
Proof. hammer_hook "Ndec" "Ndec.Nleb_alt". Restart. 
unfold Nleb.
now rewrite eq_iff_eq_true, N.leb_le, leb_compare, <- N2Nat.inj_compare.
Qed.

Lemma Nleb_Nle a b : Nleb a b = true <-> a <= b.
Proof. hammer_hook "Ndec" "Ndec.Nleb_Nle". Restart.  now rewrite Nleb_alt, N.leb_le. Qed.

Lemma Nleb_refl a : Nleb a a = true.
Proof. hammer_hook "Ndec" "Ndec.Nleb_refl". Restart.  rewrite Nleb_Nle; apply N.le_refl. Qed.

Lemma Nleb_antisym a b : Nleb a b = true -> Nleb b a = true -> a = b.
Proof. hammer_hook "Ndec" "Ndec.Nleb_antisym". Restart.  rewrite !Nleb_Nle. apply N.le_antisymm. Qed.

Lemma Nleb_trans a b c : Nleb a b = true -> Nleb b c = true -> Nleb a c = true.
Proof. hammer_hook "Ndec" "Ndec.Nleb_trans". Restart.  rewrite !Nleb_Nle. apply N.le_trans. Qed.

Lemma Nleb_ltb_trans a b c :
Nleb a b = true -> Nleb c b = false -> Nleb c a = false.
Proof. hammer_hook "Ndec" "Ndec.Nleb_ltb_trans". Restart. 
unfold Nleb. intros. apply leb_correct_conv.
apply le_lt_trans with (m := N.to_nat b).
apply leb_complete. assumption.
apply leb_complete_conv. assumption.
Qed.

Lemma Nltb_leb_trans a b c :
Nleb b a = false -> Nleb b c = true -> Nleb c a = false.
Proof. hammer_hook "Ndec" "Ndec.Nltb_leb_trans". Restart. 
unfold Nleb. intros. apply leb_correct_conv.
apply lt_le_trans with (m := N.to_nat b).
apply leb_complete_conv. assumption.
apply leb_complete. assumption.
Qed.

Lemma Nltb_trans a b c :
Nleb b a = false -> Nleb c b = false -> Nleb c a = false.
Proof. hammer_hook "Ndec" "Ndec.Nltb_trans". Restart. 
unfold Nleb. intros. apply leb_correct_conv.
apply lt_trans with (m := N.to_nat b).
apply leb_complete_conv. assumption.
apply leb_complete_conv. assumption.
Qed.

Lemma Nltb_leb_weak a b : Nleb b a = false -> Nleb a b = true.
Proof. hammer_hook "Ndec" "Ndec.Nltb_leb_weak". Restart. 
unfold Nleb. intros. apply leb_correct. apply lt_le_weak.
apply leb_complete_conv. assumption.
Qed.

Lemma Nleb_double_mono a b :
Nleb a b = true -> Nleb (N.double a) (N.double b) = true.
Proof. hammer_hook "Ndec" "Ndec.Nleb_double_mono". Restart. 
unfold Nleb. intros. rewrite !N2Nat.inj_double. apply leb_correct.
apply mult_le_compat_l. now apply leb_complete.
Qed.

Lemma Nleb_double_plus_one_mono a b :
Nleb a b = true ->
Nleb (N.succ_double a) (N.succ_double b) = true.
Proof. hammer_hook "Ndec" "Ndec.Nleb_double_plus_one_mono". Restart. 
unfold Nleb. intros. rewrite !N2Nat.inj_succ_double. apply leb_correct.
apply le_n_S, mult_le_compat_l. now apply leb_complete.
Qed.

Lemma Nleb_double_mono_conv a b :
Nleb (N.double a) (N.double b) = true -> Nleb a b = true.
Proof. hammer_hook "Ndec" "Ndec.Nleb_double_mono_conv". Restart. 
unfold Nleb. rewrite !N2Nat.inj_double. intro. apply leb_correct.
apply (mult_S_le_reg_l 1). now apply leb_complete.
Qed.

Lemma Nleb_double_plus_one_mono_conv a b :
Nleb (N.succ_double a) (N.succ_double b) = true ->
Nleb a b = true.
Proof. hammer_hook "Ndec" "Ndec.Nleb_double_plus_one_mono_conv". Restart. 
unfold Nleb. rewrite !N2Nat.inj_succ_double. intro. apply leb_correct.
apply (mult_S_le_reg_l 1). apply le_S_n. now apply leb_complete.
Qed.

Lemma Nltb_double_mono a b :
Nleb a b = false -> Nleb (N.double a) (N.double b) = false.
Proof. hammer_hook "Ndec" "Ndec.Nltb_double_mono". Restart. 
intros. elim (sumbool_of_bool (Nleb (N.double a) (N.double b))). intro H0.
rewrite (Nleb_double_mono_conv _ _ H0) in H. discriminate H.
trivial.
Qed.

Lemma Nltb_double_plus_one_mono a b :
Nleb a b = false ->
Nleb (N.succ_double a) (N.succ_double b) = false.
Proof. hammer_hook "Ndec" "Ndec.Nltb_double_plus_one_mono". Restart. 
intros. elim (sumbool_of_bool (Nleb (N.succ_double a) (N.succ_double b))).
intro H0.
rewrite (Nleb_double_plus_one_mono_conv _ _ H0) in H. discriminate H.
trivial.
Qed.

Lemma Nltb_double_mono_conv a b :
Nleb (N.double a) (N.double b) = false -> Nleb a b = false.
Proof. hammer_hook "Ndec" "Ndec.Nltb_double_mono_conv". Restart. 
intros. elim (sumbool_of_bool (Nleb a b)). intro H0.
rewrite (Nleb_double_mono _ _ H0) in H. discriminate H.
trivial.
Qed.

Lemma Nltb_double_plus_one_mono_conv a b :
Nleb (N.succ_double a) (N.succ_double b) = false ->
Nleb a b = false.
Proof. hammer_hook "Ndec" "Ndec.Nltb_double_plus_one_mono_conv". Restart. 
intros. elim (sumbool_of_bool (Nleb a b)). intro H0.
rewrite (Nleb_double_plus_one_mono _ _ H0) in H. discriminate H.
trivial.
Qed.





Lemma Nltb_Ncompare a b : Nleb a b = false <-> N.compare a b = Gt.
Proof. hammer_hook "Ndec" "Ndec.Nltb_Ncompare". Restart. 
now rewrite N.compare_nle_iff, <- Nleb_Nle, not_true_iff_false.
Qed.

Lemma Ncompare_Gt_Nltb a b : N.compare a b = Gt -> Nleb a b = false.
Proof. hammer_hook "Ndec" "Ndec.Ncompare_Gt_Nltb". Restart.  apply <- Nltb_Ncompare; auto. Qed.

Lemma Ncompare_Lt_Nltb a b : N.compare a b = Lt -> Nleb b a = false.
Proof. hammer_hook "Ndec" "Ndec.Ncompare_Lt_Nltb". Restart. 
intros H. rewrite Nltb_Ncompare, N.compare_antisym, H; auto.
Qed.



Notation Nmin_choice := N.min_dec (compat "8.3").

Lemma Nmin_le_1 a b : Nleb (N.min a b) a = true.
Proof. hammer_hook "Ndec" "Ndec.Nmin_le_1". Restart.  rewrite Nleb_Nle. apply N.le_min_l. Qed.

Lemma Nmin_le_2 a b : Nleb (N.min a b) b = true.
Proof. hammer_hook "Ndec" "Ndec.Nmin_le_2". Restart.  rewrite Nleb_Nle. apply N.le_min_r. Qed.

Lemma Nmin_le_3 a b c : Nleb a (N.min b c) = true -> Nleb a b = true.
Proof. hammer_hook "Ndec" "Ndec.Nmin_le_3". Restart.  rewrite !Nleb_Nle. apply N.min_glb_l. Qed.

Lemma Nmin_le_4 a b c : Nleb a (N.min b c) = true -> Nleb a c = true.
Proof. hammer_hook "Ndec" "Ndec.Nmin_le_4". Restart.  rewrite !Nleb_Nle. apply N.min_glb_r. Qed.

Lemma Nmin_le_5 a b c :
Nleb a b = true -> Nleb a c = true -> Nleb a (N.min b c) = true.
Proof. hammer_hook "Ndec" "Ndec.Nmin_le_5". Restart.  rewrite !Nleb_Nle. apply N.min_glb. Qed.

Lemma Nmin_lt_3 a b c : Nleb (N.min b c) a = false -> Nleb b a = false.
Proof. hammer_hook "Ndec" "Ndec.Nmin_lt_3". Restart. 
rewrite <- !not_true_iff_false, !Nleb_Nle.
rewrite N.min_le_iff; auto.
Qed.

Lemma Nmin_lt_4 a b c : Nleb (N.min b c) a = false -> Nleb c a = false.
Proof. hammer_hook "Ndec" "Ndec.Nmin_lt_4". Restart. 
rewrite <- !not_true_iff_false, !Nleb_Nle.
rewrite N.min_le_iff; auto.
Qed.
