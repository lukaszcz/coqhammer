From Hammer Require Import Hammer.









Require Import Orders Rbase Rbasic_fun ROrderedType GenericMinMax.



Local Open Scope R_scope.



Lemma Rmax_l : forall x y, y<=x -> Rmax x y = x.
Proof. hammer_hook "Rminmax" "Rminmax.Rmax_l".  
unfold Rmax. intros.
destruct Rle_dec as [H'|H']; [| apply Rnot_le_lt in H' ];
unfold Rle in *; intuition.
Qed.

Lemma Rmax_r : forall x y, x<=y -> Rmax x y = y.
Proof. hammer_hook "Rminmax" "Rminmax.Rmax_r".  
unfold Rmax. intros.
destruct Rle_dec as [H'|H']; [| apply Rnot_le_lt in H' ];
unfold Rle in *; intuition.
Qed.

Lemma Rmin_l : forall x y, x<=y -> Rmin x y = x.
Proof. hammer_hook "Rminmax" "Rminmax.Rmin_l".  
unfold Rmin. intros.
destruct Rle_dec as [H'|H']; [| apply Rnot_le_lt in H' ];
unfold Rle in *; intuition.
Qed.

Lemma Rmin_r : forall x y, y<=x -> Rmin x y = y.
Proof. hammer_hook "Rminmax" "Rminmax.Rmin_r".  
unfold Rmin. intros.
destruct Rle_dec as [H'|H']; [| apply Rnot_le_lt in H' ];
unfold Rle in *; intuition.
Qed.

Module RHasMinMax <: HasMinMax R_as_OT.
Definition max := Rmax.
Definition min := Rmin.
Definition max_l := Rmax_l.
Definition max_r := Rmax_r.
Definition min_l := Rmin_l.
Definition min_r := Rmin_r.
End RHasMinMax.

Module R.



Include UsualMinMaxProperties R_as_OT RHasMinMax.





Lemma plus_max_distr_l : forall n m p, Rmax (p + n) (p + m) = p + Rmax n m.
Proof. hammer_hook "Rminmax" "Rminmax.R.plus_max_distr_l".  
intros. apply max_monotone.
intros x y. apply Rplus_le_compat_l.
Qed.

Lemma plus_max_distr_r : forall n m p, Rmax (n + p) (m + p) = Rmax n m + p.
Proof. hammer_hook "Rminmax" "Rminmax.R.plus_max_distr_r".  
intros. rewrite (Rplus_comm n p), (Rplus_comm m p), (Rplus_comm _ p).
apply plus_max_distr_l.
Qed.

Lemma plus_min_distr_l : forall n m p, Rmin (p + n) (p + m) = p + Rmin n m.
Proof. hammer_hook "Rminmax" "Rminmax.R.plus_min_distr_l".  
intros. apply min_monotone.
intros x y. apply Rplus_le_compat_l.
Qed.

Lemma plus_min_distr_r : forall n m p, Rmin (n + p) (m + p) = Rmin n m + p.
Proof. hammer_hook "Rminmax" "Rminmax.R.plus_min_distr_r".  
intros. rewrite (Rplus_comm n p), (Rplus_comm m p), (Rplus_comm _ p).
apply plus_min_distr_l.
Qed.



Lemma opp_max_distr : forall n m : R, -(Rmax n m) = Rmin (- n) (- m).
Proof. hammer_hook "Rminmax" "Rminmax.R.opp_max_distr".  
intros. symmetry. apply min_max_antimonotone.
do 3 red. intros; apply Rge_le. apply Ropp_le_ge_contravar; auto.
Qed.

Lemma opp_min_distr : forall n m : R, - (Rmin n m) = Rmax (- n) (- m).
Proof. hammer_hook "Rminmax" "Rminmax.R.opp_min_distr".  
intros. symmetry. apply max_min_antimonotone.
do 3 red. intros; apply Rge_le. apply Ropp_le_ge_contravar; auto.
Qed.

Lemma minus_max_distr_l : forall n m p, Rmax (p - n) (p - m) = p - Rmin n m.
Proof. hammer_hook "Rminmax" "Rminmax.R.minus_max_distr_l".  
unfold Rminus. intros. rewrite opp_min_distr. apply plus_max_distr_l.
Qed.

Lemma minus_max_distr_r : forall n m p, Rmax (n - p) (m - p) = Rmax n m - p.
Proof. hammer_hook "Rminmax" "Rminmax.R.minus_max_distr_r".  
unfold Rminus. intros. apply plus_max_distr_r.
Qed.

Lemma minus_min_distr_l : forall n m p, Rmin (p - n) (p - m) = p - Rmax n m.
Proof. hammer_hook "Rminmax" "Rminmax.R.minus_min_distr_l".  
unfold Rminus. intros. rewrite opp_max_distr. apply plus_min_distr_l.
Qed.

Lemma minus_min_distr_r : forall n m p, Rmin (n - p) (m - p) = Rmin n m - p.
Proof. hammer_hook "Rminmax" "Rminmax.R.minus_min_distr_r".  
unfold Rminus. intros. apply plus_min_distr_r.
Qed.

End R.
