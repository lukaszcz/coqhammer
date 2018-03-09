From Hammer Require Import Hammer.









Require Import ZAxioms ZMulOrder GenericMinMax.



Module Type ZMaxMinProp (Import Z : ZAxiomsMiniSig').
Include ZMulOrderProp Z.





Lemma succ_max_distr : forall n m, S (max n m) == max (S n) (S m).
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.succ_max_distr". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?succ_le_mono.
Qed.

Lemma succ_min_distr : forall n m, S (min n m) == min (S n) (S m).
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.succ_min_distr". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?succ_le_mono.
Qed.



Lemma pred_max_distr : forall n m, P (max n m) == max (P n) (P m).
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.pred_max_distr". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?pred_le_mono.
Qed.

Lemma pred_min_distr : forall n m, P (min n m) == min (P n) (P m).
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.pred_min_distr". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?pred_le_mono.
Qed.



Lemma add_max_distr_l : forall n m p, max (p + n) (p + m) == p + max n m.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.add_max_distr_l". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?add_le_mono_l.
Qed.

Lemma add_max_distr_r : forall n m p, max (n + p) (m + p) == max n m + p.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.add_max_distr_r". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?add_le_mono_r.
Qed.

Lemma add_min_distr_l : forall n m p, min (p + n) (p + m) == p + min n m.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.add_min_distr_l". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?add_le_mono_l.
Qed.

Lemma add_min_distr_r : forall n m p, min (n + p) (m + p) == min n m + p.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.add_min_distr_r". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?add_le_mono_r.
Qed.



Lemma opp_max_distr : forall n m, -(max n m) == min (-n) (-m).
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.opp_max_distr". Restart. 
intros. destruct (le_ge_cases n m).
rewrite max_r by trivial. symmetry. apply min_r. now rewrite <- opp_le_mono.
rewrite max_l by trivial. symmetry. apply min_l. now rewrite <- opp_le_mono.
Qed.

Lemma opp_min_distr : forall n m, -(min n m) == max (-n) (-m).
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.opp_min_distr". Restart. 
intros. destruct (le_ge_cases n m).
rewrite min_l by trivial. symmetry. apply max_l. now rewrite <- opp_le_mono.
rewrite min_r by trivial. symmetry. apply max_r. now rewrite <- opp_le_mono.
Qed.



Lemma sub_max_distr_l : forall n m p, max (p - n) (p - m) == p - min n m.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.sub_max_distr_l". Restart. 
intros. destruct (le_ge_cases n m).
rewrite min_l by trivial. apply max_l. now rewrite <- sub_le_mono_l.
rewrite min_r by trivial. apply max_r. now rewrite <- sub_le_mono_l.
Qed.

Lemma sub_max_distr_r : forall n m p, max (n - p) (m - p) == max n m - p.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.sub_max_distr_r". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; try order; now apply sub_le_mono_r.
Qed.

Lemma sub_min_distr_l : forall n m p, min (p - n) (p - m) == p - max n m.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.sub_min_distr_l". Restart. 
intros. destruct (le_ge_cases n m).
rewrite max_r by trivial. apply min_r. now rewrite <- sub_le_mono_l.
rewrite max_l by trivial. apply min_l. now rewrite <- sub_le_mono_l.
Qed.

Lemma sub_min_distr_r : forall n m p, min (n - p) (m - p) == min n m - p.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.sub_min_distr_r". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; try order; now apply sub_le_mono_r.
Qed.



Lemma mul_max_distr_nonneg_l : forall n m p, 0 <= p ->
max (p * n) (p * m) == p * max n m.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.mul_max_distr_nonneg_l". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; try order; now apply mul_le_mono_nonneg_l.
Qed.

Lemma mul_max_distr_nonneg_r : forall n m p, 0 <= p ->
max (n * p) (m * p) == max n m * p.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.mul_max_distr_nonneg_r". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; try order; now apply mul_le_mono_nonneg_r.
Qed.

Lemma mul_min_distr_nonneg_l : forall n m p, 0 <= p ->
min (p * n) (p * m) == p * min n m.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.mul_min_distr_nonneg_l". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; try order; now apply mul_le_mono_nonneg_l.
Qed.

Lemma mul_min_distr_nonneg_r : forall n m p, 0 <= p ->
min (n * p) (m * p) == min n m * p.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.mul_min_distr_nonneg_r". Restart. 
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; try order; now apply mul_le_mono_nonneg_r.
Qed.

Lemma mul_max_distr_nonpos_l : forall n m p, p <= 0 ->
max (p * n) (p * m) == p * min n m.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.mul_max_distr_nonpos_l". Restart. 
intros. destruct (le_ge_cases n m).
rewrite min_l by trivial. rewrite max_l. reflexivity. now apply mul_le_mono_nonpos_l.
rewrite min_r by trivial. rewrite max_r. reflexivity. now apply mul_le_mono_nonpos_l.
Qed.

Lemma mul_max_distr_nonpos_r : forall n m p, p <= 0 ->
max (n * p) (m * p) == min n m * p.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.mul_max_distr_nonpos_r". Restart. 
intros. destruct (le_ge_cases n m).
rewrite min_l by trivial. rewrite max_l. reflexivity. now apply mul_le_mono_nonpos_r.
rewrite min_r by trivial. rewrite max_r. reflexivity. now apply mul_le_mono_nonpos_r.
Qed.

Lemma mul_min_distr_nonpos_l : forall n m p, p <= 0 ->
min (p * n) (p * m) == p * max n m.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.mul_min_distr_nonpos_l". Restart. 
intros. destruct (le_ge_cases n m).
rewrite max_r by trivial. rewrite min_r. reflexivity. now apply mul_le_mono_nonpos_l.
rewrite max_l by trivial. rewrite min_l. reflexivity. now apply mul_le_mono_nonpos_l.
Qed.

Lemma mul_min_distr_nonpos_r : forall n m p, p <= 0 ->
min (n * p) (m * p) == max n m * p.
Proof. hammer_hook "ZMaxMin" "ZMaxMin.ZMaxMinProp.mul_min_distr_nonpos_r". Restart. 
intros. destruct (le_ge_cases n m).
rewrite max_r by trivial. rewrite min_r. reflexivity. now apply mul_le_mono_nonpos_r.
rewrite max_l by trivial. rewrite min_l. reflexivity. now apply mul_le_mono_nonpos_r.
Qed.

End ZMaxMinProp.
