From Hammer Require Import Hammer.









Require Import NAxioms NSub GenericMinMax.



Module Type NMaxMinProp (Import N : NAxiomsMiniSig').
Include NSubProp N.



Lemma max_0_l : forall n, max 0 n == n.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.max_0_l". Undo.  
intros. apply max_r. apply le_0_l.
Qed.

Lemma max_0_r : forall n, max n 0 == n.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.max_0_r". Undo.  
intros. apply max_l. apply le_0_l.
Qed.

Lemma min_0_l : forall n, min 0 n == 0.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.min_0_l". Undo.  
intros. apply min_l. apply le_0_l.
Qed.

Lemma min_0_r : forall n, min n 0 == 0.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.min_0_r". Undo.  
intros. apply min_r. apply le_0_l.
Qed.





Lemma succ_max_distr : forall n m, S (max n m) == max (S n) (S m).
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.succ_max_distr". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?succ_le_mono.
Qed.

Lemma succ_min_distr : forall n m, S (min n m) == min (S n) (S m).
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.succ_min_distr". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?succ_le_mono.
Qed.



Lemma add_max_distr_l : forall n m p, max (p + n) (p + m) == p + max n m.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.add_max_distr_l". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?add_le_mono_l.
Qed.

Lemma add_max_distr_r : forall n m p, max (n + p) (m + p) == max n m + p.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.add_max_distr_r". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; now rewrite <- ?add_le_mono_r.
Qed.

Lemma add_min_distr_l : forall n m p, min (p + n) (p + m) == p + min n m.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.add_min_distr_l". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?add_le_mono_l.
Qed.

Lemma add_min_distr_r : forall n m p, min (n + p) (m + p) == min n m + p.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.add_min_distr_r". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; now rewrite <- ?add_le_mono_r.
Qed.



Lemma mul_max_distr_l : forall n m p, max (p * n) (p * m) == p * max n m.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.mul_max_distr_l". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; try order; now apply mul_le_mono_l.
Qed.

Lemma mul_max_distr_r : forall n m p, max (n * p) (m * p) == max n m * p.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.mul_max_distr_r". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; try order; now apply mul_le_mono_r.
Qed.

Lemma mul_min_distr_l : forall n m p, min (p * n) (p * m) == p * min n m.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.mul_min_distr_l". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; try order; now apply mul_le_mono_l.
Qed.

Lemma mul_min_distr_r : forall n m p, min (n * p) (m * p) == min n m * p.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.mul_min_distr_r". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; try order; now apply mul_le_mono_r.
Qed.



Lemma sub_max_distr_l : forall n m p, max (p - n) (p - m) == p - min n m.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.sub_max_distr_l". Undo.  
intros. destruct (le_ge_cases n m).
rewrite min_l by trivial. apply max_l. now apply sub_le_mono_l.
rewrite min_r by trivial. apply max_r. now apply sub_le_mono_l.
Qed.

Lemma sub_max_distr_r : forall n m p, max (n - p) (m - p) == max n m - p.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.sub_max_distr_r". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 max_r | rewrite 2 max_l]; try order; now apply sub_le_mono_r.
Qed.

Lemma sub_min_distr_l : forall n m p, min (p - n) (p - m) == p - max n m.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.sub_min_distr_l". Undo.  
intros. destruct (le_ge_cases n m).
rewrite max_r by trivial. apply min_r. now apply sub_le_mono_l.
rewrite max_l by trivial. apply min_l. now apply sub_le_mono_l.
Qed.

Lemma sub_min_distr_r : forall n m p, min (n - p) (m - p) == min n m - p.
Proof. try hammer_hook "NMaxMin" "NMaxMin.NMaxMinProp.sub_min_distr_r". Undo.  
intros. destruct (le_ge_cases n m);
[rewrite 2 min_l | rewrite 2 min_r]; try order; now apply sub_le_mono_r.
Qed.

End NMaxMinProp.
