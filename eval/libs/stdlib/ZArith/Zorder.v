From Hammer Require Import Hammer.















Require Import BinPos BinInt Decidable Zcompare.
Require Import Arith_base.

Local Open Scope Z_scope.






Theorem Ztrichotomy_inf n m : {n < m} + {n = m} + {n > m}.
Proof. try hammer_hook "Zorder" "Zorder.Ztrichotomy_inf".  
unfold ">", "<". generalize (Z.compare_eq n m).
destruct (n ?= m); [ left; right | left; left | right]; auto.
Defined.

Theorem Ztrichotomy n m : n < m \/ n = m \/ n > m.
Proof. try hammer_hook "Zorder" "Zorder.Ztrichotomy".  
Z.swap_greater. apply Z.lt_trichotomy.
Qed.




Notation dec_eq := Z.eq_decidable (compat "8.3").
Notation dec_Zle := Z.le_decidable (compat "8.3").
Notation dec_Zlt := Z.lt_decidable (compat "8.3").

Theorem dec_Zne n m : decidable (Zne n m).
Proof. try hammer_hook "Zorder" "Zorder.dec_Zne".  
destruct (Z.eq_decidable n m); [right|left]; subst; auto.
Qed.

Theorem dec_Zgt n m : decidable (n > m).
Proof. try hammer_hook "Zorder" "Zorder.dec_Zgt".  
destruct (Z.lt_decidable m n); [left|right]; Z.swap_greater; auto.
Qed.

Theorem dec_Zge n m : decidable (n >= m).
Proof. try hammer_hook "Zorder" "Zorder.dec_Zge".  
destruct (Z.le_decidable m n); [left|right]; Z.swap_greater; auto.
Qed.

Theorem not_Zeq n m : n <> m -> n < m \/ m < n.
Proof. try hammer_hook "Zorder" "Zorder.not_Zeq".  
apply Z.lt_gt_cases.
Qed.



Notation Zgt_lt := Z.gt_lt (compat "8.3").
Notation Zlt_gt := Z.lt_gt (compat "8.3").
Notation Zge_le := Z.ge_le (compat "8.3").
Notation Zle_ge := Z.le_ge (compat "8.3").
Notation Zgt_iff_lt := Z.gt_lt_iff (compat "8.3").
Notation Zge_iff_le := Z.ge_le_iff (compat "8.3").

Lemma Zle_not_lt n m : n <= m -> ~ m < n.
Proof. try hammer_hook "Zorder" "Zorder.Zle_not_lt".  
apply Z.le_ngt.
Qed.

Lemma Zlt_not_le n m : n < m -> ~ m <= n.
Proof. try hammer_hook "Zorder" "Zorder.Zlt_not_le".  
apply Z.lt_nge.
Qed.

Lemma Zle_not_gt n m : n <= m -> ~ n > m.
Proof. try hammer_hook "Zorder" "Zorder.Zle_not_gt".  
trivial.
Qed.

Lemma Zgt_not_le n m : n > m -> ~ n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_not_le".  
Z.swap_greater. apply Z.lt_nge.
Qed.

Lemma Znot_ge_lt n m : ~ n >= m -> n < m.
Proof. try hammer_hook "Zorder" "Zorder.Znot_ge_lt".  
Z.swap_greater. apply Z.nle_gt.
Qed.

Lemma Znot_lt_ge n m : ~ n < m -> n >= m.
Proof. try hammer_hook "Zorder" "Zorder.Znot_lt_ge".  
trivial.
Qed.

Lemma Znot_gt_le n m: ~ n > m -> n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Znot_gt_le".  
trivial.
Qed.

Lemma Znot_le_gt n m : ~ n <= m -> n > m.
Proof. try hammer_hook "Zorder" "Zorder.Znot_le_gt".  
Z.swap_greater. apply Z.nle_gt.
Qed.

Lemma not_Zne n m : ~ Zne n m -> n = m.
Proof. try hammer_hook "Zorder" "Zorder.not_Zne".  
intros H.
destruct (Z.eq_decidable n m); [assumption|now elim H].
Qed.





Notation Zle_refl := Z.le_refl (compat "8.3").
Notation Zeq_le := Z.eq_le_incl (compat "8.3").

Hint Resolve Z.le_refl: zarith.



Notation Zle_antisym := Z.le_antisymm (compat "8.3").



Notation Zlt_asym := Z.lt_asymm (compat "8.3").

Lemma Zgt_asym n m : n > m -> ~ m > n.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_asym".  
Z.swap_greater. apply Z.lt_asymm.
Qed.



Notation Zlt_irrefl := Z.lt_irrefl (compat "8.3").
Notation Zlt_not_eq := Z.lt_neq (compat "8.3").

Lemma Zgt_irrefl n : ~ n > n.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_irrefl".  
Z.swap_greater. apply Z.lt_irrefl.
Qed.



Notation Zlt_le_weak := Z.lt_le_incl (compat "8.3").
Notation Zle_lt_or_eq_iff := Z.lt_eq_cases (compat "8.3").

Lemma Zle_lt_or_eq n m : n <= m -> n < m \/ n = m.
Proof. try hammer_hook "Zorder" "Zorder.Zle_lt_or_eq".  
apply Z.lt_eq_cases.
Qed.



Notation Zle_or_lt := Z.le_gt_cases (compat "8.3").



Notation Zlt_trans := Z.lt_trans (compat "8.3").

Lemma Zgt_trans n m p : n > m -> m > p -> n > p.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_trans".  
Z.swap_greater. intros; now transitivity m.
Qed.



Notation Zlt_le_trans := Z.lt_le_trans (compat "8.3").
Notation Zle_lt_trans := Z.le_lt_trans (compat "8.3").

Lemma Zle_gt_trans n m p : m <= n -> m > p -> n > p.
Proof. try hammer_hook "Zorder" "Zorder.Zle_gt_trans".  
Z.swap_greater. Z.order.
Qed.

Lemma Zgt_le_trans n m p : n > m -> p <= m -> n > p.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_le_trans".  
Z.swap_greater. Z.order.
Qed.



Notation Zle_trans := Z.le_trans (compat "8.3").

Lemma Zge_trans n m p : n >= m -> m >= p -> n >= p.
Proof. try hammer_hook "Zorder" "Zorder.Zge_trans".  
Z.swap_greater. Z.order.
Qed.

Hint Resolve Z.le_trans: zarith.







Lemma Zsucc_le_compat n m : m <= n -> Z.succ m <= Z.succ n.
Proof. try hammer_hook "Zorder" "Zorder.Zsucc_le_compat".  
apply Z.succ_le_mono.
Qed.

Lemma Zsucc_lt_compat n m : n < m -> Z.succ n < Z.succ m.
Proof. try hammer_hook "Zorder" "Zorder.Zsucc_lt_compat".  
apply Z.succ_lt_mono.
Qed.

Lemma Zsucc_gt_compat n m : m > n -> Z.succ m > Z.succ n.
Proof. try hammer_hook "Zorder" "Zorder.Zsucc_gt_compat".  
Z.swap_greater. apply Z.succ_lt_mono.
Qed.

Hint Resolve Zsucc_le_compat: zarith.



Lemma Zsucc_gt_reg n m : Z.succ m > Z.succ n -> m > n.
Proof. try hammer_hook "Zorder" "Zorder.Zsucc_gt_reg".  
Z.swap_greater. apply Z.succ_lt_mono.
Qed.

Lemma Zsucc_le_reg n m : Z.succ m <= Z.succ n -> m <= n.
Proof. try hammer_hook "Zorder" "Zorder.Zsucc_le_reg".  
apply Z.succ_le_mono.
Qed.

Lemma Zsucc_lt_reg n m : Z.succ n < Z.succ m -> n < m.
Proof. try hammer_hook "Zorder" "Zorder.Zsucc_lt_reg".  
apply Z.succ_lt_mono.
Qed.



Notation Zlt_succ := Z.lt_succ_diag_r (compat "8.3").
Notation Zlt_pred := Z.lt_pred_l (compat "8.3").

Lemma Zgt_succ n : Z.succ n > n.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_succ".  
Z.swap_greater. apply Z.lt_succ_diag_r.
Qed.

Lemma Znot_le_succ n : ~ Z.succ n <= n.
Proof. try hammer_hook "Zorder" "Zorder.Znot_le_succ".  
apply Z.lt_nge, Z.lt_succ_diag_r.
Qed.



Notation Zlt_succ_r := Z.lt_succ_r (compat "8.3").
Notation Zle_succ_l := Z.le_succ_l (compat "8.3").

Lemma Zgt_le_succ n m : m > n -> Z.succ n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_le_succ".  
Z.swap_greater. apply Z.le_succ_l.
Qed.

Lemma Zle_gt_succ n m : n <= m -> Z.succ m > n.
Proof. try hammer_hook "Zorder" "Zorder.Zle_gt_succ".  
Z.swap_greater. apply Z.lt_succ_r.
Qed.

Lemma Zle_lt_succ n m : n <= m -> n < Z.succ m.
Proof. try hammer_hook "Zorder" "Zorder.Zle_lt_succ".  
apply Z.lt_succ_r.
Qed.

Lemma Zlt_le_succ n m : n < m -> Z.succ n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zlt_le_succ".  
apply Z.le_succ_l.
Qed.

Lemma Zgt_succ_le n m : Z.succ m > n -> n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_succ_le".  
Z.swap_greater. apply Z.lt_succ_r.
Qed.

Lemma Zlt_succ_le n m : n < Z.succ m -> n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zlt_succ_le".  
apply Z.lt_succ_r.
Qed.

Lemma Zle_succ_gt n m : Z.succ n <= m -> m > n.
Proof. try hammer_hook "Zorder" "Zorder.Zle_succ_gt".  
Z.swap_greater. apply Z.le_succ_l.
Qed.



Notation Zle_succ := Z.le_succ_diag_r (compat "8.3").
Notation Zle_pred := Z.le_pred_l (compat "8.3").
Notation Zlt_lt_succ := Z.lt_lt_succ_r (compat "8.3").
Notation Zle_le_succ := Z.le_le_succ_r (compat "8.3").

Lemma Zle_succ_le n m : Z.succ n <= m -> n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zle_succ_le".  
intros. now apply Z.lt_le_incl, Z.le_succ_l.
Qed.

Hint Resolve Z.le_succ_diag_r: zarith.
Hint Resolve Z.le_le_succ_r: zarith.



Lemma Zgt_succ_pred n m : m > Z.succ n -> Z.pred m > n.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_succ_pred".  
Z.swap_greater. apply Z.lt_succ_lt_pred.
Qed.

Lemma Zlt_succ_pred n m : Z.succ n < m -> n < Z.pred m.
Proof. try hammer_hook "Zorder" "Zorder.Zlt_succ_pred".  
apply Z.lt_succ_lt_pred.
Qed.



Lemma Zlt_0_le_0_pred n : 0 < n -> 0 <= Z.pred n.
Proof. try hammer_hook "Zorder" "Zorder.Zlt_0_le_0_pred".  
apply Z.lt_le_pred.
Qed.

Lemma Zgt_0_le_0_pred n : n > 0 -> 0 <= Z.pred n.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_0_le_0_pred".  
Z.swap_greater. apply Z.lt_le_pred.
Qed.



Notation Zlt_0_1 := Z.lt_0_1 (compat "8.3").
Notation Zle_0_1 := Z.le_0_1 (compat "8.3").

Lemma Zle_neg_pos : forall p q:positive, Zneg p <= Zpos q.
Proof. try hammer_hook "Zorder" "Zorder.Zle_neg_pos".  
exact Pos2Z.neg_le_pos.
Qed.

Lemma Zgt_pos_0 : forall p:positive, Zpos p > 0.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_pos_0".  
easy.
Qed.


Lemma Zle_0_pos : forall p:positive, 0 <= Zpos p.
Proof. try hammer_hook "Zorder" "Zorder.Zle_0_pos".  
exact Pos2Z.pos_is_nonneg.
Qed.

Lemma Zlt_neg_0 : forall p:positive, Zneg p < 0.
Proof. try hammer_hook "Zorder" "Zorder.Zlt_neg_0".  
exact Pos2Z.neg_is_neg.
Qed.

Lemma Zle_0_nat : forall n:nat, 0 <= Z.of_nat n.
Proof. try hammer_hook "Zorder" "Zorder.Zle_0_nat".  
induction n; simpl; intros. apply Z.le_refl. easy.
Qed.

Hint Immediate Z.eq_le_incl: zarith.



Lemma Zgt_succ_gt_or_eq n m : Z.succ n > m -> n > m \/ m = n.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_succ_gt_or_eq".  
Z.swap_greater. intros. now apply Z.lt_eq_cases, Z.lt_succ_r.
Qed.




Notation Zplus_lt_le_compat := Z.add_lt_le_mono (compat "8.3").
Notation Zplus_le_lt_compat := Z.add_le_lt_mono (compat "8.3").
Notation Zplus_le_compat := Z.add_le_mono (compat "8.3").
Notation Zplus_lt_compat := Z.add_lt_mono (compat "8.3").

Lemma Zplus_gt_compat_l n m p : n > m -> p + n > p + m.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_gt_compat_l".  
Z.swap_greater. apply Z.add_lt_mono_l.
Qed.

Lemma Zplus_gt_compat_r n m p : n > m -> n + p > m + p.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_gt_compat_r".  
Z.swap_greater. apply Z.add_lt_mono_r.
Qed.

Lemma Zplus_le_compat_l n m p : n <= m -> p + n <= p + m.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_le_compat_l".  
apply Z.add_le_mono_l.
Qed.

Lemma Zplus_le_compat_r n m p : n <= m -> n + p <= m + p.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_le_compat_r".  
apply Z.add_le_mono_r.
Qed.

Lemma Zplus_lt_compat_l n m p : n < m -> p + n < p + m.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_lt_compat_l".  
apply Z.add_lt_mono_l.
Qed.

Lemma Zplus_lt_compat_r n m p : n < m -> n + p < m + p.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_lt_compat_r".  
apply Z.add_lt_mono_r.
Qed.



Notation Zplus_le_0_compat := Z.add_nonneg_nonneg (compat "8.3").



Lemma Zplus_le_reg_l n m p : p + n <= p + m -> n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_le_reg_l".  
apply Z.add_le_mono_l.
Qed.

Lemma Zplus_le_reg_r n m p : n + p <= m + p -> n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_le_reg_r".  
apply Z.add_le_mono_r.
Qed.

Lemma Zplus_lt_reg_l n m p : p + n < p + m -> n < m.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_lt_reg_l".  
apply Z.add_lt_mono_l.
Qed.

Lemma Zplus_lt_reg_r n m p : n + p < m + p -> n < m.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_lt_reg_r".  
apply Z.add_lt_mono_r.
Qed.

Lemma Zplus_gt_reg_l n m p : p + n > p + m -> n > m.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_gt_reg_l".  
Z.swap_greater. apply Z.add_lt_mono_l.
Qed.

Lemma Zplus_gt_reg_r n m p : n + p > m + p -> n > m.
Proof. try hammer_hook "Zorder" "Zorder.Zplus_gt_reg_r".  
Z.swap_greater. apply Z.add_lt_mono_r.
Qed.




Lemma Zmult_le_compat_r n m p : n <= m -> 0 <= p -> n * p <= m * p.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_le_compat_r".  
intros. now apply Z.mul_le_mono_nonneg_r.
Qed.

Lemma Zmult_le_compat_l n m p : n <= m -> 0 <= p -> p * n <= p * m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_le_compat_l".  
intros. now apply Z.mul_le_mono_nonneg_l.
Qed.

Lemma Zmult_lt_compat_r n m p : 0 < p -> n < m -> n * p < m * p.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_lt_compat_r".  
apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_gt_compat_r n m p : p > 0 -> n > m -> n * p > m * p.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_compat_r".  
Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_gt_0_lt_compat_r n m p : p > 0 -> n < m -> n * p < m * p.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_0_lt_compat_r".  
Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_gt_0_le_compat_r n m p : p > 0 -> n <= m -> n * p <= m * p.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_0_le_compat_r".  
Z.swap_greater. apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_lt_0_le_compat_r n m p : 0 < p -> n <= m -> n * p <= m * p.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_lt_0_le_compat_r".  
apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_gt_0_lt_compat_l n m p : p > 0 -> n < m -> p * n < p * m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_0_lt_compat_l".  
Z.swap_greater. apply Z.mul_lt_mono_pos_l.
Qed.

Lemma Zmult_lt_compat_l n m p : 0 < p -> n < m -> p * n < p * m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_lt_compat_l".  
apply Z.mul_lt_mono_pos_l.
Qed.

Lemma Zmult_gt_compat_l n m p : p > 0 -> n > m -> p * n > p * m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_compat_l".  
Z.swap_greater. apply Z.mul_lt_mono_pos_l.
Qed.

Lemma Zmult_ge_compat_r n m p : n >= m -> p >= 0 -> n * p >= m * p.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_ge_compat_r".  
Z.swap_greater. intros. now apply Z.mul_le_mono_nonneg_r.
Qed.

Lemma Zmult_ge_compat_l n m p : n >= m -> p >= 0 -> p * n >= p * m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_ge_compat_l".  
Z.swap_greater. intros. now apply Z.mul_le_mono_nonneg_l.
Qed.

Lemma Zmult_ge_compat n m p q :
n >= p -> m >= q -> p >= 0 -> q >= 0 -> n * m >= p * q.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_ge_compat".  
Z.swap_greater. intros. now apply Z.mul_le_mono_nonneg.
Qed.

Lemma Zmult_le_compat n m p q :
n <= p -> m <= q -> 0 <= n -> 0 <= m -> n * m <= p * q.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_le_compat".  
intros. now apply Z.mul_le_mono_nonneg.
Qed.



Lemma Zmult_gt_0_lt_reg_r n m p : p > 0 -> n * p < m * p -> n < m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_0_lt_reg_r".  
Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_lt_reg_r n m p : 0 < p -> n * p < m * p -> n < m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_lt_reg_r".  
apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_le_reg_r n m p : p > 0 -> n * p <= m * p -> n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_le_reg_r".  
Z.swap_greater. apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_lt_0_le_reg_r n m p : 0 < p -> n * p <= m * p -> n <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_lt_0_le_reg_r".  
apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_ge_reg_r n m p : p > 0 -> n * p >= m * p -> n >= m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_ge_reg_r".  
Z.swap_greater. apply Z.mul_le_mono_pos_r.
Qed.

Lemma Zmult_gt_reg_r n m p : p > 0 -> n * p > m * p -> n > m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_reg_r".  
Z.swap_greater. apply Z.mul_lt_mono_pos_r.
Qed.

Lemma Zmult_lt_compat n m p q :
0 <= n < p -> 0 <= m < q -> n * m < p * q.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_lt_compat".  
intros (Hn,Hnp) (Hm,Hmq). now apply Z.mul_lt_mono_nonneg.
Qed.

Lemma Zmult_lt_compat2 n m p q :
0 < n <= p -> 0 < m < q -> n * m < p * q.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_lt_compat2".  
intros (Hn, Hnp) (Hm,Hmq).
apply Z.le_lt_trans with (p * m).
apply Z.mul_le_mono_pos_r; trivial.
apply Z.mul_lt_mono_pos_l; Z.order.
Qed.



Notation Zmult_le_0_compat := Z.mul_nonneg_nonneg (compat "8.3").
Notation Zmult_lt_0_compat := Z.mul_pos_pos (compat "8.3").
Notation Zmult_lt_O_compat := Z.mul_pos_pos (compat "8.3").

Lemma Zmult_gt_0_compat n m : n > 0 -> m > 0 -> n * m > 0.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_0_compat".  
Z.swap_greater. apply Z.mul_pos_pos.
Qed.



Lemma Zmult_gt_0_le_0_compat n m : n > 0 -> 0 <= m -> 0 <= m * n.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_0_le_0_compat".  
Z.swap_greater. intros. apply Z.mul_nonneg_nonneg. trivial.
now apply Z.lt_le_incl.
Qed.



Lemma Zmult_le_0_reg_r n m : n > 0 -> 0 <= m * n -> 0 <= m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_le_0_reg_r".  
Z.swap_greater. apply Z.mul_nonneg_cancel_r.
Qed.

Lemma Zmult_lt_0_reg_r n m : 0 < n -> 0 < m * n -> 0 < m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_lt_0_reg_r".  
apply Z.mul_pos_cancel_r.
Qed.

Lemma Zmult_gt_0_lt_0_reg_r n m : n > 0 -> 0 < m * n -> 0 < m.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_0_lt_0_reg_r".  
Z.swap_greater. apply Z.mul_pos_cancel_r.
Qed.

Lemma Zmult_gt_0_reg_l n m : n > 0 -> n * m > 0 -> m > 0.
Proof. try hammer_hook "Zorder" "Zorder.Zmult_gt_0_reg_l".  
Z.swap_greater. apply Z.mul_pos_cancel_l.
Qed.




Lemma Zlt_square_simpl n m : 0 <= n -> m * m < n * n -> m < n.
Proof. try hammer_hook "Zorder" "Zorder.Zlt_square_simpl".  
apply Z.square_lt_simpl_nonneg.
Qed.

Lemma Zgt_square_simpl n m : n >= 0 -> n * n > m * m -> n > m.
Proof. try hammer_hook "Zorder" "Zorder.Zgt_square_simpl".  
Z.swap_greater. apply Z.square_lt_simpl_nonneg.
Qed.



Notation Zle_plus_swap := Z.le_add_le_sub_r (compat "8.3").
Notation Zlt_plus_swap := Z.lt_add_lt_sub_r (compat "8.3").
Notation Zlt_minus_simpl_swap := Z.lt_sub_pos (compat "8.3").

Lemma Zeq_plus_swap n m p : n + p = m <-> n = m - p.
Proof. try hammer_hook "Zorder" "Zorder.Zeq_plus_swap".  
apply Z.add_move_r.
Qed.

Lemma Zlt_0_minus_lt n m : 0 < n - m -> m < n.
Proof. try hammer_hook "Zorder" "Zorder.Zlt_0_minus_lt".  
apply Z.lt_0_sub.
Qed.

Lemma Zle_0_minus_le n m : 0 <= n - m -> m <= n.
Proof. try hammer_hook "Zorder" "Zorder.Zle_0_minus_le".  
apply Z.le_0_sub.
Qed.

Lemma Zle_minus_le_0 n m : m <= n -> 0 <= n - m.
Proof. try hammer_hook "Zorder" "Zorder.Zle_minus_le_0".  
apply Z.le_0_sub.
Qed.


Notation Zlt_O_minus_lt := Zlt_0_minus_lt (only parsing).
