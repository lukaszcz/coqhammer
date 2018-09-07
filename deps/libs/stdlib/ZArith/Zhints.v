From Hammer Require Import Hammer.

























Require Import BinInt.
Require Import Zorder.
Require Import Zmin.
Require Import Zabs.
Require Import Zcompare.
Require Import Znat.
Require Import auxiliary.
Require Import Zmisc.
Require Import Wf_Z.






Hint Resolve




Zsucc_eq_compat


Zsucc_gt_compat
Zgt_succ
Zorder.Zgt_pos_0
Zplus_gt_compat_l
Zplus_gt_compat_r


Pos2Z.is_pos
Z.lt_succ_diag_r
Zsucc_lt_compat
Z.lt_pred_l
Zplus_lt_compat_l
Zplus_lt_compat_r


Nat2Z.is_nonneg
Pos2Z.is_nonneg
Z.le_refl
Z.le_succ_diag_r
Zsucc_le_compat
Z.le_pred_l
Z.le_min_l
Z.le_min_r
Zplus_le_compat_l
Zplus_le_compat_r
Z.abs_nonneg





Z_eq_mult
Zplus_eq_compat


Zorder.Zmult_ge_compat_r
Zorder.Zmult_ge_compat_l
Zorder.Zmult_ge_compat


Zorder.Zmult_gt_0_compat
Z.lt_lt_succ_r


Z.mul_nonneg_nonneg
Zorder.Zmult_le_compat_r
Zorder.Zmult_le_compat_l
Z.add_nonneg_nonneg
Z.le_le_succ_r
Z.add_le_mono

: zarith.
