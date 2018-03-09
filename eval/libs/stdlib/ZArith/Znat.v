From Hammer Require Import Hammer.












Require Export Arith_base.
Require Import BinPos BinInt BinNat Pnat Nnat.

Local Open Scope Z_scope.







Lemma nat_N_Z n : Z.of_N (N.of_nat n) = Z.of_nat n.
Proof. hammer_hook "Znat" "Znat.nat_N_Z". Restart. 
now destruct n.
Qed.

Lemma N_nat_Z n : Z.of_nat (N.to_nat n) = Z.of_N n.
Proof. hammer_hook "Znat" "Znat.N_nat_Z". Restart. 
destruct n; trivial. simpl.
destruct (Pos2Nat.is_succ p) as (m,H).
rewrite H. simpl. f_equal. now apply SuccNat2Pos.inv.
Qed.

Lemma positive_nat_Z p : Z.of_nat (Pos.to_nat p) = Zpos p.
Proof. hammer_hook "Znat" "Znat.positive_nat_Z". Restart. 
destruct (Pos2Nat.is_succ p) as (n,H).
rewrite H. simpl. f_equal. now apply SuccNat2Pos.inv.
Qed.

Lemma positive_N_Z p : Z.of_N (Npos p) = Zpos p.
Proof. hammer_hook "Znat" "Znat.positive_N_Z". Restart. 
reflexivity.
Qed.

Lemma positive_N_nat p : N.to_nat (Npos p) = Pos.to_nat p.
Proof. hammer_hook "Znat" "Znat.positive_N_nat". Restart. 
reflexivity.
Qed.

Lemma positive_nat_N p : N.of_nat (Pos.to_nat p) = Npos p.
Proof. hammer_hook "Znat" "Znat.positive_nat_N". Restart. 
destruct (Pos2Nat.is_succ p) as (n,H).
rewrite H. simpl. f_equal. now apply SuccNat2Pos.inv.
Qed.

Lemma Z_N_nat n : N.to_nat (Z.to_N n) = Z.to_nat n.
Proof. hammer_hook "Znat" "Znat.Z_N_nat". Restart. 
now destruct n.
Qed.

Lemma Z_nat_N n : N.of_nat (Z.to_nat n) = Z.to_N n.
Proof. hammer_hook "Znat" "Znat.Z_nat_N". Restart. 
destruct n; simpl; trivial. apply positive_nat_N.
Qed.

Lemma Zabs_N_nat n : N.to_nat (Z.abs_N n) = Z.abs_nat n.
Proof. hammer_hook "Znat" "Znat.Zabs_N_nat". Restart. 
now destruct n.
Qed.

Lemma Zabs_nat_N n : N.of_nat (Z.abs_nat n) = Z.abs_N n.
Proof. hammer_hook "Znat" "Znat.Zabs_nat_N". Restart. 
destruct n; simpl; trivial; apply positive_nat_N.
Qed.




Module N2Z.



Lemma id n : Z.to_N (Z.of_N n) = n.
Proof. hammer_hook "Znat" "Znat.N2Z.id". Restart. 
now destruct n.
Qed.



Lemma inj n m : Z.of_N n = Z.of_N m -> n = m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj". Restart. 
destruct n, m; simpl; congruence.
Qed.

Lemma inj_iff n m : Z.of_N n = Z.of_N m <-> n = m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_iff". Restart. 
split. apply inj. intros; now f_equal.
Qed.



Lemma is_nonneg n : 0 <= Z.of_N n.
Proof. hammer_hook "Znat" "Znat.N2Z.is_nonneg". Restart. 
now destruct n.
Qed.



Lemma inj_0 : Z.of_N 0 = 0.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_0". Restart. 
reflexivity.
Qed.

Lemma inj_pos p : Z.of_N (Npos p) = Zpos p.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_pos". Restart. 
reflexivity.
Qed.



Lemma inj_compare n m : (Z.of_N n ?= Z.of_N m) = (n ?= m)%N.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_compare". Restart. 
now destruct n, m.
Qed.

Lemma inj_le n m : (n<=m)%N <-> Z.of_N n <= Z.of_N m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_le". Restart. 
unfold Z.le. now rewrite inj_compare.
Qed.

Lemma inj_lt n m : (n<m)%N <-> Z.of_N n < Z.of_N m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_lt". Restart. 
unfold Z.lt. now rewrite inj_compare.
Qed.

Lemma inj_ge n m : (n>=m)%N <-> Z.of_N n >= Z.of_N m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_ge". Restart. 
unfold Z.ge. now rewrite inj_compare.
Qed.

Lemma inj_gt n m : (n>m)%N <-> Z.of_N n > Z.of_N m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_gt". Restart. 
unfold Z.gt. now rewrite inj_compare.
Qed.

Lemma inj_abs_N z : Z.of_N (Z.abs_N z) = Z.abs z.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_abs_N". Restart. 
now destruct z.
Qed.

Lemma inj_add n m : Z.of_N (n+m) = Z.of_N n + Z.of_N m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_add". Restart. 
now destruct n, m.
Qed.

Lemma inj_mul n m : Z.of_N (n*m) = Z.of_N n * Z.of_N m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_mul". Restart. 
now destruct n, m.
Qed.

Lemma inj_sub_max n m : Z.of_N (n-m) = Z.max 0 (Z.of_N n - Z.of_N m).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_sub_max". Restart. 
destruct n as [|n], m as [|m]; simpl; trivial.
rewrite Z.pos_sub_spec, Pos.compare_sub_mask. unfold Pos.sub.
now destruct (Pos.sub_mask n m).
Qed.

Lemma inj_sub n m : (m<=n)%N -> Z.of_N (n-m) = Z.of_N n - Z.of_N m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_sub". Restart. 
intros H. rewrite inj_sub_max.
unfold N.le in H.
rewrite N.compare_antisym, <- inj_compare, Z.compare_sub in H.
destruct (Z.of_N n - Z.of_N m); trivial; now destruct H.
Qed.

Lemma inj_succ n : Z.of_N (N.succ n) = Z.succ (Z.of_N n).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_succ". Restart. 
destruct n. trivial. simpl. now rewrite Pos.add_1_r.
Qed.

Lemma inj_pred_max n : Z.of_N (N.pred n) = Z.max 0 (Z.pred (Z.of_N n)).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_pred_max". Restart. 
unfold Z.pred. now rewrite N.pred_sub, inj_sub_max.
Qed.

Lemma inj_pred n : (0<n)%N -> Z.of_N (N.pred n) = Z.pred (Z.of_N n).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_pred". Restart. 
intros H. unfold Z.pred. rewrite N.pred_sub, inj_sub; trivial.
now apply N.le_succ_l in H.
Qed.

Lemma inj_min n m : Z.of_N (N.min n m) = Z.min (Z.of_N n) (Z.of_N m).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_min". Restart. 
unfold Z.min, N.min. rewrite inj_compare. now case N.compare.
Qed.

Lemma inj_max n m : Z.of_N (N.max n m) = Z.max (Z.of_N n) (Z.of_N m).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_max". Restart. 
unfold Z.max, N.max. rewrite inj_compare.
case N.compare_spec; intros; subst; trivial.
Qed.

Lemma inj_div n m : Z.of_N (n/m) = Z.of_N n / Z.of_N m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_div". Restart. 
destruct m as [|m]. now destruct n.
apply Z.div_unique_pos with (Z.of_N (n mod (Npos m))).
split. apply is_nonneg. apply inj_lt. now apply N.mod_lt.
rewrite <- inj_mul, <- inj_add. f_equal. now apply N.div_mod.
Qed.

Lemma inj_mod n m : (m<>0)%N -> Z.of_N (n mod m) = (Z.of_N n) mod (Z.of_N m).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_mod". Restart. 
intros Hm.
apply Z.mod_unique_pos with (Z.of_N (n / m)).
split. apply is_nonneg. apply inj_lt. now apply N.mod_lt.
rewrite <- inj_mul, <- inj_add. f_equal. now apply N.div_mod.
Qed.

Lemma inj_quot n m : Z.of_N (n/m) = Z.of_N n ÷ Z.of_N m.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_quot". Restart. 
destruct m.
- now destruct n.
- rewrite Z.quot_div_nonneg, inj_div; trivial. apply is_nonneg. easy.
Qed.

Lemma inj_rem n m : Z.of_N (n mod m) = Z.rem (Z.of_N n) (Z.of_N m).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_rem". Restart. 
destruct m.
- now destruct n.
- rewrite Z.rem_mod_nonneg, inj_mod; trivial. easy. apply is_nonneg. easy.
Qed.

Lemma inj_div2 n : Z.of_N (N.div2 n) = Z.div2 (Z.of_N n).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_div2". Restart. 
destruct n as [|p]; trivial. now destruct p.
Qed.

Lemma inj_quot2 n : Z.of_N (N.div2 n) = Z.quot2 (Z.of_N n).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_quot2". Restart. 
destruct n as [|p]; trivial. now destruct p.
Qed.

Lemma inj_pow n m : Z.of_N (n^m) = (Z.of_N n)^(Z.of_N m).
Proof. hammer_hook "Znat" "Znat.N2Z.inj_pow". Restart. 
destruct n, m; trivial. now rewrite Z.pow_0_l. apply Pos2Z.inj_pow.
Qed.

Lemma inj_testbit a n :
Z.testbit (Z.of_N a) (Z.of_N n) = N.testbit a n.
Proof. hammer_hook "Znat" "Znat.N2Z.inj_testbit". Restart.  apply Z.testbit_of_N. Qed.

End N2Z.

Module Z2N.



Lemma id n : 0<=n -> Z.of_N (Z.to_N n) = n.
Proof. hammer_hook "Znat" "Znat.Z2N.id". Restart. 
destruct n; (now destruct 1) || trivial.
Qed.



Lemma inj n m : 0<=n -> 0<=m -> Z.to_N n = Z.to_N m -> n = m.
Proof. hammer_hook "Znat" "Znat.Z2N.inj". Restart. 
intros. rewrite <- (id n), <- (id m) by trivial. now f_equal.
Qed.

Lemma inj_iff n m : 0<=n -> 0<=m -> (Z.to_N n = Z.to_N m <-> n = m).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_iff". Restart. 
intros. split. now apply inj. intros; now subst.
Qed.



Lemma inj_0 : Z.to_N 0 = 0%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_0". Restart. 
reflexivity.
Qed.

Lemma inj_pos n : Z.to_N (Zpos n) = Npos n.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_pos". Restart. 
reflexivity.
Qed.

Lemma inj_neg n : Z.to_N (Zneg n) = 0%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_neg". Restart. 
reflexivity.
Qed.



Lemma inj_add n m : 0<=n -> 0<=m -> Z.to_N (n+m) = (Z.to_N n + Z.to_N m)%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_add". Restart. 
destruct n, m; trivial; (now destruct 1) || (now destruct 2).
Qed.

Lemma inj_mul n m : 0<=n -> 0<=m -> Z.to_N (n*m) = (Z.to_N n * Z.to_N m)%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_mul". Restart. 
destruct n, m; trivial; (now destruct 1) || (now destruct 2).
Qed.

Lemma inj_succ n : 0<=n -> Z.to_N (Z.succ n) = N.succ (Z.to_N n).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_succ". Restart. 
unfold Z.succ. intros. rewrite inj_add by easy. apply N.add_1_r.
Qed.

Lemma inj_sub n m : 0<=m -> Z.to_N (n - m) = (Z.to_N n - Z.to_N m)%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_sub". Restart. 
destruct n as [|n|n], m as [|m|m]; trivial; try (now destruct 1).
intros _. simpl.
rewrite Z.pos_sub_spec, Pos.compare_sub_mask. unfold Pos.sub.
now destruct (Pos.sub_mask n m).
Qed.

Lemma inj_pred n : Z.to_N (Z.pred n) = N.pred (Z.to_N n).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_pred". Restart. 
unfold Z.pred. rewrite <- N.sub_1_r. now apply (inj_sub n 1).
Qed.

Lemma inj_compare n m : 0<=n -> 0<=m ->
(Z.to_N n ?= Z.to_N m)%N = (n ?= m).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_compare". Restart. 
intros Hn Hm. now rewrite <- N2Z.inj_compare, !id.
Qed.

Lemma inj_le n m : 0<=n -> 0<=m -> (n<=m <-> (Z.to_N n <= Z.to_N m)%N).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_le". Restart. 
intros Hn Hm. unfold Z.le, N.le. now rewrite inj_compare.
Qed.

Lemma inj_lt n m : 0<=n -> 0<=m -> (n<m <-> (Z.to_N n < Z.to_N m)%N).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_lt". Restart. 
intros Hn Hm. unfold Z.lt, N.lt. now rewrite inj_compare.
Qed.

Lemma inj_min n m : Z.to_N (Z.min n m) = N.min (Z.to_N n) (Z.to_N m).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_min". Restart. 
destruct n, m; simpl; trivial; unfold Z.min, N.min; simpl;
now case Pos.compare.
Qed.

Lemma inj_max n m : Z.to_N (Z.max n m) = N.max (Z.to_N n) (Z.to_N m).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_max". Restart. 
destruct n, m; simpl; trivial; unfold Z.max, N.max; simpl.
case Pos.compare_spec; intros; subst; trivial.
now case Pos.compare.
Qed.

Lemma inj_div n m : 0<=n -> 0<=m -> Z.to_N (n/m) = (Z.to_N n / Z.to_N m)%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_div". Restart. 
destruct n, m; trivial; intros Hn Hm;
(now destruct Hn) || (now destruct Hm) || clear.
simpl. rewrite <- (N2Z.id (_ / _)). f_equal. now rewrite N2Z.inj_div.
Qed.

Lemma inj_mod n m : 0<=n -> 0<m ->
Z.to_N (n mod m) = ((Z.to_N n) mod (Z.to_N m))%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_mod". Restart. 
destruct n, m; trivial; intros Hn Hm;
(now destruct Hn) || (now destruct Hm) || clear.
simpl. rewrite <- (N2Z.id (_ mod _)). f_equal. now rewrite N2Z.inj_mod.
Qed.

Lemma inj_quot n m : 0<=n -> 0<=m -> Z.to_N (n÷m) = (Z.to_N n / Z.to_N m)%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_quot". Restart. 
destruct m.
- now destruct n.
- intros. now rewrite Z.quot_div_nonneg, inj_div.
- now destruct 2.
Qed.

Lemma inj_rem n m :0<=n -> 0<=m ->
Z.to_N (Z.rem n m) = ((Z.to_N n) mod (Z.to_N m))%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_rem". Restart. 
destruct m.
- now destruct n.
- intros. now rewrite Z.rem_mod_nonneg, inj_mod.
- now destruct 2.
Qed.

Lemma inj_div2 n : Z.to_N (Z.div2 n) = N.div2 (Z.to_N n).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_div2". Restart. 
destruct n as [|p|p]; trivial. now destruct p.
Qed.

Lemma inj_quot2 n : Z.to_N (Z.quot2 n) = N.div2 (Z.to_N n).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_quot2". Restart. 
destruct n as [|p|p]; trivial; now destruct p.
Qed.

Lemma inj_pow n m : 0<=n -> 0<=m -> Z.to_N (n^m) = ((Z.to_N n)^(Z.to_N m))%N.
Proof. hammer_hook "Znat" "Znat.Z2N.inj_pow". Restart. 
destruct m.
- trivial.
- intros. now rewrite <- (N2Z.id (_ ^ _)), N2Z.inj_pow, id.
- now destruct 2.
Qed.

Lemma inj_testbit a n : 0<=n ->
Z.testbit (Z.of_N a) n = N.testbit a (Z.to_N n).
Proof. hammer_hook "Znat" "Znat.Z2N.inj_testbit". Restart.  apply Z.testbit_of_N'. Qed.

End Z2N.

Module Zabs2N.



Lemma abs_N_spec n : Z.abs_N n = Z.to_N (Z.abs n).
Proof. hammer_hook "Znat" "Znat.Zabs2N.abs_N_spec". Restart. 
now destruct n.
Qed.

Lemma abs_N_nonneg n : 0<=n -> Z.abs_N n = Z.to_N n.
Proof. hammer_hook "Znat" "Znat.Zabs2N.abs_N_nonneg". Restart. 
destruct n; trivial; now destruct 1.
Qed.

Lemma id_abs n : Z.of_N (Z.abs_N n) = Z.abs n.
Proof. hammer_hook "Znat" "Znat.Zabs2N.id_abs". Restart. 
now destruct n.
Qed.

Lemma id n : Z.abs_N (Z.of_N n) = n.
Proof. hammer_hook "Znat" "Znat.Zabs2N.id". Restart. 
now destruct n.
Qed.



Lemma inj_0 : Z.abs_N 0 = 0%N.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_0". Restart. 
reflexivity.
Qed.

Lemma inj_pos p : Z.abs_N (Zpos p) = Npos p.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_pos". Restart. 
reflexivity.
Qed.

Lemma inj_neg p : Z.abs_N (Zneg p) = Npos p.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_neg". Restart. 
reflexivity.
Qed.



Lemma inj_opp n : Z.abs_N (-n) = Z.abs_N n.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_opp". Restart. 
now destruct n.
Qed.

Lemma inj_succ n : 0<=n -> Z.abs_N (Z.succ n) = N.succ (Z.abs_N n).
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_succ". Restart. 
intros. rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_succ.
now apply Z.le_le_succ_r.
Qed.

Lemma inj_add n m : 0<=n -> 0<=m -> Z.abs_N (n+m) = (Z.abs_N n + Z.abs_N m)%N.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_add". Restart. 
intros. rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_add.
now apply Z.add_nonneg_nonneg.
Qed.

Lemma inj_mul n m : Z.abs_N (n*m) = (Z.abs_N n * Z.abs_N m)%N.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_mul". Restart. 
now destruct n, m.
Qed.

Lemma inj_sub n m : 0<=m<=n -> Z.abs_N (n-m) = (Z.abs_N n - Z.abs_N m)%N.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_sub". Restart. 
intros (Hn,H). rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_sub.
Z.order.
now apply Z.le_0_sub.
Qed.

Lemma inj_pred n : 0<n -> Z.abs_N (Z.pred n) = N.pred (Z.abs_N n).
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_pred". Restart. 
intros. rewrite !abs_N_nonneg. now apply Z2N.inj_pred.
Z.order.
apply Z.lt_succ_r. now rewrite Z.succ_pred.
Qed.

Lemma inj_compare n m : 0<=n -> 0<=m ->
(Z.abs_N n ?= Z.abs_N m)%N = (n ?= m).
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_compare". Restart. 
intros. rewrite !abs_N_nonneg by trivial. now apply Z2N.inj_compare.
Qed.

Lemma inj_le n m : 0<=n -> 0<=m -> (n<=m <-> (Z.abs_N n <= Z.abs_N m)%N).
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_le". Restart. 
intros Hn Hm. unfold Z.le, N.le. now rewrite inj_compare.
Qed.

Lemma inj_lt n m : 0<=n -> 0<=m -> (n<m <-> (Z.abs_N n < Z.abs_N m)%N).
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_lt". Restart. 
intros Hn Hm. unfold Z.lt, N.lt. now rewrite inj_compare.
Qed.

Lemma inj_min n m : 0<=n -> 0<=m ->
Z.abs_N (Z.min n m) = N.min (Z.abs_N n) (Z.abs_N m).
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_min". Restart. 
intros. rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_min.
now apply Z.min_glb.
Qed.

Lemma inj_max n m : 0<=n -> 0<=m ->
Z.abs_N (Z.max n m) = N.max (Z.abs_N n) (Z.abs_N m).
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_max". Restart. 
intros. rewrite !abs_N_nonneg; trivial. now apply Z2N.inj_max.
transitivity n; trivial. apply Z.le_max_l.
Qed.

Lemma inj_quot n m : Z.abs_N (n÷m) = ((Z.abs_N n) / (Z.abs_N m))%N.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_quot". Restart. 
assert (forall p q, Z.abs_N (Zpos p ÷ Zpos q) = (Npos p / Npos q)%N).
intros. rewrite abs_N_nonneg. now apply Z2N.inj_quot. now apply Z.quot_pos.
destruct n, m; trivial; simpl.
- trivial.
- now rewrite <- Pos2Z.opp_pos, Z.quot_opp_r, inj_opp.
- now rewrite <- Pos2Z.opp_pos, Z.quot_opp_l, inj_opp.
- now rewrite <- 2 Pos2Z.opp_pos, Z.quot_opp_opp.
Qed.

Lemma inj_rem n m : Z.abs_N (Z.rem n m) = ((Z.abs_N n) mod (Z.abs_N m))%N.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_rem". Restart. 
assert
(forall p q, Z.abs_N (Z.rem (Zpos p) (Zpos q)) = ((Npos p) mod (Npos q))%N).
intros. rewrite abs_N_nonneg. now apply Z2N.inj_rem. now apply Z.rem_nonneg.
destruct n, m; trivial; simpl.
- trivial.
- now rewrite <- Pos2Z.opp_pos, Z.rem_opp_r.
- now rewrite <- Pos2Z.opp_pos, Z.rem_opp_l, inj_opp.
- now rewrite <- 2 Pos2Z.opp_pos, Z.rem_opp_opp, inj_opp.
Qed.

Lemma inj_pow n m : 0<=m -> Z.abs_N (n^m) = ((Z.abs_N n)^(Z.abs_N m))%N.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_pow". Restart. 
intros Hm. rewrite abs_N_spec, Z.abs_pow, Z2N.inj_pow, <- abs_N_spec; trivial.
f_equal. symmetry; now apply abs_N_nonneg. apply Z.abs_nonneg.
Qed.



Lemma inj_succ_abs n : Z.abs_N (Z.succ (Z.abs n)) = N.succ (Z.abs_N n).
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_succ_abs". Restart. 
destruct n; simpl; trivial; now rewrite Pos.add_1_r.
Qed.

Lemma inj_add_abs n m :
Z.abs_N (Z.abs n + Z.abs m) = (Z.abs_N n + Z.abs_N m)%N.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_add_abs". Restart. 
now destruct n, m.
Qed.

Lemma inj_mul_abs n m :
Z.abs_N (Z.abs n * Z.abs m) = (Z.abs_N n * Z.abs_N m)%N.
Proof. hammer_hook "Znat" "Znat.Zabs2N.inj_mul_abs". Restart. 
now destruct n, m.
Qed.

End Zabs2N.




Module Nat2Z.



Lemma inj_0 : Z.of_nat 0 = 0.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_0". Restart. 
reflexivity.
Qed.

Lemma inj_succ n : Z.of_nat (S n) = Z.succ (Z.of_nat n).
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_succ". Restart. 
destruct n. trivial. simpl. apply Pos2Z.inj_succ.
Qed.



Lemma is_nonneg n : 0 <= Z.of_nat n.
Proof. hammer_hook "Znat" "Znat.Nat2Z.is_nonneg". Restart. 
now induction n.
Qed.



Lemma id n : Z.to_nat (Z.of_nat n) = n.
Proof. hammer_hook "Znat" "Znat.Nat2Z.id". Restart. 
now rewrite <- nat_N_Z, <- Z_N_nat, N2Z.id, Nat2N.id.
Qed.



Lemma inj n m : Z.of_nat n = Z.of_nat m -> n = m.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj". Restart. 
intros H. now rewrite <- (id n), <- (id m), H.
Qed.

Lemma inj_iff n m : Z.of_nat n = Z.of_nat m <-> n = m.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_iff". Restart. 
split. apply inj. intros; now f_equal.
Qed.



Lemma inj_compare n m : (Z.of_nat n ?= Z.of_nat m) = (n ?= m)%nat.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_compare". Restart. 
now rewrite <-!nat_N_Z, N2Z.inj_compare, <- Nat2N.inj_compare.
Qed.

Lemma inj_le n m : (n<=m)%nat <-> Z.of_nat n <= Z.of_nat m.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_le". Restart. 
unfold Z.le. now rewrite inj_compare, nat_compare_le.
Qed.

Lemma inj_lt n m : (n<m)%nat <-> Z.of_nat n < Z.of_nat m.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_lt". Restart. 
unfold Z.lt. now rewrite inj_compare, nat_compare_lt.
Qed.

Lemma inj_ge n m : (n>=m)%nat <-> Z.of_nat n >= Z.of_nat m.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_ge". Restart. 
unfold Z.ge. now rewrite inj_compare, nat_compare_ge.
Qed.

Lemma inj_gt n m : (n>m)%nat <-> Z.of_nat n > Z.of_nat m.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_gt". Restart. 
unfold Z.gt. now rewrite inj_compare, nat_compare_gt.
Qed.

Lemma inj_abs_nat z : Z.of_nat (Z.abs_nat z) = Z.abs z.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_abs_nat". Restart. 
destruct z; simpl; trivial;
destruct (Pos2Nat.is_succ p) as (n,H); rewrite H; simpl; f_equal;
now apply SuccNat2Pos.inv.
Qed.

Lemma inj_add n m : Z.of_nat (n+m) = Z.of_nat n + Z.of_nat m.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_add". Restart. 
now rewrite <- !nat_N_Z, Nat2N.inj_add, N2Z.inj_add.
Qed.

Lemma inj_mul n m : Z.of_nat (n*m) = Z.of_nat n * Z.of_nat m.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_mul". Restart. 
now rewrite <- !nat_N_Z, Nat2N.inj_mul, N2Z.inj_mul.
Qed.

Lemma inj_sub_max n m : Z.of_nat (n-m) = Z.max 0 (Z.of_nat n - Z.of_nat m).
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_sub_max". Restart. 
now rewrite <- !nat_N_Z, Nat2N.inj_sub, N2Z.inj_sub_max.
Qed.

Lemma inj_sub n m : (m<=n)%nat -> Z.of_nat (n-m) = Z.of_nat n - Z.of_nat m.
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_sub". Restart. 
rewrite nat_compare_le, Nat2N.inj_compare. intros.
now rewrite <- !nat_N_Z, Nat2N.inj_sub, N2Z.inj_sub.
Qed.

Lemma inj_pred_max n : Z.of_nat (Nat.pred n) = Z.max 0 (Z.pred (Z.of_nat n)).
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_pred_max". Restart. 
now rewrite <- !nat_N_Z, Nat2N.inj_pred, N2Z.inj_pred_max.
Qed.

Lemma inj_pred n : (0<n)%nat -> Z.of_nat (Nat.pred n) = Z.pred (Z.of_nat n).
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_pred". Restart. 
rewrite nat_compare_lt, Nat2N.inj_compare. intros.
now rewrite <- !nat_N_Z, Nat2N.inj_pred, N2Z.inj_pred.
Qed.

Lemma inj_min n m : Z.of_nat (Nat.min n m) = Z.min (Z.of_nat n) (Z.of_nat m).
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_min". Restart. 
now rewrite <- !nat_N_Z, Nat2N.inj_min, N2Z.inj_min.
Qed.

Lemma inj_max n m : Z.of_nat (Nat.max n m) = Z.max (Z.of_nat n) (Z.of_nat m).
Proof. hammer_hook "Znat" "Znat.Nat2Z.inj_max". Restart. 
now rewrite <- !nat_N_Z, Nat2N.inj_max, N2Z.inj_max.
Qed.

End Nat2Z.

Module Z2Nat.



Lemma id n : 0<=n -> Z.of_nat (Z.to_nat n) = n.
Proof. hammer_hook "Znat" "Znat.Z2Nat.id". Restart. 
intros. now rewrite <- Z_N_nat, <- nat_N_Z, N2Nat.id, Z2N.id.
Qed.



Lemma inj n m : 0<=n -> 0<=m -> Z.to_nat n = Z.to_nat m -> n = m.
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj". Restart. 
intros. rewrite <- (id n), <- (id m) by trivial. now f_equal.
Qed.

Lemma inj_iff n m : 0<=n -> 0<=m -> (Z.to_nat n = Z.to_nat m <-> n = m).
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_iff". Restart. 
intros. split. now apply inj. intros; now subst.
Qed.



Lemma inj_0 : Z.to_nat 0 = O.
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_0". Restart. 
reflexivity.
Qed.

Lemma inj_pos n : Z.to_nat (Zpos n) = Pos.to_nat n.
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_pos". Restart. 
reflexivity.
Qed.

Lemma inj_neg n : Z.to_nat (Zneg n) = O.
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_neg". Restart. 
reflexivity.
Qed.



Lemma inj_add n m : 0<=n -> 0<=m ->
Z.to_nat (n+m) = (Z.to_nat n + Z.to_nat m)%nat.
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_add". Restart. 
intros. now rewrite <- !Z_N_nat, Z2N.inj_add, N2Nat.inj_add.
Qed.

Lemma inj_mul n m : 0<=n -> 0<=m ->
Z.to_nat (n*m) = (Z.to_nat n * Z.to_nat m)%nat.
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_mul". Restart. 
intros. now rewrite <- !Z_N_nat, Z2N.inj_mul, N2Nat.inj_mul.
Qed.

Lemma inj_succ n : 0<=n -> Z.to_nat (Z.succ n) = S (Z.to_nat n).
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_succ". Restart. 
intros. now rewrite <- !Z_N_nat, Z2N.inj_succ, N2Nat.inj_succ.
Qed.

Lemma inj_sub n m : 0<=m -> Z.to_nat (n - m) = (Z.to_nat n - Z.to_nat m)%nat.
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_sub". Restart. 
intros. now rewrite <- !Z_N_nat, Z2N.inj_sub, N2Nat.inj_sub.
Qed.

Lemma inj_pred n : Z.to_nat (Z.pred n) = Nat.pred (Z.to_nat n).
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_pred". Restart. 
now rewrite <- !Z_N_nat, Z2N.inj_pred, N2Nat.inj_pred.
Qed.

Lemma inj_compare n m : 0<=n -> 0<=m ->
(Z.to_nat n ?= Z.to_nat m)%nat = (n ?= m).
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_compare". Restart. 
intros Hn Hm. now rewrite <- Nat2Z.inj_compare, !id.
Qed.

Lemma inj_le n m : 0<=n -> 0<=m -> (n<=m <-> (Z.to_nat n <= Z.to_nat m)%nat).
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_le". Restart. 
intros Hn Hm. unfold Z.le. now rewrite nat_compare_le, inj_compare.
Qed.

Lemma inj_lt n m : 0<=n -> 0<=m -> (n<m <-> (Z.to_nat n < Z.to_nat m)%nat).
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_lt". Restart. 
intros Hn Hm. unfold Z.lt. now rewrite nat_compare_lt, inj_compare.
Qed.

Lemma inj_min n m : Z.to_nat (Z.min n m) = Nat.min (Z.to_nat n) (Z.to_nat m).
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_min". Restart. 
now rewrite <- !Z_N_nat, Z2N.inj_min, N2Nat.inj_min.
Qed.

Lemma inj_max n m : Z.to_nat (Z.max n m) = Nat.max (Z.to_nat n) (Z.to_nat m).
Proof. hammer_hook "Znat" "Znat.Z2Nat.inj_max". Restart. 
now rewrite <- !Z_N_nat, Z2N.inj_max, N2Nat.inj_max.
Qed.

End Z2Nat.

Module Zabs2Nat.



Lemma abs_nat_spec n : Z.abs_nat n = Z.to_nat (Z.abs n).
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.abs_nat_spec". Restart. 
now destruct n.
Qed.

Lemma abs_nat_nonneg n : 0<=n -> Z.abs_nat n = Z.to_nat n.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.abs_nat_nonneg". Restart. 
destruct n; trivial; now destruct 1.
Qed.

Lemma id_abs n : Z.of_nat (Z.abs_nat n) = Z.abs n.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.id_abs". Restart. 
rewrite <-Zabs_N_nat, N_nat_Z. apply Zabs2N.id_abs.
Qed.

Lemma id n : Z.abs_nat (Z.of_nat n) = n.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.id". Restart. 
now rewrite <-Zabs_N_nat, <-nat_N_Z, Zabs2N.id, Nat2N.id.
Qed.



Lemma inj_0 : Z.abs_nat 0 = 0%nat.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_0". Restart. 
reflexivity.
Qed.

Lemma inj_pos p : Z.abs_nat (Zpos p) = Pos.to_nat p.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_pos". Restart. 
reflexivity.
Qed.

Lemma inj_neg p : Z.abs_nat (Zneg p) = Pos.to_nat p.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_neg". Restart. 
reflexivity.
Qed.



Lemma inj_succ n : 0<=n -> Z.abs_nat (Z.succ n) = S (Z.abs_nat n).
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_succ". Restart. 
intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_succ, N2Nat.inj_succ.
Qed.

Lemma inj_add n m : 0<=n -> 0<=m ->
Z.abs_nat (n+m) = (Z.abs_nat n + Z.abs_nat m)%nat.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_add". Restart. 
intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_add, N2Nat.inj_add.
Qed.

Lemma inj_mul n m : Z.abs_nat (n*m) = (Z.abs_nat n * Z.abs_nat m)%nat.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_mul". Restart. 
destruct n, m; simpl; trivial using Pos2Nat.inj_mul.
Qed.

Lemma inj_sub n m : 0<=m<=n ->
Z.abs_nat (n-m) = (Z.abs_nat n - Z.abs_nat m)%nat.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_sub". Restart. 
intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_sub, N2Nat.inj_sub.
Qed.

Lemma inj_pred n : 0<n -> Z.abs_nat (Z.pred n) = Nat.pred (Z.abs_nat n).
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_pred". Restart. 
intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_pred, N2Nat.inj_pred.
Qed.

Lemma inj_compare n m : 0<=n -> 0<=m ->
(Z.abs_nat n ?= Z.abs_nat m)%nat = (n ?= m).
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_compare". Restart. 
intros. now rewrite <- !Zabs_N_nat, <- N2Nat.inj_compare, Zabs2N.inj_compare.
Qed.

Lemma inj_le n m : 0<=n -> 0<=m -> (n<=m <-> (Z.abs_nat n <= Z.abs_nat m)%nat).
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_le". Restart. 
intros Hn Hm. unfold Z.le. now rewrite nat_compare_le, inj_compare.
Qed.

Lemma inj_lt n m : 0<=n -> 0<=m -> (n<m <-> (Z.abs_nat n < Z.abs_nat m)%nat).
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_lt". Restart. 
intros Hn Hm. unfold Z.lt. now rewrite nat_compare_lt, inj_compare.
Qed.

Lemma inj_min n m : 0<=n -> 0<=m ->
Z.abs_nat (Z.min n m) = Nat.min (Z.abs_nat n) (Z.abs_nat m).
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_min". Restart. 
intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_min, N2Nat.inj_min.
Qed.

Lemma inj_max n m : 0<=n -> 0<=m ->
Z.abs_nat (Z.max n m) = Nat.max (Z.abs_nat n) (Z.abs_nat m).
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_max". Restart. 
intros. now rewrite <- !Zabs_N_nat, Zabs2N.inj_max, N2Nat.inj_max.
Qed.



Lemma inj_succ_abs n : Z.abs_nat (Z.succ (Z.abs n)) = S (Z.abs_nat n).
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_succ_abs". Restart. 
now rewrite <- !Zabs_N_nat, Zabs2N.inj_succ_abs, N2Nat.inj_succ.
Qed.

Lemma inj_add_abs n m :
Z.abs_nat (Z.abs n + Z.abs m) = (Z.abs_nat n + Z.abs_nat m)%nat.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_add_abs". Restart. 
now rewrite <- !Zabs_N_nat, Zabs2N.inj_add_abs, N2Nat.inj_add.
Qed.

Lemma inj_mul_abs n m :
Z.abs_nat (Z.abs n * Z.abs m) = (Z.abs_nat n * Z.abs_nat m)%nat.
Proof. hammer_hook "Znat" "Znat.Zabs2Nat.inj_mul_abs". Restart. 
now rewrite <- !Zabs_N_nat, Zabs2N.inj_mul_abs, N2Nat.inj_mul.
Qed.

End Zabs2Nat.




Definition neq (x y:nat) := x <> y.

Lemma inj_neq n m : neq n m -> Zne (Z.of_nat n) (Z.of_nat m).
Proof. hammer_hook "Znat" "Znat.inj_neq". Restart.  intros H H'. now apply H, Nat2Z.inj. Qed.

Lemma Zpos_P_of_succ_nat n : Zpos (Pos.of_succ_nat n) = Z.succ (Z.of_nat n).
Proof. hammer_hook "Znat" "Znat.Zpos_P_of_succ_nat". Restart. exact ((Nat2Z.inj_succ n)). Qed.



Definition inj_eq := (f_equal Z.of_nat).
Definition inj_le n m := proj1 (Nat2Z.inj_le n m).
Definition inj_lt n m := proj1 (Nat2Z.inj_lt n m).
Definition inj_ge n m := proj1 (Nat2Z.inj_ge n m).
Definition inj_gt n m := proj1 (Nat2Z.inj_gt n m).



Notation inj_0 := Nat2Z.inj_0 (compat "8.3").
Notation inj_S := Nat2Z.inj_succ (compat "8.3").
Notation inj_compare := Nat2Z.inj_compare (compat "8.3").
Notation inj_eq_rev := Nat2Z.inj (compat "8.3").
Notation inj_eq_iff := (fun n m => iff_sym (Nat2Z.inj_iff n m)) (compat "8.3").
Notation inj_le_iff := Nat2Z.inj_le (compat "8.3").
Notation inj_lt_iff := Nat2Z.inj_lt (compat "8.3").
Notation inj_ge_iff := Nat2Z.inj_ge (compat "8.3").
Notation inj_gt_iff := Nat2Z.inj_gt (compat "8.3").
Notation inj_le_rev := (fun n m => proj2 (Nat2Z.inj_le n m)) (compat "8.3").
Notation inj_lt_rev := (fun n m => proj2 (Nat2Z.inj_lt n m)) (compat "8.3").
Notation inj_ge_rev := (fun n m => proj2 (Nat2Z.inj_ge n m)) (compat "8.3").
Notation inj_gt_rev := (fun n m => proj2 (Nat2Z.inj_gt n m)) (compat "8.3").
Notation inj_plus := Nat2Z.inj_add (compat "8.3").
Notation inj_mult := Nat2Z.inj_mul (compat "8.3").
Notation inj_minus1 := Nat2Z.inj_sub (compat "8.3").
Notation inj_minus := Nat2Z.inj_sub_max (compat "8.3").
Notation inj_min := Nat2Z.inj_min (compat "8.3").
Notation inj_max := Nat2Z.inj_max (compat "8.3").

Notation Z_of_nat_of_P := positive_nat_Z (compat "8.3").
Notation Zpos_eq_Z_of_nat_o_nat_of_P :=
(fun p => eq_sym (positive_nat_Z p)) (compat "8.3").

Notation Z_of_nat_of_N := N_nat_Z (compat "8.3").
Notation Z_of_N_of_nat := nat_N_Z (compat "8.3").

Notation Z_of_N_eq := (f_equal Z.of_N) (compat "8.3").
Notation Z_of_N_eq_rev := N2Z.inj (compat "8.3").
Notation Z_of_N_eq_iff := (fun n m => iff_sym (N2Z.inj_iff n m)) (compat "8.3").
Notation Z_of_N_compare := N2Z.inj_compare (compat "8.3").
Notation Z_of_N_le_iff := N2Z.inj_le (compat "8.3").
Notation Z_of_N_lt_iff := N2Z.inj_lt (compat "8.3").
Notation Z_of_N_ge_iff := N2Z.inj_ge (compat "8.3").
Notation Z_of_N_gt_iff := N2Z.inj_gt (compat "8.3").
Notation Z_of_N_le := (fun n m => proj1 (N2Z.inj_le n m)) (compat "8.3").
Notation Z_of_N_lt := (fun n m => proj1 (N2Z.inj_lt n m)) (compat "8.3").
Notation Z_of_N_ge := (fun n m => proj1 (N2Z.inj_ge n m)) (compat "8.3").
Notation Z_of_N_gt := (fun n m => proj1 (N2Z.inj_gt n m)) (compat "8.3").
Notation Z_of_N_le_rev := (fun n m => proj2 (N2Z.inj_le n m)) (compat "8.3").
Notation Z_of_N_lt_rev := (fun n m => proj2 (N2Z.inj_lt n m)) (compat "8.3").
Notation Z_of_N_ge_rev := (fun n m => proj2 (N2Z.inj_ge n m)) (compat "8.3").
Notation Z_of_N_gt_rev := (fun n m => proj2 (N2Z.inj_gt n m)) (compat "8.3").
Notation Z_of_N_pos := N2Z.inj_pos (compat "8.3").
Notation Z_of_N_abs := N2Z.inj_abs_N (compat "8.3").
Notation Z_of_N_le_0 := N2Z.is_nonneg (compat "8.3").
Notation Z_of_N_plus := N2Z.inj_add (compat "8.3").
Notation Z_of_N_mult := N2Z.inj_mul (compat "8.3").
Notation Z_of_N_minus := N2Z.inj_sub_max (compat "8.3").
Notation Z_of_N_succ := N2Z.inj_succ (compat "8.3").
Notation Z_of_N_min := N2Z.inj_min (compat "8.3").
Notation Z_of_N_max := N2Z.inj_max (compat "8.3").
Notation Zabs_of_N := Zabs2N.id (compat "8.3").
Notation Zabs_N_succ_abs := Zabs2N.inj_succ_abs (compat "8.3").
Notation Zabs_N_succ := Zabs2N.inj_succ (compat "8.3").
Notation Zabs_N_plus_abs := Zabs2N.inj_add_abs (compat "8.3").
Notation Zabs_N_plus := Zabs2N.inj_add (compat "8.3").
Notation Zabs_N_mult_abs := Zabs2N.inj_mul_abs (compat "8.3").
Notation Zabs_N_mult := Zabs2N.inj_mul (compat "8.3").

Theorem inj_minus2 : forall n m:nat, (m > n)%nat -> Z.of_nat (n - m) = 0.
Proof. hammer_hook "Znat" "Znat.inj_minus2". Restart. 
intros. rewrite not_le_minus_0; auto with arith.
Qed.
