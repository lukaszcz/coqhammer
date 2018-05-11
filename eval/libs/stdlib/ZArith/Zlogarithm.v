From Hammer Require Import Hammer.

















Require Import ZArith_base Omega Zcomplements Zpower.
Local Open Scope Z_scope.

Section Log_pos.



Fixpoint log_inf (p:positive) : Z :=
match p with
| xH => 0
| xO q => Z.succ (log_inf q)
| xI q => Z.succ (log_inf q)
end.

Fixpoint log_sup (p:positive) : Z :=
match p with
| xH => 0
| xO n => Z.succ (log_sup n)
| xI n => Z.succ (Z.succ (log_inf n))
end.

Hint Unfold log_inf log_sup.

Lemma Psize_log_inf : forall p, Zpos (Pos.size p) = Z.succ (log_inf p).
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.Psize_log_inf".  
induction p; simpl; now rewrite ?Pos2Z.inj_succ, ?IHp.
Qed.

Lemma Zlog2_log_inf : forall p, Z.log2 (Zpos p) = log_inf p.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.Zlog2_log_inf".  
unfold Z.log2. destruct p; simpl; trivial; apply Psize_log_inf.
Qed.

Lemma Zlog2_up_log_sup : forall p, Z.log2_up (Zpos p) = log_sup p.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.Zlog2_up_log_sup".  
induction p; simpl log_sup.
- change (Zpos p~1) with (2*(Zpos p)+1).
rewrite Z.log2_up_succ_double, Zlog2_log_inf; try easy.
unfold Z.succ. now rewrite !(Z.add_comm _ 1), Z.add_assoc.
- change (Zpos p~0) with (2*Zpos p).
now rewrite Z.log2_up_double, IHp.
- reflexivity.
Qed.



Hint Resolve Z.le_trans: zarith.

Theorem log_inf_correct :
forall x:positive,
0 <= log_inf x /\ two_p (log_inf x) <= Zpos x < two_p (Z.succ (log_inf x)).
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_inf_correct".  
simple induction x; intros; simpl;
[ elim H; intros Hp HR; clear H; split;
[ auto with zarith
| rewrite two_p_S with (x := Z.succ (log_inf p)) by (apply Z.le_le_succ_r; trivial);
rewrite two_p_S by trivial;
rewrite two_p_S in HR by trivial; rewrite (BinInt.Pos2Z.inj_xI p);
omega ]
| elim H; intros Hp HR; clear H; split;
[ auto with zarith
| rewrite two_p_S with (x := Z.succ (log_inf p)) by (apply Z.le_le_succ_r; trivial);
rewrite two_p_S by trivial;
rewrite two_p_S in HR by trivial; rewrite (BinInt.Pos2Z.inj_xO p);
omega ]
| unfold two_power_pos; unfold shift_pos; simpl;
omega ].
Qed.

Definition log_inf_correct1 (p:positive) := proj1 (log_inf_correct p).
Definition log_inf_correct2 (p:positive) := proj2 (log_inf_correct p).

Opaque log_inf_correct1 log_inf_correct2.

Hint Resolve log_inf_correct1 log_inf_correct2: zarith.

Lemma log_sup_correct1 : forall p:positive, 0 <= log_sup p.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_sup_correct1".  
simple induction p; intros; simpl; auto with zarith.
Qed.



Theorem log_sup_log_inf :
forall p:positive,
IF Zpos p = two_p (log_inf p) then Zpos p = two_p (log_sup p)
else log_sup p = Z.succ (log_inf p).
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_sup_log_inf".  
simple induction p; intros;
[ elim H; right; simpl;
rewrite (two_p_S (log_inf p0) (log_inf_correct1 p0));
rewrite BinInt.Pos2Z.inj_xI; unfold Z.succ; omega
| elim H; clear H; intro Hif;
[ left; simpl;
rewrite (two_p_S (log_inf p0) (log_inf_correct1 p0));
rewrite (two_p_S (log_sup p0) (log_sup_correct1 p0));
rewrite <- (proj1 Hif); rewrite <- (proj2 Hif);
auto
| right; simpl;
rewrite (two_p_S (log_inf p0) (log_inf_correct1 p0));
rewrite BinInt.Pos2Z.inj_xO; unfold Z.succ;
omega ]
| left; auto ].
Qed.

Theorem log_sup_correct2 :
forall x:positive, two_p (Z.pred (log_sup x)) < Zpos x <= two_p (log_sup x).
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_sup_correct2".  
intro.
elim (log_sup_log_inf x).

intros [E1 E2]; rewrite E2.
split; [ apply two_p_pred; apply log_sup_correct1 | apply Z.le_refl ].
intros [E1 E2]; rewrite E2.
rewrite (Z.pred_succ (log_inf x)).
generalize (log_inf_correct2 x); omega.
Qed.

Lemma log_inf_le_log_sup : forall p:positive, log_inf p <= log_sup p.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_inf_le_log_sup".  
simple induction p; simpl; intros; omega.
Qed.

Lemma log_sup_le_Slog_inf : forall p:positive, log_sup p <= Z.succ (log_inf p).
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_sup_le_Slog_inf".  
simple induction p; simpl; intros; omega.
Qed.



Fixpoint log_near (x:positive) : Z :=
match x with
| xH => 0
| xO xH => 1
| xI xH => 2
| xO y => Z.succ (log_near y)
| xI y => Z.succ (log_near y)
end.

Theorem log_near_correct1 : forall p:positive, 0 <= log_near p.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_near_correct1".  
simple induction p; simpl; intros;
[ elim p0; auto with zarith
| elim p0; auto with zarith
| trivial with zarith ].
intros; apply Z.le_le_succ_r.
generalize H0; now elim p1.
intros; apply Z.le_le_succ_r.
generalize H0; now elim p1.
Qed.

Theorem log_near_correct2 :
forall p:positive, log_near p = log_inf p \/ log_near p = log_sup p.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_near_correct2".  
simple induction p.
intros p0 [Einf| Esup].
simpl. rewrite Einf.
case p0; [ left | left | right ]; reflexivity.
simpl; rewrite Esup.
elim (log_sup_log_inf p0).
generalize (log_inf_le_log_sup p0).
generalize (log_sup_le_Slog_inf p0).
case p0; auto with zarith.
intros; omega.
case p0; intros; auto with zarith.
intros p0 [Einf| Esup].
simpl.
repeat rewrite Einf.
case p0; intros; auto with zarith.
simpl.
repeat rewrite Esup.
case p0; intros; auto with zarith.
auto.
Qed.

End Log_pos.

Section divers.



Definition N_digits (x:Z) :=
match x with
| Zpos p => log_inf p
| Zneg p => log_inf p
| Z0 => 0
end.

Lemma ZERO_le_N_digits : forall x:Z, 0 <= N_digits x.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.ZERO_le_N_digits".  
simple induction x; simpl;
[ apply Z.le_refl | exact log_inf_correct1 | exact log_inf_correct1 ].
Qed.

Lemma log_inf_shift_nat : forall n:nat, log_inf (shift_nat n 1) = Z.of_nat n.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_inf_shift_nat".  
simple induction n; intros;
[ try trivial | rewrite Nat2Z.inj_succ; rewrite <- H; reflexivity ].
Qed.

Lemma log_sup_shift_nat : forall n:nat, log_sup (shift_nat n 1) = Z.of_nat n.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.log_sup_shift_nat".  
simple induction n; intros;
[ try trivial | rewrite Nat2Z.inj_succ; rewrite <- H; reflexivity ].
Qed.


Fixpoint Is_power (p:positive) : Prop :=
match p with
| xH => True
| xO q => Is_power q
| xI q => False
end.

Lemma Is_power_correct :
forall p:positive, Is_power p <-> (exists y : nat, p = shift_nat y 1).
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.Is_power_correct".  
split;
[ elim p;
[ simpl; tauto
| simpl; intros; generalize (H H0); intro H1; elim H1;
intros y0 Hy0; exists (S y0); rewrite Hy0; reflexivity
| intro; exists 0%nat; reflexivity ]
| intros; elim H; intros; rewrite H0; elim x; intros; simpl; trivial ].
Qed.

Lemma Is_power_or : forall p:positive, Is_power p \/ ~ Is_power p.
Proof. try hammer_hook "Zlogarithm" "Zlogarithm.Is_power_or".  
simple induction p;
[ intros; right; simpl; tauto
| intros; elim H;
[ intros; left; simpl; exact H0
| intros; right; simpl; exact H0 ]
| left; simpl; trivial ].
Qed.

End divers.






