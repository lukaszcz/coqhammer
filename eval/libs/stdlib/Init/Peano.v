From Hammer Require Import Hammer.













Require Import Notations.
Require Import Datatypes.
Require Import Logic.
Require Coq.Init.Nat.

Open Scope nat_scope.

Definition eq_S := f_equal S.
Definition f_equal_nat := f_equal (A:=nat).

Hint Resolve f_equal_nat: core.



Notation pred := Nat.pred (compat "8.4").

Definition f_equal_pred := f_equal pred.

Theorem pred_Sn : forall n:nat, n = pred (S n).
Proof. hammer_hook "Peano" "Peano.pred_Sn". Restart. 
simpl; reflexivity.
Qed.



Definition eq_add_S n m (H: S n = S m): n = m := f_equal pred H.
Hint Immediate eq_add_S: core.

Theorem not_eq_S : forall n m:nat, n <> m -> S n <> S m.
Proof. hammer_hook "Peano" "Peano.not_eq_S". Restart. 
red; auto.
Qed.
Hint Resolve not_eq_S: core.

Definition IsSucc (n:nat) : Prop :=
match n with
| O => False
| S p => True
end.



Theorem O_S : forall n:nat, 0 <> S n.
Proof. hammer_hook "Peano" "Peano.O_S". Restart. 
discriminate.
Qed.
Hint Resolve O_S: core.

Theorem n_Sn : forall n:nat, n <> S n.
Proof. hammer_hook "Peano" "Peano.n_Sn". Restart. 
induction n; auto.
Qed.
Hint Resolve n_Sn: core.



Notation plus := Nat.add (compat "8.4").
Infix "+" := Nat.add : nat_scope.

Definition f_equal2_plus := f_equal2 plus.
Definition f_equal2_nat := f_equal2 (A1:=nat) (A2:=nat).
Hint Resolve f_equal2_nat: core.

Lemma plus_n_O : forall n:nat, n = n + 0.
Proof. hammer_hook "Peano" "Peano.plus_n_O". Restart. 
induction n; simpl; auto.
Qed.
Hint Resolve plus_n_O: core.

Lemma plus_O_n : forall n:nat, 0 + n = n.
Proof. hammer_hook "Peano" "Peano.plus_O_n". Restart. 
reflexivity.
Qed.

Lemma plus_n_Sm : forall n m:nat, S (n + m) = n + S m.
Proof. hammer_hook "Peano" "Peano.plus_n_Sm". Restart. 
intros n m; induction n; simpl; auto.
Qed.
Hint Resolve plus_n_Sm: core.

Lemma plus_Sn_m : forall n m:nat, S n + m = S (n + m).
Proof. hammer_hook "Peano" "Peano.plus_Sn_m". Restart. 
reflexivity.
Qed.



Notation plus_0_r_reverse := plus_n_O (compat "8.2").
Notation plus_succ_r_reverse := plus_n_Sm (compat "8.2").



Notation mult := Nat.mul (compat "8.4").
Infix "*" := Nat.mul : nat_scope.

Definition f_equal2_mult := f_equal2 mult.
Hint Resolve f_equal2_mult: core.

Lemma mult_n_O : forall n:nat, 0 = n * 0.
Proof. hammer_hook "Peano" "Peano.mult_n_O". Restart. 
induction n; simpl; auto.
Qed.
Hint Resolve mult_n_O: core.

Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof. hammer_hook "Peano" "Peano.mult_n_Sm". Restart. 
intros; induction n as [| p H]; simpl; auto.
destruct H; rewrite <- plus_n_Sm; apply eq_S.
pattern m at 1 3; elim m; simpl; auto.
Qed.
Hint Resolve mult_n_Sm: core.



Notation mult_0_r_reverse := mult_n_O (compat "8.2").
Notation mult_succ_r_reverse := mult_n_Sm (compat "8.2").



Notation minus := Nat.sub (compat "8.4").
Infix "-" := Nat.sub : nat_scope.



Inductive le (n:nat) : nat -> Prop :=
| le_n : n <= n
| le_S : forall m:nat, n <= m -> n <= S m

where "n <= m" := (le n m) : nat_scope.

Hint Constructors le: core.


Definition lt (n m:nat) := S n <= m.
Hint Unfold lt: core.

Infix "<" := lt : nat_scope.

Definition ge (n m:nat) := m <= n.
Hint Unfold ge: core.

Infix ">=" := ge : nat_scope.

Definition gt (n m:nat) := m < n.
Hint Unfold gt: core.

Infix ">" := gt : nat_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : nat_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : nat_scope.
Notation "x < y < z" := (x < y /\ y < z) : nat_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : nat_scope.

Theorem le_pred : forall n m, n <= m -> pred n <= pred m.
Proof. hammer_hook "Peano" "Peano.le_pred". Restart. 
induction 1; auto. destruct m; simpl; auto.
Qed.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof. hammer_hook "Peano" "Peano.le_S_n". Restart. 
intros n m. exact (le_pred (S n) (S m)).
Qed.

Theorem le_0_n : forall n, 0 <= n.
Proof. hammer_hook "Peano" "Peano.le_0_n". Restart. 
induction n; constructor; trivial.
Qed.

Theorem le_n_S : forall n m, n <= m -> S n <= S m.
Proof. hammer_hook "Peano" "Peano.le_n_S". Restart. 
induction 1; constructor; trivial.
Qed.



Theorem nat_case :
forall (n:nat) (P:nat -> Prop), P 0 -> (forall m:nat, P (S m)) -> P n.
Proof. hammer_hook "Peano" "Peano.nat_case". Restart. 
induction n; auto.
Qed.



Theorem nat_double_ind :
forall R:nat -> nat -> Prop,
(forall n:nat, R 0 n) ->
(forall n:nat, R (S n) 0) ->
(forall n m:nat, R n m -> R (S n) (S m)) -> forall n m:nat, R n m.
Proof. hammer_hook "Peano" "Peano.nat_double_ind". Restart. 
induction n; auto.
destruct m; auto.
Qed.



Notation max := Nat.max (compat "8.4").
Notation min := Nat.min (compat "8.4").

Lemma max_l n m : m <= n -> Nat.max n m = n.
Proof. hammer_hook "Peano" "Peano.max_l". Restart. 
revert m; induction n; destruct m; simpl; trivial.
- inversion 1.
- intros. apply f_equal, IHn, le_S_n; trivial.
Qed.

Lemma max_r n m : n <= m -> Nat.max n m = m.
Proof. hammer_hook "Peano" "Peano.max_r". Restart. 
revert m; induction n; destruct m; simpl; trivial.
- inversion 1.
- intros. apply f_equal, IHn, le_S_n; trivial.
Qed.

Lemma min_l n m : n <= m -> Nat.min n m = n.
Proof. hammer_hook "Peano" "Peano.min_l". Restart. 
revert m; induction n; destruct m; simpl; trivial.
- inversion 1.
- intros. apply f_equal, IHn, le_S_n; trivial.
Qed.

Lemma min_r n m : m <= n -> Nat.min n m = m.
Proof. hammer_hook "Peano" "Peano.min_r". Restart. 
revert m; induction n; destruct m; simpl; trivial.
- inversion 1.
- intros. apply f_equal, IHn, le_S_n; trivial.
Qed.


Lemma nat_rect_succ_r {A} (f: A -> A) (x:A) n :
nat_rect (fun _ => A) x (fun _ => f) (S n) = nat_rect (fun _ => A) (f x) (fun _ => f) n.
Proof. hammer_hook "Peano" "Peano.nat_rect_succ_r". Restart. 
induction n; intros; simpl; rewrite <- ?IHn; trivial.
Qed.

Theorem nat_rect_plus :
forall (n m:nat) {A} (f:A -> A) (x:A),
nat_rect (fun _ => A) x (fun _ => f) (n + m) =
nat_rect (fun _ => A) (nat_rect (fun _ => A) x (fun _ => f) m) (fun _ => f) n.
Proof. hammer_hook "Peano" "Peano.nat_rect_plus". Restart. 
induction n; intros; simpl; rewrite ?IHn; trivial.
Qed.
