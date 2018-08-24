From Hammer Require Import Hammer.











Require Import NZAxioms NZBase NZAdd.

Module Type NZMulProp (Import NZ : NZAxiomsSig')(Import NZBase : NZBaseProp NZ).
Include NZAddProp NZ NZBase.

Theorem mul_0_r : forall n, n * 0 == 0.
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_0_r". Undo.  
nzinduct n; intros; now nzsimpl.
Qed.

Theorem mul_succ_r : forall n m, n * (S m) == n * m + n.
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_succ_r". Undo.  
intros n m; nzinduct n. now nzsimpl.
intro n. nzsimpl. rewrite succ_inj_wd, <- add_assoc, (add_comm m n), add_assoc.
now rewrite add_cancel_r.
Qed.

Hint Rewrite mul_0_r mul_succ_r : nz.

Theorem mul_comm : forall n m, n * m == m * n.
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_comm". Undo.  
intros n m; nzinduct n. now nzsimpl.
intro. nzsimpl. now rewrite add_cancel_r.
Qed.

Theorem mul_add_distr_r : forall n m p, (n + m) * p == n * p + m * p.
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_add_distr_r". Undo.  
intros n m p; nzinduct n. now nzsimpl.
intro n. nzsimpl. rewrite <- add_assoc, (add_comm p (m*p)), add_assoc.
now rewrite add_cancel_r.
Qed.

Theorem mul_add_distr_l : forall n m p, n * (m + p) == n * m + n * p.
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_add_distr_l". Undo.  
intros n m p.
rewrite (mul_comm n (m + p)), (mul_comm n m), (mul_comm n p).
apply mul_add_distr_r.
Qed.

Theorem mul_assoc : forall n m p, n * (m * p) == (n * m) * p.
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_assoc". Undo.  
intros n m p; nzinduct n. now nzsimpl.
intro n. nzsimpl. rewrite mul_add_distr_r.
now rewrite add_cancel_r.
Qed.

Theorem mul_1_l : forall n, 1 * n == n.
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_1_l". Undo.  
intro n. now nzsimpl'.
Qed.

Theorem mul_1_r : forall n, n * 1 == n.
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_1_r". Undo.  
intro n. now nzsimpl'.
Qed.

Hint Rewrite mul_1_l mul_1_r : nz.

Theorem mul_shuffle0 : forall n m p, n*m*p == n*p*m.
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_shuffle0". Undo.  
intros n m p. now rewrite <- 2 mul_assoc, (mul_comm m).
Qed.

Theorem mul_shuffle1 : forall n m p q, (n * m) * (p * q) == (n * p) * (m * q).
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_shuffle1". Undo.  
intros n m p q. now rewrite 2 mul_assoc, (mul_shuffle0 n).
Qed.

Theorem mul_shuffle2 : forall n m p q, (n * m) * (p * q) == (n * q) * (m * p).
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_shuffle2". Undo.  
intros n m p q. rewrite (mul_comm p). apply mul_shuffle1.
Qed.

Theorem mul_shuffle3 : forall n m p, n * (m * p) == m * (n * p).
Proof. try hammer_hook "NZMul" "NZMul.NZMulProp.mul_shuffle3". Undo.  
intros n m p. now rewrite mul_assoc, (mul_comm n), mul_assoc.
Qed.

End NZMulProp.
