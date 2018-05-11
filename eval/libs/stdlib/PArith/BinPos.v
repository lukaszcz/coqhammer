From Hammer Require Import Hammer.










Require Export BinNums.
Require Import Eqdep_dec EqdepFacts RelationClasses Morphisms Setoid
Equalities Orders OrdersFacts GenericMinMax Le Plus.

Require Export BinPosDef.









Local Open Scope positive_scope.



Module Pos
<: UsualOrderedTypeFull
<: UsualDecidableTypeFull
<: TotalOrder.



Include BinPosDef.Pos.



Set Inline Level 30.



Definition eq := @Logic.eq positive.
Definition eq_equiv := @eq_equivalence positive.
Include BackportEq.

Definition lt x y := (x ?= y) = Lt.
Definition gt x y := (x ?= y) = Gt.
Definition le x y := (x ?= y) <> Gt.
Definition ge x y := (x ?= y) <> Lt.

Infix "<=" := le : positive_scope.
Infix "<" := lt : positive_scope.
Infix ">=" := ge : positive_scope.
Infix ">" := gt : positive_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : positive_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : positive_scope.
Notation "x < y < z" := (x < y /\ y < z) : positive_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : positive_scope.






Lemma eq_dec : forall x y:positive, {x = y} + {x <> y}.
Proof. try hammer_hook "BinPos" "BinPos.Pos.eq_dec".  
decide equality.
Defined.






Lemma xI_succ_xO p : p~1 = succ p~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.xI_succ_xO".  
reflexivity.
Qed.

Lemma succ_discr p : p <> succ p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_discr".  
now destruct p.
Qed.



Lemma pred_double_spec p : pred_double p = pred (p~0).
Proof. try hammer_hook "BinPos" "BinPos.Pos.pred_double_spec".  
reflexivity.
Qed.

Lemma succ_pred_double p : succ (pred_double p) = p~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_pred_double".  
induction p; simpl; now f_equal.
Qed.

Lemma pred_double_succ p : pred_double (succ p) = p~1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.pred_double_succ".  
induction p; simpl; now f_equal.
Qed.

Lemma double_succ p : (succ p)~0 = succ (succ p~0).
Proof. try hammer_hook "BinPos" "BinPos.Pos.double_succ".  
now destruct p.
Qed.

Lemma pred_double_xO_discr p : pred_double p <> p~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.pred_double_xO_discr".  
now destruct p.
Qed.



Lemma succ_not_1 p : succ p <> 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_not_1".  
now destruct p.
Qed.

Lemma pred_succ p : pred (succ p) = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.pred_succ".  
destruct p; simpl; trivial. apply pred_double_succ.
Qed.

Lemma succ_pred_or p : p = 1 \/ succ (pred p) = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_pred_or".  
destruct p; simpl; auto.
right; apply succ_pred_double.
Qed.

Lemma succ_pred p : p <> 1 -> succ (pred p) = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_pred".  
destruct p; intros H; simpl; trivial.
apply succ_pred_double.
now destruct H.
Qed.



Lemma succ_inj p q : succ p = succ q -> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_inj".  
revert q.
induction p; intros [q|q| ] H; simpl in H; destr_eq H; f_equal; auto.
elim (succ_not_1 p); auto.
elim (succ_not_1 q); auto.
Qed.



Lemma pred_N_succ p : pred_N (succ p) = Npos p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.pred_N_succ".  
destruct p; simpl; trivial. f_equal. apply pred_double_succ.
Qed.







Lemma add_1_r p : p + 1 = succ p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_1_r".  
now destruct p.
Qed.

Lemma add_1_l p : 1 + p = succ p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_1_l".  
now destruct p.
Qed.



Theorem add_carry_spec p q : add_carry p q = succ (p + q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_carry_spec".  
revert q. induction p; destruct q; simpl; now f_equal.
Qed.



Theorem add_comm p q : p + q = q + p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_comm".  
revert q. induction p; destruct q; simpl; f_equal; trivial.
rewrite 2 add_carry_spec; now f_equal.
Qed.



Theorem add_succ_r p q : p + succ q = succ (p + q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_succ_r".  
revert q.
induction p; destruct q; simpl; f_equal;
auto using add_1_r; rewrite add_carry_spec; auto.
Qed.

Theorem add_succ_l p q : succ p + q = succ (p + q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_succ_l".  
rewrite add_comm, (add_comm p). apply add_succ_r.
Qed.


Lemma add_no_neutral p q : q + p <> p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_no_neutral".  
revert q.
induction p as [p IHp|p IHp| ]; intros [q|q| ] H;
destr_eq H; apply (IHp q H).
Qed.



Lemma add_carry_add p q r s :
add_carry p r = add_carry q s -> p + r = q + s.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_carry_add".  
intros H; apply succ_inj; now rewrite <- 2 add_carry_spec.
Qed.

Lemma add_reg_r p q r : p + r = q + r -> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_reg_r".  
revert p q. induction r.
intros [p|p| ] [q|q| ] H; simpl; destr_eq H; f_equal;
auto using add_carry_add; contradict H;
rewrite add_carry_spec, <- add_succ_r; auto using add_no_neutral.
intros [p|p| ] [q|q| ] H; simpl; destr_eq H; f_equal; auto;
contradict H; auto using add_no_neutral.
intros p q H. apply succ_inj. now rewrite <- 2 add_1_r.
Qed.

Lemma add_reg_l p q r : p + q = p + r -> q = r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_reg_l".  
rewrite 2 (add_comm p). now apply add_reg_r.
Qed.

Lemma add_cancel_r p q r : p + r = q + r <-> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_cancel_r".  
split. apply add_reg_r. congruence.
Qed.

Lemma add_cancel_l p q r : r + p = r + q <-> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_cancel_l".  
split. apply add_reg_l. congruence.
Qed.

Lemma add_carry_reg_r p q r :
add_carry p r = add_carry q r -> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_carry_reg_r".  
intros H. apply add_reg_r with (r:=r); now apply add_carry_add.
Qed.

Lemma add_carry_reg_l p q r :
add_carry p q = add_carry p r -> q = r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_carry_reg_l".  
intros H; apply add_reg_r with (r:=p);
rewrite (add_comm r), (add_comm q); now apply add_carry_add.
Qed.



Theorem add_assoc p q r : p + (q + r) = p + q + r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_assoc".  
revert q r. induction p.
intros [q|q| ] [r|r| ]; simpl; f_equal; trivial;
rewrite ?add_carry_spec, ?add_succ_r, ?add_succ_l, ?add_1_r;
f_equal; trivial.
intros [q|q| ] [r|r| ]; simpl; f_equal; trivial;
rewrite ?add_carry_spec, ?add_succ_r, ?add_succ_l, ?add_1_r;
f_equal; trivial.
intros q r; rewrite 2 add_1_l, add_succ_l; auto.
Qed.



Lemma add_xO p q : (p + q)~0 = p~0 + q~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_xO".  
now destruct p, q.
Qed.

Lemma add_xI_pred_double p q :
(p + q)~0 = p~1 + pred_double q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_xI_pred_double".  
change (p~1) with (p~0 + 1).
now rewrite <- add_assoc, add_1_l, succ_pred_double.
Qed.

Lemma add_xO_pred_double p q :
pred_double (p + q) = p~0 + pred_double q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_xO_pred_double".  
revert q. induction p as [p IHp| p IHp| ]; destruct q; simpl;
rewrite ?add_carry_spec, ?pred_double_succ, ?add_xI_pred_double;
try reflexivity.
rewrite IHp; auto.
rewrite <- succ_pred_double, <- add_1_l. reflexivity.
Qed.



Lemma add_diag p : p + p = p~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_diag".  
induction p as [p IHp| p IHp| ]; simpl;
now rewrite ?add_carry_spec, ?IHp.
Qed.






Fixpoint peano_rect (P:positive->Type) (a:P 1)
(f: forall p:positive, P p -> P (succ p)) (p:positive) : P p :=
let f2 := peano_rect (fun p:positive => P (p~0)) (f _ a)
(fun (p:positive) (x:P (p~0)) => f _ (f _ x))
in
match p with
| q~1 => f _ (f2 q)
| q~0 => f2 q
| 1 => a
end.

Theorem peano_rect_succ (P:positive->Type) (a:P 1)
(f:forall p, P p -> P (succ p)) (p:positive) :
peano_rect P a f (succ p) = f _ (peano_rect P a f p).
Proof. try hammer_hook "BinPos" "BinPos.Pos.peano_rect_succ".  
revert P a f. induction p; trivial.
intros. simpl. now rewrite IHp.
Qed.

Theorem peano_rect_base (P:positive->Type) (a:P 1)
(f:forall p, P p -> P (succ p)) :
peano_rect P a f 1 = a.
Proof. try hammer_hook "BinPos" "BinPos.Pos.peano_rect_base".  
trivial.
Qed.

Definition peano_rec (P:positive->Set) := peano_rect P.



Definition peano_ind (P:positive->Prop) := peano_rect P.



Theorem peano_case :
forall P:positive -> Prop,
P 1 -> (forall n:positive, P (succ n)) -> forall p:positive, P p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.peano_case".  
intros; apply peano_ind; auto.
Qed.



Inductive PeanoView : positive -> Type :=
| PeanoOne : PeanoView 1
| PeanoSucc : forall p, PeanoView p -> PeanoView (succ p).

Fixpoint peanoView_xO p (q:PeanoView p) : PeanoView (p~0) :=
match q in PeanoView x return PeanoView (x~0) with
| PeanoOne => PeanoSucc _ PeanoOne
| PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xO _ q))
end.

Fixpoint peanoView_xI p (q:PeanoView p) : PeanoView (p~1) :=
match q in PeanoView x return PeanoView (x~1) with
| PeanoOne => PeanoSucc _ (PeanoSucc _ PeanoOne)
| PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xI _ q))
end.

Fixpoint peanoView p : PeanoView p :=
match p return PeanoView p with
| 1 => PeanoOne
| p~0 => peanoView_xO p (peanoView p)
| p~1 => peanoView_xI p (peanoView p)
end.

Definition PeanoView_iter (P:positive->Type)
(a:P 1) (f:forall p, P p -> P (succ p)) :=
(fix iter p (q:PeanoView p) : P p :=
match q in PeanoView p return P p with
| PeanoOne => a
| PeanoSucc _ q => f _ (iter _ q)
end).

Theorem eq_dep_eq_positive :
forall (P:positive->Type) (p:positive) (x y:P p),
eq_dep positive P p x p y -> x = y.
Proof. try hammer_hook "BinPos" "BinPos.Pos.eq_dep_eq_positive".  
apply eq_dep_eq_dec.
decide equality.
Qed.

Theorem PeanoViewUnique : forall p (q q':PeanoView p), q = q'.
Proof. try hammer_hook "BinPos" "BinPos.Pos.PeanoViewUnique".  
intros.
induction q as [ | p q IHq ].
apply eq_dep_eq_positive.
cut (1=1). pattern 1 at 1 2 5, q'. destruct q'. trivial.
destruct p; intros; discriminate.
trivial.
apply eq_dep_eq_positive.
cut (succ p=succ p). pattern (succ p) at 1 2 5, q'. destruct q'.
intro. destruct p; discriminate.
intro. apply succ_inj in H.
generalize q'. rewrite H. intro.
rewrite (IHq q'0).
trivial.
trivial.
Qed.

Lemma peano_equiv (P:positive->Type) (a:P 1) (f:forall p, P p -> P (succ p)) p :
PeanoView_iter P a f p (peanoView p) = peano_rect P a f p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.peano_equiv".  
revert P a f. induction p using peano_rect.
trivial.
intros; simpl. rewrite peano_rect_succ.
rewrite (PeanoViewUnique _ (peanoView (succ p)) (PeanoSucc _ (peanoView p))).
simpl; now f_equal.
Qed.






Lemma mul_1_l p : 1 * p = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_1_l".  
reflexivity.
Qed.

Lemma mul_1_r p : p * 1 = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_1_r".  
induction p; simpl; now f_equal.
Qed.



Lemma mul_xO_r p q : p * q~0 = (p * q)~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_xO_r".  
induction p; simpl; f_equal; f_equal; trivial.
Qed.

Lemma mul_xI_r p q : p * q~1 = p + (p * q)~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_xI_r".  
induction p as [p IHp|p IHp| ]; simpl; f_equal; trivial.
now rewrite IHp, 2 add_assoc, (add_comm p).
Qed.



Theorem mul_comm p q : p * q = q * p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_comm".  
induction q as [q IHq|q IHq| ]; simpl; rewrite <- ? IHq;
auto using mul_xI_r, mul_xO_r, mul_1_r.
Qed.



Theorem mul_add_distr_l p q r :
p * (q + r) = p * q + p * r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_add_distr_l".  
induction p as [p IHp|p IHp| ]; simpl.
rewrite IHp. set (m:=(p*q)~0). set (n:=(p*r)~0).
change ((p*q+p*r)~0) with (m+n).
rewrite 2 add_assoc; f_equal.
rewrite <- 2 add_assoc; f_equal.
apply add_comm.
f_equal; auto.
reflexivity.
Qed.

Theorem mul_add_distr_r p q r :
(p + q) * r = p * r + q * r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_add_distr_r".  
rewrite 3 (mul_comm _ r); apply mul_add_distr_l.
Qed.



Theorem mul_assoc p q r : p * (q * r) = p * q * r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_assoc".  
induction p as [p IHp| p IHp | ]; simpl; rewrite ?IHp; trivial.
now rewrite mul_add_distr_r.
Qed.



Lemma mul_succ_l p q : (succ p) * q = q + p * q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_succ_l".  
induction p as [p IHp | p IHp | ]; simpl; trivial.
now rewrite IHp, add_assoc, add_diag, <-add_xO.
symmetry; apply add_diag.
Qed.

Lemma mul_succ_r p q : p * (succ q) = p + p * q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_succ_r".  
rewrite mul_comm, mul_succ_l. f_equal. apply mul_comm.
Qed.



Lemma mul_xI_mul_xO_discr p q r : p~1 * r <> q~0 * r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_xI_mul_xO_discr".  
induction r; try discriminate.
rewrite 2 mul_xO_r; intro H; destr_eq H; auto.
Qed.

Lemma mul_xO_discr p q : p~0 * q <> q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_xO_discr".  
induction q; try discriminate.
rewrite mul_xO_r; injection; auto.
Qed.



Theorem mul_reg_r p q r : p * r = q * r -> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_reg_r".  
revert q r.
induction p as [p IHp| p IHp| ]; intros [q|q| ] r H;
reflexivity || apply f_equal || exfalso.
apply IHp with (r~0). simpl in *.
rewrite 2 mul_xO_r. apply add_reg_l with (1:=H).
contradict H. apply mul_xI_mul_xO_discr.
contradict H. simpl. rewrite add_comm. apply add_no_neutral.
symmetry in H. contradict H. apply mul_xI_mul_xO_discr.
apply IHp with (r~0). simpl. now rewrite 2 mul_xO_r.
contradict H. apply mul_xO_discr.
symmetry in H. contradict H. simpl. rewrite add_comm.
apply add_no_neutral.
symmetry in H. contradict H. apply mul_xO_discr.
Qed.

Theorem mul_reg_l p q r : r * p = r * q -> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_reg_l".  
rewrite 2 (mul_comm r). apply mul_reg_r.
Qed.

Lemma mul_cancel_r p q r : p * r = q * r <-> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_cancel_r".  
split. apply mul_reg_r. congruence.
Qed.

Lemma mul_cancel_l p q r : r * p = r * q <-> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_cancel_l".  
split. apply mul_reg_l. congruence.
Qed.



Lemma mul_eq_1_l p q : p * q = 1 -> p = 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_eq_1_l".  
now destruct p, q.
Qed.

Lemma mul_eq_1_r p q : p * q = 1 -> q = 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_eq_1_r".  
now destruct p, q.
Qed.

Notation mul_eq_1 := mul_eq_1_l.



Lemma square_xO p : p~0 * p~0 = (p*p)~0~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.square_xO".  
simpl. now rewrite mul_comm.
Qed.

Lemma square_xI p : p~1 * p~1 = (p*p+p)~0~1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.square_xI".  
simpl. rewrite mul_comm. simpl. f_equal.
rewrite add_assoc, add_diag. simpl. now rewrite add_comm.
Qed.



Lemma iter_swap_gen : forall A B (f:A->B)(g:A->A)(h:B->B),
(forall a, f (g a) = h (f a)) -> forall p a,
f (iter g a p) = iter h (f a) p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.iter_swap_gen".  
induction p; simpl; intros; now rewrite ?H, ?IHp.
Qed.

Theorem iter_swap :
forall p (A:Type) (f:A -> A) (x:A),
iter f (f x) p = f (iter f x p).
Proof. try hammer_hook "BinPos" "BinPos.Pos.iter_swap".  
intros. symmetry. now apply iter_swap_gen.
Qed.

Theorem iter_succ :
forall p (A:Type) (f:A -> A) (x:A),
iter f x (succ p) = f (iter f x p).
Proof. try hammer_hook "BinPos" "BinPos.Pos.iter_succ".  
induction p as [p IHp|p IHp|]; intros; simpl; trivial.
now rewrite !IHp, iter_swap.
Qed.

Theorem iter_add :
forall p q (A:Type) (f:A -> A) (x:A),
iter f x (p+q) = iter f (iter f x q) p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.iter_add".  
induction p using peano_ind; intros.
now rewrite add_1_l, iter_succ.
now rewrite add_succ_l, !iter_succ, IHp.
Qed.

Theorem iter_invariant :
forall (p:positive) (A:Type) (f:A -> A) (Inv:A -> Prop),
(forall x:A, Inv x -> Inv (f x)) ->
forall x:A, Inv x -> Inv (iter f x p).
Proof. try hammer_hook "BinPos" "BinPos.Pos.iter_invariant".  
induction p as [p IHp|p IHp|]; simpl; trivial.
intros A f Inv H x H0. apply H, IHp, IHp; trivial.
intros A f Inv H x H0. apply IHp, IHp; trivial.
Qed.



Lemma pow_1_r p : p^1 = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.pow_1_r".  
unfold pow. simpl. now rewrite mul_comm.
Qed.

Lemma pow_succ_r p q : p^(succ q) = p * p^q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.pow_succ_r".  
unfold pow. now rewrite iter_succ.
Qed.



Lemma square_spec p : square p = p * p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.square_spec".  
induction p.
- rewrite square_xI. simpl. now rewrite IHp.
- rewrite square_xO. simpl. now rewrite IHp.
- trivial.
Qed.



Lemma sub_mask_succ_r p q :
sub_mask p (succ q) = sub_mask_carry p q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_succ_r".  
revert q. induction p; destruct q; simpl; f_equal; trivial; now destruct p.
Qed.

Theorem sub_mask_carry_spec p q :
sub_mask_carry p q = pred_mask (sub_mask p q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_carry_spec".  
revert q. induction p as [p IHp|p IHp| ]; destruct q; simpl;
try reflexivity; rewrite ?IHp;
destruct (sub_mask p q) as [|[r|r| ]|] || destruct p; auto.
Qed.

Inductive SubMaskSpec (p q : positive) : mask -> Prop :=
| SubIsNul : p = q -> SubMaskSpec p q IsNul
| SubIsPos : forall r, q + r = p -> SubMaskSpec p q (IsPos r)
| SubIsNeg : forall r, p + r = q -> SubMaskSpec p q IsNeg.

Theorem sub_mask_spec p q : SubMaskSpec p q (sub_mask p q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_spec".  
revert q. induction p; destruct q; simpl; try constructor; trivial.

destruct (IHp q); subst; try now constructor.
now apply SubIsNeg with r~0.

destruct (IHp q); subst; try now constructor.
apply SubIsNeg with (pred_double r). symmetry. apply add_xI_pred_double.

rewrite sub_mask_carry_spec.
destruct (IHp q); subst; try constructor.
now apply SubIsNeg with 1.
destruct r; simpl; try constructor; simpl.
now rewrite add_carry_spec, <- add_succ_r.
now rewrite add_carry_spec, <- add_succ_r, succ_pred_double.
now rewrite add_1_r.
now apply SubIsNeg with r~1.

destruct (IHp q); subst; try now constructor.
now apply SubIsNeg with r~0.

now rewrite add_1_l, succ_pred_double.

now apply SubIsNeg with q~0.

apply SubIsNeg with (pred_double q). now rewrite add_1_l, succ_pred_double.
Qed.

Theorem sub_mask_nul_iff p q : sub_mask p q = IsNul <-> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_nul_iff".  
split.
now case sub_mask_spec.
intros <-. induction p; simpl; now rewrite ?IHp.
Qed.

Theorem sub_mask_diag p : sub_mask p p = IsNul.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_diag".  
now apply sub_mask_nul_iff.
Qed.

Lemma sub_mask_add p q r : sub_mask p q = IsPos r -> q + r = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_add".  
case sub_mask_spec; congruence.
Qed.

Lemma sub_mask_add_diag_l p q : sub_mask (p+q) p = IsPos q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_add_diag_l".  
case sub_mask_spec.
intros H. rewrite add_comm in H. elim (add_no_neutral _ _ H).
intros r H. apply add_cancel_l in H. now f_equal.
intros r H. rewrite <- add_assoc, add_comm in H. elim (add_no_neutral _ _ H).
Qed.

Lemma sub_mask_pos_iff p q r : sub_mask p q = IsPos r <-> q + r = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_pos_iff".  
split. apply sub_mask_add. intros <-; apply sub_mask_add_diag_l.
Qed.

Lemma sub_mask_add_diag_r p q : sub_mask p (p+q) = IsNeg.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_add_diag_r".  
case sub_mask_spec; trivial.
intros H. symmetry in H; rewrite add_comm in H. elim (add_no_neutral _ _ H).
intros r H. rewrite <- add_assoc, add_comm in H. elim (add_no_neutral _ _ H).
Qed.

Lemma sub_mask_neg_iff p q : sub_mask p q = IsNeg <-> exists r, p + r = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_neg_iff".  
split.
case sub_mask_spec; try discriminate. intros r Hr _; now exists r.
intros (r,<-). apply sub_mask_add_diag_r.
Qed.




Theorem eqb_eq p q : (p =? q) = true <-> p=q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.eqb_eq".  
revert q. induction p; destruct q; simpl; rewrite ?IHp; split; congruence.
Qed.

Theorem ltb_lt p q : (p <? q) = true <-> p < q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.ltb_lt".  
unfold ltb, lt. destruct compare; easy'.
Qed.

Theorem leb_le p q : (p <=? q) = true <-> p <= q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.leb_le".  
unfold leb, le. destruct compare; easy'.
Qed.



Include BoolEqualityFacts.






Definition switch_Eq c c' :=
match c' with
| Eq => c
| Lt => Lt
| Gt => Gt
end.

Lemma compare_cont_spec p q c :
compare_cont c p q = switch_Eq c (p ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_spec".  
unfold compare.
revert q c.
induction p; destruct q; simpl; trivial.
intros c.
rewrite 2 IHp. now destruct (compare_cont Eq p q).
intros c.
rewrite 2 IHp. now destruct (compare_cont Eq p q).
Qed.



Theorem compare_cont_Eq p q c :
compare_cont c p q = Eq -> c = Eq.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_Eq".  
rewrite compare_cont_spec. now destruct (p ?= q).
Qed.

Lemma compare_cont_Lt_Gt p q :
compare_cont Lt p q = Gt <-> p > q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_Lt_Gt".  
rewrite compare_cont_spec. unfold gt. destruct (p ?= q); now split.
Qed.

Lemma compare_cont_Lt_Lt p q :
compare_cont Lt p q = Lt <-> p <= q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_Lt_Lt".  
rewrite compare_cont_spec. unfold le. destruct (p ?= q); easy'.
Qed.

Lemma compare_cont_Gt_Lt p q :
compare_cont Gt p q = Lt <-> p < q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_Gt_Lt".  
rewrite compare_cont_spec. unfold lt. destruct (p ?= q); now split.
Qed.

Lemma compare_cont_Gt_Gt p q :
compare_cont Gt p q = Gt <-> p >= q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_Gt_Gt".  
rewrite compare_cont_spec. unfold ge. destruct (p ?= q); easy'.
Qed.

Lemma compare_cont_Lt_not_Lt p q :
compare_cont Lt p q <> Lt <-> p > q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_Lt_not_Lt".  
rewrite compare_cont_Lt_Lt.
unfold gt, le, compare.
now destruct compare_cont; split; try apply comparison_eq_stable.
Qed.

Lemma compare_cont_Lt_not_Gt p q :
compare_cont Lt p q <> Gt <-> p <= q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_Lt_not_Gt".  
apply not_iff_compat, compare_cont_Lt_Gt.
Qed.

Lemma compare_cont_Gt_not_Lt p q :
compare_cont Gt p q <> Lt <-> p >= q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_Gt_not_Lt".  
apply not_iff_compat, compare_cont_Gt_Lt.
Qed.

Lemma compare_cont_Gt_not_Gt p q :
compare_cont Gt p q <> Gt <-> p < q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_Gt_not_Gt".  
rewrite compare_cont_Gt_Gt.
unfold ge, lt, compare.
now destruct compare_cont; split; try apply comparison_eq_stable.
Qed.



Lemma compare_xO_xO p q : (p~0 ?= q~0) = (p ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_xO_xO".   reflexivity. Qed.

Lemma compare_xI_xI p q : (p~1 ?= q~1) = (p ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_xI_xI".   reflexivity. Qed.

Lemma compare_xI_xO p q :
(p~1 ?= q~0) = switch_Eq Gt (p ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_xI_xO".   exact (compare_cont_spec p q Gt). Qed.

Lemma compare_xO_xI p q :
(p~0 ?= q~1) = switch_Eq Lt (p ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_xO_xI".   exact (compare_cont_spec p q Lt). Qed.

Hint Rewrite compare_xO_xO compare_xI_xI compare_xI_xO compare_xO_xI : compare.

Ltac simpl_compare := autorewrite with compare.
Ltac simpl_compare_in H := autorewrite with compare in H.



Definition mask2cmp (p:mask) : comparison :=
match p with
| IsNul => Eq
| IsPos _ => Gt
| IsNeg => Lt
end.

Lemma compare_sub_mask p q : (p ?= q) = mask2cmp (sub_mask p q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_sub_mask".  
revert q.
induction p as [p IHp| p IHp| ]; intros [q|q| ]; simpl; trivial;
specialize (IHp q); rewrite ?sub_mask_carry_spec;
destruct (sub_mask p q) as [|r|]; simpl in *;
try clear r; try destruct r; simpl; trivial;
simpl_compare; now rewrite IHp.
Qed.



Lemma lt_iff_add p q : p < q <-> exists r, p + r = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_iff_add".  
unfold "<". rewrite <- sub_mask_neg_iff, compare_sub_mask.
destruct sub_mask; now split.
Qed.

Lemma gt_iff_add p q : p > q <-> exists r, q + r = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.gt_iff_add".  
unfold ">". rewrite compare_sub_mask.
split.
case_eq (sub_mask p q); try discriminate; intros r Hr _.
exists r. now apply sub_mask_pos_iff.
intros (r,Hr). apply sub_mask_pos_iff in Hr. now rewrite Hr.
Qed.



Theorem compare_cont_refl p c :
compare_cont c p p = c.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_refl".  
now induction p.
Qed.

Lemma compare_cont_antisym p q c :
CompOpp (compare_cont c p q) = compare_cont (CompOpp c) q p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_cont_antisym".  
revert q c.
induction p as [p IHp|p IHp| ]; intros [q|q| ] c; simpl;
trivial; apply IHp.
Qed.



Lemma compare_eq_iff p q : (p ?= q) = Eq <-> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_eq_iff".  
rewrite compare_sub_mask, <- sub_mask_nul_iff.
destruct sub_mask; now split.
Qed.

Lemma compare_antisym p q : (q ?= p) = CompOpp (p ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_antisym".  
unfold compare. now rewrite compare_cont_antisym.
Qed.

Lemma compare_lt_iff p q : (p ?= q) = Lt <-> p < q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_lt_iff".   reflexivity. Qed.

Lemma compare_le_iff p q : (p ?= q) <> Gt <-> p <= q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_le_iff".   reflexivity. Qed.



Include BoolOrderFacts.

Definition le_lteq := lt_eq_cases.





Lemma gt_lt_iff p q : p > q <-> q < p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.gt_lt_iff".  
unfold lt, gt. now rewrite compare_antisym, CompOpp_iff.
Qed.

Lemma gt_lt p q : p > q -> q < p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.gt_lt".  
apply gt_lt_iff.
Qed.

Lemma lt_gt p q : p < q -> q > p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_gt".  
apply gt_lt_iff.
Qed.

Lemma ge_le_iff p q : p >= q <-> q <= p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.ge_le_iff".  
unfold le, ge. now rewrite compare_antisym, CompOpp_iff.
Qed.

Lemma ge_le p q : p >= q -> q <= p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.ge_le".  
apply ge_le_iff.
Qed.

Lemma le_ge p q : p <= q -> q >= p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_ge".  
apply ge_le_iff.
Qed.



Lemma compare_succ_r p q :
switch_Eq Gt (p ?= succ q) = switch_Eq Lt (p ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_succ_r".  
revert q.
induction p as [p IH|p IH| ]; intros [q|q| ]; simpl;
simpl_compare; rewrite ?IH; trivial;
(now destruct compare) || (now destruct p).
Qed.

Lemma compare_succ_l p q :
switch_Eq Lt (succ p ?= q) = switch_Eq Gt (p ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_succ_l".  
rewrite 2 (compare_antisym q). generalize (compare_succ_r q p).
now do 2 destruct compare.
Qed.

Theorem lt_succ_r p q : p < succ q <-> p <= q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_succ_r".  
unfold lt, le. generalize (compare_succ_r p q).
do 2 destruct compare; try discriminate; now split.
Qed.

Lemma lt_succ_diag_r p : p < succ p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_succ_diag_r".  
rewrite lt_iff_add. exists 1. apply add_1_r.
Qed.

Lemma compare_succ_succ p q : (succ p ?= succ q) = (p ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.compare_succ_succ".  
revert q.
induction p; destruct q; simpl; simpl_compare; trivial;
apply compare_succ_l || apply compare_succ_r ||
(now destruct p) || (now destruct q).
Qed.



Lemma le_1_l p : 1 <= p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_1_l".  
now destruct p.
Qed.

Lemma nlt_1_r p : ~ p < 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.nlt_1_r".  
now destruct p.
Qed.

Lemma lt_1_succ p : 1 < succ p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_1_succ".  
apply lt_succ_r, le_1_l.
Qed.



Lemma le_nlt p q : p <= q <-> ~ q < p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_nlt".  
now rewrite <- ge_le_iff.
Qed.

Lemma lt_nle p q : p < q <-> ~ q <= p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_nle".  
intros. unfold lt, le. rewrite compare_antisym.
destruct compare; split; auto; easy'.
Qed.

Lemma lt_le_incl p q : p<q -> p<=q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_le_incl".  
intros. apply le_lteq. now left.
Qed.

Lemma lt_lt_succ n m : n < m -> n < succ m.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_lt_succ".  
intros. now apply lt_succ_r, lt_le_incl.
Qed.

Lemma succ_lt_mono n m : n < m <-> succ n < succ m.
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_lt_mono".  
unfold lt. now rewrite compare_succ_succ.
Qed.

Lemma succ_le_mono n m : n <= m <-> succ n <= succ m.
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_le_mono".  
unfold le. now rewrite compare_succ_succ.
Qed.

Lemma lt_trans n m p : n < m -> m < p -> n < p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_trans".  
rewrite 3 lt_iff_add. intros (r,Hr) (s,Hs).
exists (r+s). now rewrite add_assoc, Hr, Hs.
Qed.

Theorem lt_ind : forall (A : positive -> Prop) (n : positive),
A (succ n) ->
(forall m : positive, n < m -> A m -> A (succ m)) ->
forall m : positive, n < m -> A m.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_ind".  
intros A n AB AS m. induction m using peano_ind; intros H.
elim (nlt_1_r _ H).
apply lt_succ_r, le_lteq in H. destruct H as [H|H]; subst; auto.
Qed.

Instance lt_strorder : StrictOrder lt.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_strorder".   split. exact lt_irrefl. exact lt_trans. Qed.

Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) lt.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_compat".   repeat red. intros. subst; auto. Qed.

Lemma lt_total p q : p < q \/ p = q \/ q < p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_total".  
case (compare_spec p q); intuition.
Qed.

Lemma le_refl p : p <= p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_refl".  
intros. unfold le. now rewrite compare_refl.
Qed.

Lemma le_lt_trans n m p : n <= m -> m < p -> n < p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_lt_trans".  
intros H H'. apply le_lteq in H. destruct H.
now apply lt_trans with m. now subst.
Qed.

Lemma lt_le_trans n m p : n < m -> m <= p -> n < p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_le_trans".  
intros H H'. apply le_lteq in H'. destruct H'.
now apply lt_trans with m. now subst.
Qed.

Lemma le_trans n m p : n <= m -> m <= p -> n <= p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_trans".  
intros H H'.
apply le_lteq in H. destruct H.
apply le_lteq; left. now apply lt_le_trans with m.
now subst.
Qed.

Lemma le_succ_l n m : succ n <= m <-> n < m.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_succ_l".  
rewrite <- lt_succ_r. symmetry. apply succ_lt_mono.
Qed.

Lemma le_antisym p q : p <= q -> q <= p -> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_antisym".  
rewrite le_lteq; destruct 1; auto.
rewrite le_lteq; destruct 1; auto.
elim (lt_irrefl p). now transitivity q.
Qed.

Instance le_preorder : PreOrder le.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_preorder".   split. exact le_refl. exact le_trans. Qed.

Instance le_partorder : PartialOrder Logic.eq le.
Proof. try hammer_hook "BinPos" "BinPos.Pos.le_partorder".  
intros x y. change (x=y <-> x <= y <= x).
split. intros; now subst.
destruct 1; now apply le_antisym.
Qed.



Lemma add_compare_mono_l p q r : (p+q ?= p+r) = (q ?= r).
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_compare_mono_l".  
revert p q r. induction p using peano_ind; intros q r.
rewrite 2 add_1_l. apply compare_succ_succ.
now rewrite 2 add_succ_l, compare_succ_succ.
Qed.

Lemma add_compare_mono_r p q r : (q+p ?= r+p) = (q ?= r).
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_compare_mono_r".  
rewrite 2 (add_comm _ p). apply add_compare_mono_l.
Qed.



Lemma lt_add_diag_r p q : p < p + q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_add_diag_r".  
rewrite lt_iff_add. now exists q.
Qed.

Lemma add_lt_mono_l p q r : q<r <-> p+q < p+r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_lt_mono_l".  
unfold lt. rewrite add_compare_mono_l. apply iff_refl.
Qed.

Lemma add_lt_mono_r p q r : q<r <-> q+p < r+p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_lt_mono_r".  
unfold lt. rewrite add_compare_mono_r. apply iff_refl.
Qed.

Lemma add_lt_mono p q r s : p<q -> r<s -> p+r<q+s.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_lt_mono".  
intros. apply lt_trans with (p+s).
now apply add_lt_mono_l.
now apply add_lt_mono_r.
Qed.

Lemma add_le_mono_l p q r : q<=r <-> p+q<=p+r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_le_mono_l".  
unfold le. rewrite add_compare_mono_l. apply iff_refl.
Qed.

Lemma add_le_mono_r p q r : q<=r <-> q+p<=r+p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_le_mono_r".  
unfold le. rewrite add_compare_mono_r. apply iff_refl.
Qed.

Lemma add_le_mono p q r s : p<=q -> r<=s -> p+r <= q+s.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_le_mono".  
intros. apply le_trans with (p+s).
now apply add_le_mono_l.
now apply add_le_mono_r.
Qed.



Lemma mul_compare_mono_l p q r : (p*q ?= p*r) = (q ?= r).
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_compare_mono_l".  
revert q r. induction p; simpl; trivial.
intros q r. specialize (IHp q r).
destruct (compare_spec q r).
subst. apply compare_refl.
now apply add_lt_mono.
now apply lt_gt, add_lt_mono, gt_lt.
Qed.

Lemma mul_compare_mono_r p q r : (q*p ?= r*p) = (q ?= r).
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_compare_mono_r".  
rewrite 2 (mul_comm _ p). apply mul_compare_mono_l.
Qed.



Lemma mul_lt_mono_l p q r : q<r <-> p*q < p*r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_lt_mono_l".  
unfold lt. rewrite mul_compare_mono_l. apply iff_refl.
Qed.

Lemma mul_lt_mono_r p q r : q<r <-> q*p < r*p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_lt_mono_r".  
unfold lt. rewrite mul_compare_mono_r. apply iff_refl.
Qed.

Lemma mul_lt_mono p q r s : p<q -> r<s -> p*r < q*s.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_lt_mono".  
intros. apply lt_trans with (p*s).
now apply mul_lt_mono_l.
now apply mul_lt_mono_r.
Qed.

Lemma mul_le_mono_l p q r : q<=r <-> p*q<=p*r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_le_mono_l".  
unfold le. rewrite mul_compare_mono_l. apply iff_refl.
Qed.

Lemma mul_le_mono_r p q r : q<=r <-> q*p<=r*p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_le_mono_r".  
unfold le. rewrite mul_compare_mono_r. apply iff_refl.
Qed.

Lemma mul_le_mono p q r s : p<=q -> r<=s -> p*r <= q*s.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_le_mono".  
intros. apply le_trans with (p*s).
now apply mul_le_mono_l.
now apply mul_le_mono_r.
Qed.

Lemma lt_add_r p q : p < p+q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_add_r".  
induction q using peano_ind.
rewrite add_1_r. apply lt_succ_diag_r.
apply lt_trans with (p+q); auto.
apply add_lt_mono_l, lt_succ_diag_r.
Qed.

Lemma lt_not_add_l p q : ~ p+q < p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.lt_not_add_l".  
intro H. elim (lt_irrefl p).
apply lt_trans with (p+q); auto using lt_add_r.
Qed.

Lemma pow_gt_1 n p : 1<n -> 1<n^p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.pow_gt_1".  
intros H. induction p using peano_ind.
now rewrite pow_1_r.
rewrite pow_succ_r.
apply lt_trans with (n*1).
now rewrite mul_1_r.
now apply mul_lt_mono_l.
Qed.




Lemma sub_1_r p : sub p 1 = pred p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_1_r".  
now destruct p.
Qed.

Lemma pred_sub p : pred p = sub p 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.pred_sub".  
symmetry. apply sub_1_r.
Qed.

Theorem sub_succ_r p q : p - (succ q) = pred (p - q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_succ_r".  
unfold sub; rewrite sub_mask_succ_r, sub_mask_carry_spec.
destruct (sub_mask p q) as [|[r|r| ]|]; auto.
Qed.



Lemma sub_mask_pos' p q :
q < p -> exists r, sub_mask p q = IsPos r /\ q + r = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_pos'".  
rewrite lt_iff_add. intros (r,Hr). exists r. split; trivial.
now apply sub_mask_pos_iff.
Qed.

Lemma sub_mask_pos p q :
q < p -> exists r, sub_mask p q = IsPos r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_pos".  
intros H. destruct (sub_mask_pos' p q H) as (r & Hr & _). now exists r.
Qed.

Theorem sub_add p q : q < p -> (p-q)+q = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_add".  
intros H. destruct (sub_mask_pos p q H) as (r,U).
unfold sub. rewrite U. rewrite add_comm. now apply sub_mask_add.
Qed.

Lemma add_sub p q : (p+q)-q = p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_sub".  
intros. apply add_reg_r with q.
rewrite sub_add; trivial.
rewrite add_comm. apply lt_add_r.
Qed.

Lemma mul_sub_distr_l p q r : r<q -> p*(q-r) = p*q-p*r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_sub_distr_l".  
intros H.
apply add_reg_r with (p*r).
rewrite <- mul_add_distr_l.
rewrite sub_add; trivial.
symmetry. apply sub_add; trivial.
now apply mul_lt_mono_l.
Qed.

Lemma mul_sub_distr_r p q r : q<p -> (p-q)*r = p*r-q*r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_sub_distr_r".  
intros H. rewrite 3 (mul_comm _ r). now apply mul_sub_distr_l.
Qed.

Lemma sub_lt_mono_l p q r: q<p -> p<r -> r-p < r-q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_lt_mono_l".  
intros Hqp Hpr.
apply (add_lt_mono_r p).
rewrite sub_add by trivial.
apply le_lt_trans with ((r-q)+q).
rewrite sub_add by (now apply lt_trans with p).
apply le_refl.
now apply add_lt_mono_l.
Qed.

Lemma sub_compare_mono_l p q r :
q<p -> r<p -> (p-q ?= p-r) = (r ?= q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_compare_mono_l".  
intros Hqp Hrp.
case (compare_spec r q); intros H. subst. apply compare_refl.
apply sub_lt_mono_l; trivial.
apply lt_gt, sub_lt_mono_l; trivial.
Qed.

Lemma sub_compare_mono_r p q r :
p<q -> p<r -> (q-p ?= r-p) = (q ?= r).
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_compare_mono_r".  
intros. rewrite <- (add_compare_mono_r p), 2 sub_add; trivial.
Qed.

Lemma sub_lt_mono_r p q r : q<p -> r<q -> q-r < p-r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_lt_mono_r".  
intros. unfold lt. rewrite sub_compare_mono_r; trivial.
now apply lt_trans with q.
Qed.

Lemma sub_decr n m : m<n -> n-m < n.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_decr".  
intros.
apply add_lt_mono_r with m.
rewrite sub_add; trivial.
apply lt_add_r.
Qed.

Lemma add_sub_assoc p q r : r<q -> p+(q-r) = p+q-r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_sub_assoc".  
intros.
apply add_reg_r with r.
rewrite <- add_assoc, !sub_add; trivial.
rewrite add_comm. apply lt_trans with q; trivial using lt_add_r.
Qed.

Lemma sub_add_distr p q r : q+r < p -> p-(q+r) = p-q-r.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_add_distr".  
intros.
assert (q < p)
by (apply lt_trans with (q+r); trivial using lt_add_r).
rewrite (add_comm q r) in *.
apply add_reg_r with (r+q).
rewrite sub_add by trivial.
rewrite add_assoc, !sub_add; trivial.
apply (add_lt_mono_r q). rewrite sub_add; trivial.
Qed.

Lemma sub_sub_distr p q r : r<q -> q-r < p -> p-(q-r) = p+r-q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_sub_distr".  
intros.
apply add_reg_r with ((q-r)+r).
rewrite add_assoc, !sub_add; trivial.
rewrite <- (sub_add q r); trivial.
now apply add_lt_mono_r.
Qed.



Lemma sub_xO_xO n m : m<n -> n~0 - m~0 = (n-m)~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_xO_xO".  
intros H. unfold sub. simpl.
now destruct (sub_mask_pos n m H) as (p, ->).
Qed.

Lemma sub_xI_xI n m : m<n -> n~1 - m~1 = (n-m)~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_xI_xI".  
intros H. unfold sub. simpl.
now destruct (sub_mask_pos n m H) as (p, ->).
Qed.

Lemma sub_xI_xO n m : m<n -> n~1 - m~0 = (n-m)~1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_xI_xO".  
intros H. unfold sub. simpl.
now destruct (sub_mask_pos n m) as (p, ->).
Qed.

Lemma sub_xO_xI n m : n~0 - m~1 = pred_double (n-m).
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_xO_xI".  
unfold sub. simpl. rewrite sub_mask_carry_spec.
now destruct (sub_mask n m) as [|[r|r|]|].
Qed.



Lemma sub_mask_neg_iff' p q : sub_mask p q = IsNeg <-> p < q.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_neg_iff'".  
rewrite lt_iff_add. apply sub_mask_neg_iff.
Qed.

Lemma sub_mask_neg p q : p<q -> sub_mask p q = IsNeg.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_mask_neg".  
apply sub_mask_neg_iff'.
Qed.

Lemma sub_le p q : p<=q -> p-q = 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_le".  
unfold le, sub. rewrite compare_sub_mask.
destruct sub_mask; easy'.
Qed.

Lemma sub_lt p q : p<q -> p-q = 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_lt".  
intros. now apply sub_le, lt_le_incl.
Qed.

Lemma sub_diag p : p-p = 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sub_diag".  
unfold sub. now rewrite sub_mask_diag.
Qed.



Lemma size_nat_monotone p q : p<q -> (size_nat p <= size_nat q)%nat.
Proof. try hammer_hook "BinPos" "BinPos.Pos.size_nat_monotone".  
assert (le0 : forall n, (0<=n)%nat) by (induction n; auto).
assert (leS : forall n m, (n<=m -> S n <= S m)%nat) by (induction 1; auto).
revert q.
induction p; destruct q; simpl; intros; auto; easy || apply leS;
red in H; simpl_compare_in H.
apply IHp. red. now destruct (p?=q).
destruct (compare_spec p q); subst; now auto.
Qed.

Lemma size_gt p : p < 2^(size p).
Proof. try hammer_hook "BinPos" "BinPos.Pos.size_gt".  
induction p; simpl; try rewrite pow_succ_r; try easy.
apply le_succ_l in IHp. now apply le_succ_l.
Qed.

Lemma size_le p : 2^(size p) <= p~0.
Proof. try hammer_hook "BinPos" "BinPos.Pos.size_le".  
induction p; simpl; try rewrite pow_succ_r; try easy.
apply mul_le_mono_l.
apply le_lteq; left. rewrite xI_succ_xO. apply lt_succ_r, IHp.
Qed.





Lemma max_l : forall x y, y<=x -> max x y = x.
Proof. try hammer_hook "BinPos" "BinPos.Pos.max_l".  
intros x y H. unfold max. case compare_spec; auto.
intros H'. apply le_nlt in H. now elim H.
Qed.

Lemma max_r : forall x y, x<=y -> max x y = y.
Proof. try hammer_hook "BinPos" "BinPos.Pos.max_r".  
unfold le, max. intros x y. destruct compare; easy'.
Qed.

Lemma min_l : forall x y, x<=y -> min x y = x.
Proof. try hammer_hook "BinPos" "BinPos.Pos.min_l".  
unfold le, min. intros x y. destruct compare; easy'.
Qed.

Lemma min_r : forall x y, y<=x -> min x y = y.
Proof. try hammer_hook "BinPos" "BinPos.Pos.min_r".  
intros x y H. unfold min. case compare_spec; auto.
intros H'. apply le_nlt in H. now elim H'.
Qed.



Include UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

Ltac order := Private_Tac.order.



Lemma max_1_l n : max 1 n = n.
Proof. try hammer_hook "BinPos" "BinPos.Pos.max_1_l".  
unfold max. case compare_spec; auto.
intros H. apply lt_nle in H. elim H. apply le_1_l.
Qed.

Lemma max_1_r n : max n 1 = n.
Proof. try hammer_hook "BinPos" "BinPos.Pos.max_1_r".   rewrite max_comm. apply max_1_l. Qed.

Lemma min_1_l n : min 1 n = 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.min_1_l".  
unfold min. case compare_spec; auto.
intros H. apply lt_nle in H. elim H. apply le_1_l.
Qed.

Lemma min_1_r n : min n 1 = 1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.min_1_r".   rewrite min_comm. apply min_1_l. Qed.



Lemma succ_max_distr n m : succ (max n m) = max (succ n) (succ m).
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_max_distr".  
symmetry. apply max_monotone.
intros x x'. apply succ_le_mono.
Qed.

Lemma succ_min_distr n m : succ (min n m) = min (succ n) (succ m).
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_min_distr".  
symmetry. apply min_monotone.
intros x x'. apply succ_le_mono.
Qed.

Lemma add_max_distr_l n m p : max (p + n) (p + m) = p + max n m.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_max_distr_l".  
apply max_monotone. intros x x'. apply add_le_mono_l.
Qed.

Lemma add_max_distr_r n m p : max (n + p) (m + p) = max n m + p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_max_distr_r".  
rewrite 3 (add_comm _ p). apply add_max_distr_l.
Qed.

Lemma add_min_distr_l n m p : min (p + n) (p + m) = p + min n m.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_min_distr_l".  
apply min_monotone. intros x x'. apply add_le_mono_l.
Qed.

Lemma add_min_distr_r n m p : min (n + p) (m + p) = min n m + p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.add_min_distr_r".  
rewrite 3 (add_comm _ p). apply add_min_distr_l.
Qed.

Lemma mul_max_distr_l n m p : max (p * n) (p * m) = p * max n m.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_max_distr_l".  
apply max_monotone. intros x x'. apply mul_le_mono_l.
Qed.

Lemma mul_max_distr_r n m p : max (n * p) (m * p) = max n m * p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_max_distr_r".  
rewrite 3 (mul_comm _ p). apply mul_max_distr_l.
Qed.

Lemma mul_min_distr_l n m p : min (p * n) (p * m) = p * min n m.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_min_distr_l".  
apply min_monotone. intros x x'. apply mul_le_mono_l.
Qed.

Lemma mul_min_distr_r n m p : min (n * p) (m * p) = min n m * p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.mul_min_distr_r".  
rewrite 3 (mul_comm _ p). apply mul_min_distr_l.
Qed.




Lemma iter_op_succ : forall A (op:A->A->A),
(forall x y z, op x (op y z) = op (op x y) z) ->
forall p a,
iter_op op (succ p) a = op a (iter_op op p a).
Proof. try hammer_hook "BinPos" "BinPos.Pos.iter_op_succ".  
induction p; simpl; intros; trivial.
rewrite H. apply IHp.
Qed.



Lemma of_nat_succ (n:nat) : of_succ_nat n = of_nat (S n).
Proof. try hammer_hook "BinPos" "BinPos.Pos.of_nat_succ".  
induction n. trivial. simpl. f_equal. now rewrite IHn.
Qed.

Lemma pred_of_succ_nat (n:nat) : pred (of_succ_nat n) = of_nat n.
Proof. try hammer_hook "BinPos" "BinPos.Pos.pred_of_succ_nat".  
destruct n. trivial. simpl pred. rewrite pred_succ. apply of_nat_succ.
Qed.

Lemma succ_of_nat (n:nat) : n<>O -> succ (of_nat n) = of_succ_nat n.
Proof. try hammer_hook "BinPos" "BinPos.Pos.succ_of_nat".  
rewrite of_nat_succ. destruct n; trivial. now destruct 1.
Qed.



Inductive SqrtSpec : positive*mask -> positive -> Prop :=
| SqrtExact s x : x=s*s -> SqrtSpec (s,IsNul) x
| SqrtApprox s r x : x=s*s+r -> r <= s~0 -> SqrtSpec (s,IsPos r) x.

Lemma sqrtrem_step_spec f g p x :
(f=xO \/ f=xI) -> (g=xO \/ g=xI) ->
SqrtSpec p x -> SqrtSpec (sqrtrem_step f g p) (g (f x)).
Proof. try hammer_hook "BinPos" "BinPos.Pos.sqrtrem_step_spec".  
intros Hf Hg [ s _ -> | s r _ -> Hr ].

unfold sqrtrem_step.
destruct Hf,Hg; subst; simpl; constructor; now rewrite ?square_xO.

assert (Hfg : forall p q, g (f (p+q)) = p~0~0 + g (f q))
by (intros; destruct Hf, Hg; now subst).
unfold sqrtrem_step, leb.
case compare_spec; [intros EQ | intros LT | intros GT].

rewrite <- EQ, sub_mask_diag. constructor.
destruct Hg; subst g; destr_eq EQ.
destruct Hf; subst f; destr_eq EQ.
subst. now rewrite square_xI.

destruct (sub_mask_pos' _ _ LT) as (y & -> & H). constructor.
rewrite Hfg, <- H. now rewrite square_xI, add_assoc. clear Hfg.
rewrite <- lt_succ_r in Hr. change (r < s~1) in Hr.
rewrite <- lt_succ_r, (add_lt_mono_l (s~0~1)), H. simpl.
rewrite add_carry_spec, add_diag. simpl.
destruct Hf,Hg; subst; red; simpl_compare; now rewrite Hr.

constructor. now rewrite Hfg, square_xO. apply lt_succ_r, GT.
Qed.

Lemma sqrtrem_spec p : SqrtSpec (sqrtrem p) p.
Proof. try hammer_hook "BinPos" "BinPos.Pos.sqrtrem_spec".  
revert p. fix 1.
destruct p; try destruct p; try (constructor; easy);
apply sqrtrem_step_spec; auto.
Qed.

Lemma sqrt_spec p :
let s := sqrt p in s*s <= p < (succ s)*(succ s).
Proof. try hammer_hook "BinPos" "BinPos.Pos.sqrt_spec".  
simpl.
assert (H:=sqrtrem_spec p).
unfold sqrt in *. destruct sqrtrem as (s,rm); simpl.
inversion_clear H; subst.

split. reflexivity. apply mul_lt_mono; apply lt_succ_diag_r.

split.
apply lt_le_incl, lt_add_r.
rewrite <- add_1_l, mul_add_distr_r, !mul_add_distr_l, !mul_1_r, !mul_1_l.
rewrite add_assoc, (add_comm _ r). apply add_lt_mono_r.
now rewrite <- add_assoc, add_diag, add_1_l, lt_succ_r.
Qed.



Lemma divide_add_cancel_l p q r : (p | r) -> (p | q + r) -> (p | q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.divide_add_cancel_l".  
intros (s,Hs) (t,Ht).
exists (t-s).
rewrite mul_sub_distr_r.
rewrite <- Hs, <- Ht.
symmetry. apply add_sub.
apply mul_lt_mono_r with p.
rewrite <- Hs, <- Ht, add_comm.
apply lt_add_r.
Qed.

Lemma divide_xO_xI p q r : (p | q~0) -> (p | r~1) -> (p | q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.divide_xO_xI".  
intros (s,Hs) (t,Ht).
destruct p.
destruct s; try easy. simpl in Hs. destr_eq Hs. now exists s.
rewrite mul_xO_r in Ht; discriminate.
exists q; now rewrite mul_1_r.
Qed.

Lemma divide_xO_xO p q : (p~0|q~0) <-> (p|q).
Proof. try hammer_hook "BinPos" "BinPos.Pos.divide_xO_xO".  
split; intros (r,H); simpl in *.
rewrite mul_xO_r in H. destr_eq H. now exists r.
exists r; simpl. rewrite mul_xO_r. f_equal; auto.
Qed.

Lemma divide_mul_l p q r : (p|q) -> (p|q*r).
Proof. try hammer_hook "BinPos" "BinPos.Pos.divide_mul_l".  
intros (s,H). exists (s*r).
rewrite <- mul_assoc, (mul_comm r p), mul_assoc. now f_equal.
Qed.

Lemma divide_mul_r p q r : (p|r) -> (p|q*r).
Proof. try hammer_hook "BinPos" "BinPos.Pos.divide_mul_r".  
rewrite mul_comm. apply divide_mul_l.
Qed.



Lemma ggcdn_gcdn : forall n a b,
fst (ggcdn n a b) = gcdn n a b.
Proof. try hammer_hook "BinPos" "BinPos.Pos.ggcdn_gcdn".  
induction n.
simpl; auto.
destruct a, b; simpl; auto; try case compare_spec; simpl; trivial;
rewrite <- IHn; destruct ggcdn as (g,(u,v)); simpl; auto.
Qed.

Lemma ggcd_gcd : forall a b, fst (ggcd a b) = gcd a b.
Proof. try hammer_hook "BinPos" "BinPos.Pos.ggcd_gcd".  
unfold ggcd, gcd. intros. apply ggcdn_gcdn.
Qed.



Ltac destr_pggcdn IHn :=
match goal with |- context [ ggcdn _ ?x ?y ] =>
generalize (IHn x y); destruct ggcdn as (g,(u,v)); simpl
end.

Lemma ggcdn_correct_divisors : forall n a b,
let '(g,(aa,bb)) := ggcdn n a b in
a = g*aa /\ b = g*bb.
Proof. try hammer_hook "BinPos" "BinPos.Pos.ggcdn_correct_divisors".  
induction n.
simpl; auto.
destruct a, b; simpl; auto; try case compare_spec; try destr_pggcdn IHn.

intros ->. now rewrite mul_comm.

intros (H',H) LT; split; auto.
rewrite mul_add_distr_l, mul_xO_r, <- H, <- H'.
simpl. f_equal. symmetry.
rewrite add_comm. now apply sub_add.

intros (H',H) LT; split; auto.
rewrite mul_add_distr_l, mul_xO_r, <- H, <- H'.
simpl. f_equal. symmetry.
rewrite add_comm. now apply sub_add.

intros (H,H'); split; auto. rewrite mul_xO_r, H'; auto.
intros (H,H'); split; auto. rewrite mul_xO_r, H; auto.
intros (H,H'); split; subst; auto.
Qed.

Lemma ggcd_correct_divisors : forall a b,
let '(g,(aa,bb)) := ggcd a b in
a=g*aa /\ b=g*bb.
Proof. try hammer_hook "BinPos" "BinPos.Pos.ggcd_correct_divisors".  
unfold ggcd. intros. apply ggcdn_correct_divisors.
Qed.



Lemma gcd_divide_l : forall a b, (gcd a b | a).
Proof. try hammer_hook "BinPos" "BinPos.Pos.gcd_divide_l".  
intros a b. rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
destruct ggcd as (g,(aa,bb)); simpl. intros (H,_). exists aa.
now rewrite mul_comm.
Qed.

Lemma gcd_divide_r : forall a b, (gcd a b | b).
Proof. try hammer_hook "BinPos" "BinPos.Pos.gcd_divide_r".  
intros a b. rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
destruct ggcd as (g,(aa,bb)); simpl. intros (_,H). exists bb.
now rewrite mul_comm.
Qed.



Lemma gcdn_greatest : forall n a b, (size_nat a + size_nat b <= n)%nat ->
forall p, (p|a) -> (p|b) -> (p|gcdn n a b).
Proof. try hammer_hook "BinPos" "BinPos.Pos.gcdn_greatest".  
induction n.
destruct a, b; simpl; inversion 1.
destruct a, b; simpl; try case compare_spec; simpl; auto.

intros LT LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
apply le_S_n in LE. eapply Le.le_trans; [|eapply LE].
rewrite plus_comm, <- plus_n_Sm, <- plus_Sn_m.
apply plus_le_compat; trivial.
apply size_nat_monotone, sub_decr, LT.
apply divide_xO_xI with a; trivial.
apply (divide_add_cancel_l p _ a~1); trivial.
now rewrite <- sub_xI_xI, sub_add.

intros LT LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
apply le_S_n in LE. eapply Le.le_trans; [|eapply LE].
apply plus_le_compat; trivial.
apply size_nat_monotone, sub_decr, LT.
apply divide_xO_xI with b; trivial.
apply (divide_add_cancel_l p _ b~1); trivial.
now rewrite <- sub_xI_xI, sub_add.

intros LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
apply le_S_n in LE. simpl. now rewrite plus_n_Sm.
apply divide_xO_xI with a; trivial.

intros LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
simpl. now apply le_S_n.
apply divide_xO_xI with b; trivial.

intros LE p Hp1 Hp2.
destruct p.
change (gcdn n a b)~0 with (2*(gcdn n a b)).
apply divide_mul_r.
apply IHn; clear IHn.
apply le_S_n in LE. apply le_Sn_le. now rewrite plus_n_Sm.
apply divide_xO_xI with p; trivial. now exists 1.
apply divide_xO_xI with p; trivial. now exists 1.
apply divide_xO_xO.
apply IHn; clear IHn.
apply le_S_n in LE. apply le_Sn_le. now rewrite plus_n_Sm.
now apply divide_xO_xO.
now apply divide_xO_xO.
exists (gcdn n a b)~0. now rewrite mul_1_r.
Qed.

Lemma gcd_greatest : forall a b p, (p|a) -> (p|b) -> (p|gcd a b).
Proof. try hammer_hook "BinPos" "BinPos.Pos.gcd_greatest".  
intros. apply gcdn_greatest; auto.
Qed.



Lemma ggcd_greatest : forall a b,
let (aa,bb) := snd (ggcd a b) in
forall p, (p|aa) -> (p|bb) -> p=1.
Proof. try hammer_hook "BinPos" "BinPos.Pos.ggcd_greatest".  
intros. generalize (gcd_greatest a b) (ggcd_correct_divisors a b).
rewrite <- ggcd_gcd. destruct ggcd as (g,(aa,bb)); simpl.
intros H (EQa,EQb) p Hp1 Hp2; subst.
assert (H' : (g*p | g)).
apply H.
destruct Hp1 as (r,Hr). exists r.
now rewrite mul_assoc, (mul_comm r g), <- mul_assoc, <- Hr.
destruct Hp2 as (r,Hr). exists r.
now rewrite mul_assoc, (mul_comm r g), <- mul_assoc, <- Hr.
destruct H' as (q,H').
rewrite (mul_comm g p), mul_assoc in H'.
apply mul_eq_1 with q; rewrite mul_comm.
now apply mul_reg_r with g.
Qed.

End Pos.

Bind Scope positive_scope with Pos.t positive.



Infix "+" := Pos.add : positive_scope.
Infix "-" := Pos.sub : positive_scope.
Infix "*" := Pos.mul : positive_scope.
Infix "^" := Pos.pow : positive_scope.
Infix "?=" := Pos.compare (at level 70, no associativity) : positive_scope.
Infix "=?" := Pos.eqb (at level 70, no associativity) : positive_scope.
Infix "<=?" := Pos.leb (at level 70, no associativity) : positive_scope.
Infix "<?" := Pos.ltb (at level 70, no associativity) : positive_scope.
Infix "<=" := Pos.le : positive_scope.
Infix "<" := Pos.lt : positive_scope.
Infix ">=" := Pos.ge : positive_scope.
Infix ">" := Pos.gt : positive_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : positive_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : positive_scope.
Notation "x < y < z" := (x < y /\ y < z) : positive_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : positive_scope.

Notation "( p | q )" := (Pos.divide p q) (at level 0) : positive_scope.



Notation positive := positive (only parsing).
Notation positive_rect := positive_rect (only parsing).
Notation positive_rec := positive_rec (only parsing).
Notation positive_ind := positive_ind (only parsing).
Notation xI := xI (only parsing).
Notation xO := xO (only parsing).
Notation xH := xH (only parsing).

Notation IsNul := Pos.IsNul (only parsing).
Notation IsPos := Pos.IsPos (only parsing).
Notation IsNeg := Pos.IsNeg (only parsing).

Notation Psucc := Pos.succ (compat "8.3").
Notation Pplus := Pos.add (compat "8.3").
Notation Pplus_carry := Pos.add_carry (compat "8.3").
Notation Ppred := Pos.pred (compat "8.3").
Notation Piter_op := Pos.iter_op (compat "8.3").
Notation Piter_op_succ := Pos.iter_op_succ (compat "8.3").
Notation Pmult_nat := (Pos.iter_op plus) (compat "8.3").
Notation nat_of_P := Pos.to_nat (compat "8.3").
Notation P_of_succ_nat := Pos.of_succ_nat (compat "8.3").
Notation Pdouble_minus_one := Pos.pred_double (compat "8.3").
Notation positive_mask := Pos.mask (compat "8.3").
Notation positive_mask_rect := Pos.mask_rect (compat "8.3").
Notation positive_mask_ind := Pos.mask_ind (compat "8.3").
Notation positive_mask_rec := Pos.mask_rec (compat "8.3").
Notation Pdouble_plus_one_mask := Pos.succ_double_mask (compat "8.3").
Notation Pdouble_mask := Pos.double_mask (compat "8.3").
Notation Pdouble_minus_two := Pos.double_pred_mask (compat "8.3").
Notation Pminus_mask := Pos.sub_mask (compat "8.3").
Notation Pminus_mask_carry := Pos.sub_mask_carry (compat "8.3").
Notation Pminus := Pos.sub (compat "8.3").
Notation Pmult := Pos.mul (compat "8.3").
Notation iter_pos := @Pos.iter (compat "8.3").
Notation Ppow := Pos.pow (compat "8.3").
Notation Pdiv2 := Pos.div2 (compat "8.3").
Notation Pdiv2_up := Pos.div2_up (compat "8.3").
Notation Psize := Pos.size_nat (compat "8.3").
Notation Psize_pos := Pos.size (compat "8.3").
Notation Pcompare x y m := (Pos.compare_cont m x y) (compat "8.3").
Notation Plt := Pos.lt (compat "8.3").
Notation Pgt := Pos.gt (compat "8.3").
Notation Ple := Pos.le (compat "8.3").
Notation Pge := Pos.ge (compat "8.3").
Notation Pmin := Pos.min (compat "8.3").
Notation Pmax := Pos.max (compat "8.3").
Notation Peqb := Pos.eqb (compat "8.3").
Notation positive_eq_dec := Pos.eq_dec (compat "8.3").
Notation xI_succ_xO := Pos.xI_succ_xO (compat "8.3").
Notation Psucc_discr := Pos.succ_discr (compat "8.3").
Notation Psucc_o_double_minus_one_eq_xO :=
Pos.succ_pred_double (compat "8.3").
Notation Pdouble_minus_one_o_succ_eq_xI :=
Pos.pred_double_succ (compat "8.3").
Notation xO_succ_permute := Pos.double_succ (compat "8.3").
Notation double_moins_un_xO_discr :=
Pos.pred_double_xO_discr (compat "8.3").
Notation Psucc_not_one := Pos.succ_not_1 (compat "8.3").
Notation Ppred_succ := Pos.pred_succ (compat "8.3").
Notation Psucc_pred := Pos.succ_pred_or (compat "8.3").
Notation Psucc_inj := Pos.succ_inj (compat "8.3").
Notation Pplus_carry_spec := Pos.add_carry_spec (compat "8.3").
Notation Pplus_comm := Pos.add_comm (compat "8.3").
Notation Pplus_succ_permute_r := Pos.add_succ_r (compat "8.3").
Notation Pplus_succ_permute_l := Pos.add_succ_l (compat "8.3").
Notation Pplus_no_neutral := Pos.add_no_neutral (compat "8.3").
Notation Pplus_carry_plus := Pos.add_carry_add (compat "8.3").
Notation Pplus_reg_r := Pos.add_reg_r (compat "8.3").
Notation Pplus_reg_l := Pos.add_reg_l (compat "8.3").
Notation Pplus_carry_reg_r := Pos.add_carry_reg_r (compat "8.3").
Notation Pplus_carry_reg_l := Pos.add_carry_reg_l (compat "8.3").
Notation Pplus_assoc := Pos.add_assoc (compat "8.3").
Notation Pplus_xO := Pos.add_xO (compat "8.3").
Notation Pplus_xI_double_minus_one := Pos.add_xI_pred_double (compat "8.3").
Notation Pplus_xO_double_minus_one := Pos.add_xO_pred_double (compat "8.3").
Notation Pplus_diag := Pos.add_diag (compat "8.3").
Notation PeanoView := Pos.PeanoView (compat "8.3").
Notation PeanoOne := Pos.PeanoOne (compat "8.3").
Notation PeanoSucc := Pos.PeanoSucc (compat "8.3").
Notation PeanoView_rect := Pos.PeanoView_rect (compat "8.3").
Notation PeanoView_ind := Pos.PeanoView_ind (compat "8.3").
Notation PeanoView_rec := Pos.PeanoView_rec (compat "8.3").
Notation peanoView_xO := Pos.peanoView_xO (compat "8.3").
Notation peanoView_xI := Pos.peanoView_xI (compat "8.3").
Notation peanoView := Pos.peanoView (compat "8.3").
Notation PeanoView_iter := Pos.PeanoView_iter (compat "8.3").
Notation eq_dep_eq_positive := Pos.eq_dep_eq_positive (compat "8.3").
Notation PeanoViewUnique := Pos.PeanoViewUnique (compat "8.3").
Notation Prect := Pos.peano_rect (compat "8.3").
Notation Prect_succ := Pos.peano_rect_succ (compat "8.3").
Notation Prect_base := Pos.peano_rect_base (compat "8.3").
Notation Prec := Pos.peano_rec (compat "8.3").
Notation Pind := Pos.peano_ind (compat "8.3").
Notation Pcase := Pos.peano_case (compat "8.3").
Notation Pmult_1_r := Pos.mul_1_r (compat "8.3").
Notation Pmult_Sn_m := Pos.mul_succ_l (compat "8.3").
Notation Pmult_xO_permute_r := Pos.mul_xO_r (compat "8.3").
Notation Pmult_xI_permute_r := Pos.mul_xI_r (compat "8.3").
Notation Pmult_comm := Pos.mul_comm (compat "8.3").
Notation Pmult_plus_distr_l := Pos.mul_add_distr_l (compat "8.3").
Notation Pmult_plus_distr_r := Pos.mul_add_distr_r (compat "8.3").
Notation Pmult_assoc := Pos.mul_assoc (compat "8.3").
Notation Pmult_xI_mult_xO_discr := Pos.mul_xI_mul_xO_discr (compat "8.3").
Notation Pmult_xO_discr := Pos.mul_xO_discr (compat "8.3").
Notation Pmult_reg_r := Pos.mul_reg_r (compat "8.3").
Notation Pmult_reg_l := Pos.mul_reg_l (compat "8.3").
Notation Pmult_1_inversion_l := Pos.mul_eq_1_l (compat "8.3").
Notation Psquare_xO := Pos.square_xO (compat "8.3").
Notation Psquare_xI := Pos.square_xI (compat "8.3").
Notation iter_pos_swap_gen := Pos.iter_swap_gen (compat "8.3").
Notation iter_pos_swap := Pos.iter_swap (compat "8.3").
Notation iter_pos_succ := Pos.iter_succ (compat "8.3").
Notation iter_pos_plus := Pos.iter_add (compat "8.3").
Notation iter_pos_invariant := Pos.iter_invariant (compat "8.3").
Notation Ppow_1_r := Pos.pow_1_r (compat "8.3").
Notation Ppow_succ_r := Pos.pow_succ_r (compat "8.3").
Notation Peqb_refl := Pos.eqb_refl (compat "8.3").
Notation Peqb_eq := Pos.eqb_eq (compat "8.3").
Notation Pcompare_refl_id := Pos.compare_cont_refl (compat "8.3").
Notation Pcompare_eq_iff := Pos.compare_eq_iff (compat "8.3").
Notation Pcompare_Gt_Lt := Pos.compare_cont_Gt_Lt (compat "8.3").
Notation Pcompare_eq_Lt := Pos.compare_lt_iff (compat "8.3").
Notation Pcompare_Lt_Gt := Pos.compare_cont_Lt_Gt (compat "8.3").

Notation Pcompare_antisym := Pos.compare_cont_antisym (compat "8.3").
Notation ZC1 := Pos.gt_lt (compat "8.3").
Notation ZC2 := Pos.lt_gt (compat "8.3").
Notation Pcompare_spec := Pos.compare_spec (compat "8.3").
Notation Pcompare_p_Sp := Pos.lt_succ_diag_r (compat "8.3").
Notation Pcompare_succ_succ := Pos.compare_succ_succ (compat "8.3").
Notation Pcompare_1 := Pos.nlt_1_r (compat "8.3").
Notation Plt_1 := Pos.nlt_1_r (compat "8.3").
Notation Plt_1_succ := Pos.lt_1_succ (compat "8.3").
Notation Plt_lt_succ := Pos.lt_lt_succ (compat "8.3").
Notation Plt_irrefl := Pos.lt_irrefl (compat "8.3").
Notation Plt_trans := Pos.lt_trans (compat "8.3").
Notation Plt_ind := Pos.lt_ind (compat "8.3").
Notation Ple_lteq := Pos.le_lteq (compat "8.3").
Notation Ple_refl := Pos.le_refl (compat "8.3").
Notation Ple_lt_trans := Pos.le_lt_trans (compat "8.3").
Notation Plt_le_trans := Pos.lt_le_trans (compat "8.3").
Notation Ple_trans := Pos.le_trans (compat "8.3").
Notation Plt_succ_r := Pos.lt_succ_r (compat "8.3").
Notation Ple_succ_l := Pos.le_succ_l (compat "8.3").
Notation Pplus_compare_mono_l := Pos.add_compare_mono_l (compat "8.3").
Notation Pplus_compare_mono_r := Pos.add_compare_mono_r (compat "8.3").
Notation Pplus_lt_mono_l := Pos.add_lt_mono_l (compat "8.3").
Notation Pplus_lt_mono_r := Pos.add_lt_mono_r (compat "8.3").
Notation Pplus_lt_mono := Pos.add_lt_mono (compat "8.3").
Notation Pplus_le_mono_l := Pos.add_le_mono_l (compat "8.3").
Notation Pplus_le_mono_r := Pos.add_le_mono_r (compat "8.3").
Notation Pplus_le_mono := Pos.add_le_mono (compat "8.3").
Notation Pmult_compare_mono_l := Pos.mul_compare_mono_l (compat "8.3").
Notation Pmult_compare_mono_r := Pos.mul_compare_mono_r (compat "8.3").
Notation Pmult_lt_mono_l := Pos.mul_lt_mono_l (compat "8.3").
Notation Pmult_lt_mono_r := Pos.mul_lt_mono_r (compat "8.3").
Notation Pmult_lt_mono := Pos.mul_lt_mono (compat "8.3").
Notation Pmult_le_mono_l := Pos.mul_le_mono_l (compat "8.3").
Notation Pmult_le_mono_r := Pos.mul_le_mono_r (compat "8.3").
Notation Pmult_le_mono := Pos.mul_le_mono (compat "8.3").
Notation Plt_plus_r := Pos.lt_add_r (compat "8.3").
Notation Plt_not_plus_l := Pos.lt_not_add_l (compat "8.3").
Notation Ppow_gt_1 := Pos.pow_gt_1 (compat "8.3").
Notation Ppred_mask := Pos.pred_mask (compat "8.3").
Notation Pminus_mask_succ_r := Pos.sub_mask_succ_r (compat "8.3").
Notation Pminus_mask_carry_spec := Pos.sub_mask_carry_spec (compat "8.3").
Notation Pminus_succ_r := Pos.sub_succ_r (compat "8.3").
Notation Pminus_mask_diag := Pos.sub_mask_diag (compat "8.3").

Notation Pplus_minus_eq := Pos.add_sub (compat "8.3").
Notation Pmult_minus_distr_l := Pos.mul_sub_distr_l (compat "8.3").
Notation Pminus_lt_mono_l := Pos.sub_lt_mono_l (compat "8.3").
Notation Pminus_compare_mono_l := Pos.sub_compare_mono_l (compat "8.3").
Notation Pminus_compare_mono_r := Pos.sub_compare_mono_r (compat "8.3").
Notation Pminus_lt_mono_r := Pos.sub_lt_mono_r (compat "8.3").
Notation Pminus_decr := Pos.sub_decr (compat "8.3").
Notation Pminus_xI_xI := Pos.sub_xI_xI (compat "8.3").
Notation Pplus_minus_assoc := Pos.add_sub_assoc (compat "8.3").
Notation Pminus_plus_distr := Pos.sub_add_distr (compat "8.3").
Notation Pminus_minus_distr := Pos.sub_sub_distr (compat "8.3").
Notation Pminus_mask_Lt := Pos.sub_mask_neg (compat "8.3").
Notation Pminus_Lt := Pos.sub_lt (compat "8.3").
Notation Pminus_Eq := Pos.sub_diag (compat "8.3").
Notation Psize_monotone := Pos.size_nat_monotone (compat "8.3").
Notation Psize_pos_gt := Pos.size_gt (compat "8.3").
Notation Psize_pos_le := Pos.size_le (compat "8.3").



Lemma Peqb_true_eq x y : Pos.eqb x y = true -> x=y.
Proof. try hammer_hook "BinPos" "BinPos.Peqb_true_eq".   apply Pos.eqb_eq. Qed.
Lemma Pcompare_eq_Gt p q : (p ?= q) = Gt <-> p > q.
Proof. try hammer_hook "BinPos" "BinPos.Pcompare_eq_Gt".   reflexivity. Qed.
Lemma Pplus_one_succ_r p : Pos.succ p = p + 1.
Proof. try hammer_hook "BinPos" "BinPos.Pplus_one_succ_r".  exact ((eq_sym (Pos.add_1_r p))). Qed.
Lemma Pplus_one_succ_l p : Pos.succ p = 1 + p.
Proof. try hammer_hook "BinPos" "BinPos.Pplus_one_succ_l".  exact ((eq_sym (Pos.add_1_l p))). Qed.
Lemma Pcompare_refl p : Pos.compare_cont Eq p p = Eq.
Proof. try hammer_hook "BinPos" "BinPos.Pcompare_refl".  exact ((Pos.compare_cont_refl p Eq)). Qed.
Lemma Pcompare_Eq_eq : forall p q, Pos.compare_cont Eq p q = Eq -> p = q.
Proof. try hammer_hook "BinPos" "BinPos.Pcompare_Eq_eq".  exact (Pos.compare_eq). Qed.
Lemma ZC4 p q : Pos.compare_cont Eq p q = CompOpp (Pos.compare_cont Eq q p).
Proof. try hammer_hook "BinPos" "BinPos.ZC4".  exact ((Pos.compare_antisym q p)). Qed.
Lemma Ppred_minus p : Pos.pred p = p - 1.
Proof. try hammer_hook "BinPos" "BinPos.Ppred_minus".  exact ((eq_sym (Pos.sub_1_r p))). Qed.

Lemma Pminus_mask_Gt p q :
p > q ->
exists h : positive,
Pos.sub_mask p q = IsPos h /\
q + h = p /\ (h = 1 \/ Pos.sub_mask_carry p q = IsPos (Pos.pred h)).
Proof. try hammer_hook "BinPos" "BinPos.Pminus_mask_Gt".  
intros H. apply Pos.gt_lt in H.
destruct (Pos.sub_mask_pos p q H) as (r & U).
exists r. repeat split; trivial.
now apply Pos.sub_mask_pos_iff.
destruct (Pos.eq_dec r 1) as [EQ|NE]; [now left|right].
rewrite Pos.sub_mask_carry_spec, U. destruct r; trivial. now elim NE.
Qed.

Lemma Pplus_minus : forall p q, p > q -> q+(p-q) = p.
Proof. try hammer_hook "BinPos" "BinPos.Pplus_minus".  
intros. rewrite Pos.add_comm. now apply Pos.sub_add, Pos.gt_lt.
Qed.





Lemma Dcompare : forall r:comparison, r = Eq \/ r = Lt \/ r = Gt.
Proof. try hammer_hook "BinPos" "BinPos.Dcompare".  
destruct r; auto.
Qed.


