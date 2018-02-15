From Hammer Require Import Hammer.



















Import EqNotations.



Section Dependent_Equality.

Variable U : Type.
Variable P : U -> Type.



Inductive eq_dep (p:U) (x:P p) : forall q:U, P q -> Prop :=
eq_dep_intro : eq_dep p x p x.
Hint Constructors eq_dep: core.

Lemma eq_dep_refl : forall (p:U) (x:P p), eq_dep p x p x.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_refl". Restart. exact (eq_dep_intro). Qed.

Lemma eq_dep_sym :
forall (p q:U) (x:P p) (y:P q), eq_dep p x q y -> eq_dep q y p x.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_sym". Restart. 
destruct 1; auto.
Qed.
Hint Immediate eq_dep_sym: core.

Lemma eq_dep_trans :
forall (p q r:U) (x:P p) (y:P q) (z:P r),
eq_dep p x q y -> eq_dep q y r z -> eq_dep p x r z.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_trans". Restart. 
destruct 1; auto.
Qed.

Scheme eq_indd := Induction for eq Sort Prop.



Inductive eq_dep1 (p:U) (x:P p) (q:U) (y:P q) : Prop :=
eq_dep1_intro : forall h:q = p, x = rew h in y -> eq_dep1 p x q y.

Lemma eq_dep1_dep :
forall (p:U) (x:P p) (q:U) (y:P q), eq_dep1 p x q y -> eq_dep p x q y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep1_dep". Restart. 
destruct 1 as (eq_qp, H).
destruct eq_qp using eq_indd.
rewrite H.
apply eq_dep_intro.
Qed.

Lemma eq_dep_dep1 :
forall (p q:U) (x:P p) (y:P q), eq_dep p x q y -> eq_dep1 p x q y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_dep1". Restart. 
destruct 1.
apply eq_dep1_intro with (eq_refl p).
simpl; trivial.
Qed.

End Dependent_Equality.

Arguments eq_dep  [U P] p x q _.
Arguments eq_dep1 [U P] p x q y.



Lemma eq_sigT_eq_dep :
forall (U:Type) (P:U -> Type) (p q:U) (x:P p) (y:P q),
existT P p x = existT P q y -> eq_dep p x q y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_sigT_eq_dep". Restart. 
intros.
dependent rewrite H.
apply eq_dep_intro.
Qed.

Notation eq_sigS_eq_dep := eq_sigT_eq_dep (compat "8.2").

Lemma eq_dep_eq_sigT :
forall (U:Type) (P:U -> Type) (p q:U) (x:P p) (y:P q),
eq_dep p x q y -> existT P p x = existT P q y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_eq_sigT". Restart. 
destruct 1; reflexivity.
Qed.

Lemma eq_sigT_iff_eq_dep :
forall (U:Type) (P:U -> Type) (p q:U) (x:P p) (y:P q),
existT P p x = existT P q y <-> eq_dep p x q y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_sigT_iff_eq_dep". Restart. 
split; auto using eq_sigT_eq_dep, eq_dep_eq_sigT.
Qed.

Notation equiv_eqex_eqdep := eq_sigT_iff_eq_dep (only parsing).

Lemma eq_sig_eq_dep :
forall (U:Type) (P:U -> Prop) (p q:U) (x:P p) (y:P q),
exist P p x = exist P q y -> eq_dep p x q y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_sig_eq_dep". Restart. 
intros.
dependent rewrite H.
apply eq_dep_intro.
Qed.

Lemma eq_dep_eq_sig :
forall (U:Type) (P:U -> Prop) (p q:U) (x:P p) (y:P q),
eq_dep p x q y -> exist P p x = exist P q y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_eq_sig". Restart. 
destruct 1; reflexivity.
Qed.

Lemma eq_sig_iff_eq_dep :
forall (U:Type) (P:U -> Prop) (p q:U) (x:P p) (y:P q),
exist P p x = exist P q y <-> eq_dep p x q y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_sig_iff_eq_dep". Restart. 
split; auto using eq_sig_eq_dep, eq_dep_eq_sig.
Qed.



Set Implicit Arguments.

Lemma eq_sigT_sig_eq : forall X P (x1 x2:X) H1 H2, existT P x1 H1 = existT P x2 H2 <->
{H:x1=x2 | rew H in H1 = H2}.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_sigT_sig_eq". Restart. 
intros; split; intro H.
- change x2 with (projT1 (existT P x2 H2)).
change H2 with (projT2 (existT P x2 H2)) at 5.
destruct H. simpl.
exists eq_refl.
reflexivity.
- destruct H as (->,<-).
reflexivity.
Defined.

Lemma eq_sigT_fst :
forall X P (x1 x2:X) H1 H2 (H:existT P x1 H1 = existT P x2 H2), x1 = x2.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_sigT_fst". Restart. 
intros.
change x2 with (projT1 (existT P x2 H2)).
destruct H.
reflexivity.
Defined.

Lemma eq_sigT_snd :
forall X P (x1 x2:X) H1 H2 (H:existT P x1 H1 = existT P x2 H2), rew (eq_sigT_fst H) in H1 = H2.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_sigT_snd". Restart. 
intros.
unfold eq_sigT_fst.
change x2 with (projT1 (existT P x2 H2)).
change H2 with (projT2 (existT P x2 H2)) at 3.
destruct H.
reflexivity.
Defined.

Lemma eq_sig_fst :
forall X P (x1 x2:X) H1 H2 (H:exist P x1 H1 = exist P x2 H2), x1 = x2.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_sig_fst". Restart. 
intros.
change x2 with (proj1_sig (exist P x2 H2)).
destruct H.
reflexivity.
Defined.

Lemma eq_sig_snd :
forall X P (x1 x2:X) H1 H2 (H:exist P x1 H1 = exist P x2 H2), rew (eq_sig_fst H) in H1 = H2.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_sig_snd". Restart. 
intros.
unfold eq_sig_fst, eq_ind.
change x2 with (proj1_sig (exist P x2 H2)).
change H2 with (proj2_sig (exist P x2 H2)) at 3.
destruct H.
reflexivity.
Defined.

Unset Implicit Arguments.



Hint Resolve eq_dep_intro: core.
Hint Immediate eq_dep_sym: core.




Section Equivalences.

Variable U:Type.



Definition Eq_rect_eq_on (p : U) (Q : U -> Type) (x : Q p) :=
forall (h : p = p), x = eq_rect p Q x p h.
Definition Eq_rect_eq := forall p Q x, Eq_rect_eq_on p Q x.



Definition Eq_dep_eq_on (P : U -> Type) (p : U) (x : P p) :=
forall (y : P p), eq_dep p x p y -> x = y.
Definition Eq_dep_eq := forall P p x, Eq_dep_eq_on P p x.



Definition UIP_on_ (x y : U) (p1 : x = y) :=
forall (p2 : x = y), p1 = p2.
Definition UIP_ := forall x y p1, UIP_on_ x y p1.



Definition UIP_refl_on_ (x : U) :=
forall (p : x = x), p = eq_refl x.
Definition UIP_refl_ := forall x, UIP_refl_on_ x.



Definition Streicher_K_on_ (x : U) (P : x = x -> Prop) :=
P (eq_refl x) -> forall p : x = x, P p.
Definition Streicher_K_ := forall x P, Streicher_K_on_ x P.




Lemma eq_rect_eq_on__eq_dep1_eq_on (p : U) (P : U -> Type) (y : P p) :
Eq_rect_eq_on p P y -> forall (x : P p), eq_dep1 p x p y -> x = y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_rect_eq_on__eq_dep1_eq_on". Restart. 
intro eq_rect_eq.
simple destruct 1; intro.
rewrite <- eq_rect_eq; auto.
Qed.
Lemma eq_rect_eq__eq_dep1_eq :
Eq_rect_eq -> forall (P:U->Type) (p:U) (x y:P p), eq_dep1 p x p y -> x = y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_rect_eq__eq_dep1_eq". Restart.
       exact ((fun eq_rect_eq P p y x => @eq_rect_eq_on__eq_dep1_eq_on p P x (eq_rect_eq p P x) y)).
Qed.


Lemma eq_rect_eq_on__eq_dep_eq_on (p : U) (P : U -> Type) (x : P p) :
Eq_rect_eq_on p P x -> Eq_dep_eq_on P p x.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_rect_eq_on__eq_dep_eq_on". Restart. 
intros eq_rect_eq; red; intros.
symmetry; apply (eq_rect_eq_on__eq_dep1_eq_on _ _ _ eq_rect_eq).
apply eq_dep_sym in H; apply eq_dep_dep1; trivial.
Qed.
Lemma eq_rect_eq__eq_dep_eq : Eq_rect_eq -> Eq_dep_eq.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_rect_eq__eq_dep_eq". Restart.
       exact ((fun eq_rect_eq P p x y => @eq_rect_eq_on__eq_dep_eq_on p P x (eq_rect_eq p P x) y)).
Qed.





Lemma eq_dep_eq_on__UIP_on (x y : U) (p1 : x = y) :
Eq_dep_eq_on (fun y => x = y) x eq_refl -> UIP_on_ x y p1.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_eq_on__UIP_on". Restart. 
intro eq_dep_eq; red.
elim p1 using eq_indd.
intros; apply eq_dep_eq.
elim p2 using eq_indd.
apply eq_dep_intro.
Qed.
Lemma eq_dep_eq__UIP : Eq_dep_eq -> UIP_.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_eq__UIP". Restart.
       exact ((fun eq_dep_eq x y p1 => @eq_dep_eq_on__UIP_on x y p1 (eq_dep_eq _ _ _))).
Qed.




Lemma UIP_on__UIP_refl_on (x : U) :
UIP_on_ x x eq_refl -> UIP_refl_on_ x.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.UIP_on__UIP_refl_on". Restart. 
intro UIP; red; intros; symmetry; apply UIP.
Qed.
Lemma UIP__UIP_refl : UIP_ -> UIP_refl_.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.UIP__UIP_refl". Restart.
       exact ((fun UIP x p => @UIP_on__UIP_refl_on x (UIP x x eq_refl) p)).
Qed.




Lemma UIP_refl_on__Streicher_K_on (x : U) (P : x = x -> Prop) :
UIP_refl_on_ x -> Streicher_K_on_ x P.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.UIP_refl_on__Streicher_K_on". Restart. 
intro UIP_refl; red; intros; rewrite UIP_refl; assumption.
Qed.
Lemma UIP_refl__Streicher_K : UIP_refl_ -> Streicher_K_.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.UIP_refl__Streicher_K". Restart.
       exact ((fun UIP_refl x P => @UIP_refl_on__Streicher_K_on x P (UIP_refl x))).
Qed.



Lemma Streicher_K_on__eq_rect_eq_on (p : U) (P : U -> Type) (x : P p) :
Streicher_K_on_ p (fun h => x = rew -> [P] h in x)
-> Eq_rect_eq_on p P x.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.Streicher_K_on__eq_rect_eq_on". Restart. 
intro Streicher_K; red; intros.
apply Streicher_K.
reflexivity.
Qed.
Lemma Streicher_K__eq_rect_eq : Streicher_K_ -> Eq_rect_eq.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.Streicher_K__eq_rect_eq". Restart.
       exact ((fun Streicher_K p P x => @Streicher_K_on__eq_rect_eq_on p P x (Streicher_K p _))).
Qed.




End Equivalences.



Theorem UIP_shift_on (X : Type) (x : X) :
UIP_refl_on_ X x -> forall y : x = x, UIP_refl_on_ (x = x) y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.UIP_shift_on". Restart. 
intros UIP_refl y.
rewrite (UIP_refl y).
intros z.
assert (UIP:forall y' y'' : x = x, y' = y'').
{ intros. apply eq_trans with (eq_refl x). apply UIP_refl.
symmetry. apply UIP_refl. }
transitivity (eq_trans (eq_trans (UIP (eq_refl x) (eq_refl x)) z)
(eq_sym (UIP (eq_refl x) (eq_refl x)))).
- destruct z. destruct (UIP _ _). reflexivity.
- change
(match eq_refl x as y' in _ = x' return y' = y' -> Prop with
| eq_refl => fun z => z = (eq_refl (eq_refl x))
end (eq_trans (eq_trans (UIP (eq_refl x) (eq_refl x)) z)
(eq_sym (UIP (eq_refl x) (eq_refl x))))).
destruct z. destruct (UIP _ _). reflexivity.
Qed.
Theorem UIP_shift : forall U, UIP_refl_ U -> forall x:U, UIP_refl_ (x = x).
Proof. hammer_hook "EqdepFacts" "EqdepFacts.UIP_shift". Restart. exact ((fun U UIP_refl x => @UIP_shift_on U x (UIP_refl x))). Qed.

Section Corollaries.

Variable U:Type.




Definition Inj_dep_pair_on (P : U -> Type) (p : U) (x : P p) :=
forall (y : P p), existT P p x = existT P p y -> x = y.
Definition Inj_dep_pair := forall P p x, Inj_dep_pair_on P p x.

Lemma eq_dep_eq_on__inj_pair2_on (P : U -> Type) (p : U) (x : P p) :
Eq_dep_eq_on U P p x -> Inj_dep_pair_on P p x.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_eq_on__inj_pair2_on". Restart. 
intro eq_dep_eq; red; intros.
apply eq_dep_eq.
apply eq_sigT_eq_dep.
assumption.
Qed.
Lemma eq_dep_eq__inj_pair2 : Eq_dep_eq U -> Inj_dep_pair.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_eq__inj_pair2". Restart. exact ((fun eq_dep_eq P p x => @eq_dep_eq_on__inj_pair2_on P p x (eq_dep_eq P p x))). Qed.


End Corollaries.

Notation Inj_dep_pairS := Inj_dep_pair.
Notation Inj_dep_pairT := Inj_dep_pair.
Notation eq_dep_eq__inj_pairT2 := eq_dep_eq__inj_pair2.





Module Type EqdepElimination.

Axiom eq_rect_eq :
forall (U:Type) (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
x = eq_rect p Q x p h.

End EqdepElimination.

Module EqdepTheory (M:EqdepElimination).

Section Axioms.

Variable U:Type.



Lemma eq_rect_eq :
forall (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.EqdepElimination.eq_rect_eq". Restart. exact (M.eq_rect_eq U). Qed.

Lemma eq_rec_eq :
forall (p:U) (Q:U -> Set) (x:Q p) (h:p = p), x = eq_rec p Q x p h.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.EqdepTheory.eq_rec_eq". Restart. exact ((fun p Q => M.eq_rect_eq U p Q)). Qed.



Lemma eq_dep_eq : forall (P:U->Type) (p:U) (x y:P p), eq_dep p x p y -> x = y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.EqdepTheory.eq_dep_eq". Restart. exact ((eq_rect_eq__eq_dep_eq U eq_rect_eq)). Qed.




Lemma UIP : forall (x y:U) (p1 p2:x = y), p1 = p2.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.EqdepTheory.UIP". Restart. exact ((eq_dep_eq__UIP U eq_dep_eq)). Qed.



Lemma UIP_refl : forall (x:U) (p:x = x), p = eq_refl x.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.EqdepTheory.UIP_refl". Restart. exact ((UIP__UIP_refl U UIP)). Qed.



Lemma Streicher_K :
forall (x:U) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.EqdepTheory.Streicher_K". Restart. exact ((UIP_refl__Streicher_K U UIP_refl)). Qed.

End Axioms.



Lemma inj_pair2 :
forall (U:Type) (P:U -> Type) (p:U) (x y:P p),
existT P p x = existT P p y -> x = y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.EqdepTheory.inj_pair2". Restart. exact ((fun U => eq_dep_eq__inj_pair2 U (eq_dep_eq U))). Qed.

Notation inj_pairT2 := inj_pair2.

End EqdepTheory.



Lemma f_eq_dep :
forall U (P:U->Type) R p q x y (f:forall p, P p -> R p),
eq_dep p x q y -> eq_dep p (f p x) q (f q y).
Proof. hammer_hook "EqdepFacts" "EqdepFacts.f_eq_dep". Restart. 
intros * []. reflexivity.
Qed.

Lemma eq_dep_non_dep :
forall U P p q x y, @eq_dep U (fun _ => P) p x q y -> x = y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.eq_dep_non_dep". Restart. 
intros * []. reflexivity.
Qed.

Lemma f_eq_dep_non_dep :
forall U (P:U->Type) R p q x y (f:forall p, P p -> R),
eq_dep p x q y -> f p x = f q y.
Proof. hammer_hook "EqdepFacts" "EqdepFacts.f_eq_dep_non_dep". Restart. 
intros * []. reflexivity.
Qed.

Arguments eq_dep  U P p x q _ : clear implicits.
Arguments eq_dep1 U P p x q y : clear implicits.
