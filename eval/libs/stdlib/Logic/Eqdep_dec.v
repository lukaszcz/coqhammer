From Hammer Require Import Hammer.

















Set Implicit Arguments.


Section EqdepDec.

Variable A : Type.

Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
eq_ind _ (fun a => a = y') eq2 _ eq1.

Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = eq_refl y.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.trans_sym_eq". Restart. 
intros.
case u; trivial.
Qed.

Variable x : A.

Variable eq_dec : forall y:A, x = y \/ x <> y.

Let nu (y:A) (u:x = y) : x = y :=
match eq_dec y with
| or_introl eqxy => eqxy
| or_intror neqxy => False_ind _ (neqxy u)
end.

Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
intros.
unfold nu.
destruct (eq_dec y) as [Heq|Hneq].
reflexivity.

case Hneq; trivial.
Qed.


Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (eq_refl x)) v.


Remark nu_left_inv_on : forall (y:A) (u:x = y), nu_inv (nu u) = u.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.nu_left_inv_on". Restart. 
intros.
case u; unfold nu_inv.
apply trans_sym_eq.
Qed.


Theorem eq_proofs_unicity_on : forall (y:A) (p1 p2:x = y), p1 = p2.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.eq_proofs_unicity_on". Restart. 
intros.
elim nu_left_inv_on with (u := p1).
elim nu_left_inv_on with (u := p2).
elim nu_constant with y p1 p2.
reflexivity.
Qed.

Theorem K_dec_on :
forall P:x = x -> Prop, P (eq_refl x) -> forall p:x = x, P p.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.K_dec_on". Restart. 
intros.
elim eq_proofs_unicity_on with x (eq_refl x) p.
trivial.
Qed.



Let proj (P:A -> Prop) (exP:ex P) (def:P x) : P x :=
match exP with
| ex_intro _ x' prf =>
match eq_dec x' with
| or_introl eqprf => eq_ind x' P prf x (eq_sym eqprf)
| _ => def
end
end.


Theorem inj_right_pair_on :
forall (P:A -> Prop) (y y':P x),
ex_intro P x y = ex_intro P x y' -> y = y'.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.inj_right_pair_on". Restart. 
intros.
cut (proj (ex_intro P x y) y = proj (ex_intro P x y') y).
simpl.
destruct (eq_dec x) as [Heq|Hneq].
elim Heq using K_dec_on; trivial.

intros.
case Hneq; trivial.

case H.
reflexivity.
Qed.

End EqdepDec.



Theorem eq_proofs_unicity A (eq_dec : forall x y : A, x = y \/ x <> y) (x : A)
: forall (y:A) (p1 p2:x = y), p1 = p2.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.eq_proofs_unicity". Restart. exact ((@eq_proofs_unicity_on A x (eq_dec x))). Qed.

Theorem K_dec A (eq_dec : forall x y : A, x = y \/ x <> y) (x : A)
: forall P:x = x -> Prop, P (eq_refl x) -> forall p:x = x, P p.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.K_dec". Restart. exact ((@K_dec_on A x (eq_dec x))). Qed.

Theorem inj_right_pair A (eq_dec : forall x y : A, x = y \/ x <> y) (x : A)
: forall (P:A -> Prop) (y y':P x),
ex_intro P x y = ex_intro P x y' -> y = y'.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.inj_right_pair". Restart. exact ((@inj_right_pair_on A x (eq_dec x))). Qed.

Require Import EqdepFacts.


Theorem K_dec_type :
forall A:Type,
(forall x y:A, {x = y} + {x <> y}) ->
forall (x:A) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.K_dec_type". Restart. 
intros A eq_dec x P H p.
elim p using K_dec; intros.
case (eq_dec x0 y); [left|right]; assumption.
trivial.
Qed.

Theorem K_dec_set :
forall A:Set,
(forall x y:A, {x = y} + {x <> y}) ->
forall (x:A) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.K_dec_set". Restart. exact (fun A => K_dec_type (A:=A)). Qed.


Theorem eq_rect_eq_dec :
forall A:Type,
(forall x y:A, {x = y} + {x <> y}) ->
forall (p:A) (Q:A -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.eq_rect_eq_dec". Restart. 
intros A eq_dec.
apply (Streicher_K__eq_rect_eq A (K_dec_type eq_dec)).
Qed.


Theorem eq_dep_eq_dec :
forall A:Type,
(forall x y:A, {x = y} + {x <> y}) ->
forall (P:A->Type) (p:A) (x y:P p), eq_dep A P p x p y -> x = y.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.eq_dep_eq_dec". Restart. exact ((fun A eq_dec => eq_rect_eq__eq_dep_eq A (eq_rect_eq_dec eq_dec))). Qed.

Theorem UIP_dec :
forall (A:Type),
(forall x y:A, {x = y} + {x <> y}) ->
forall (x y:A) (p1 p2:x = y), p1 = p2.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.UIP_dec". Restart. exact ((fun A eq_dec => eq_dep_eq__UIP A (eq_dep_eq_dec eq_dec))). Qed.

Unset Implicit Arguments.






Module Type DecidableType.

Monomorphic Parameter U:Type.
Axiom eq_dec : forall x y:U, {x = y} + {x <> y}.

End DecidableType.



Module DecidableEqDep (M:DecidableType).

Import M.



Lemma eq_rect_eq :
forall (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDep.eq_rect_eq". Restart. exact (eq_rect_eq_dec eq_dec). Qed.



Theorem eq_dep_eq :
forall (P:U->Type) (p:U) (x y:P p), eq_dep U P p x p y -> x = y.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDep.eq_dep_eq". Restart. exact ((eq_rect_eq__eq_dep_eq U eq_rect_eq)). Qed.



Lemma UIP : forall (x y:U) (p1 p2:x = y), p1 = p2.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDep.UIP". Restart. exact ((eq_dep_eq__UIP U eq_dep_eq)). Qed.



Lemma UIP_refl : forall (x:U) (p:x = x), p = eq_refl x.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDep.UIP_refl". Restart. exact ((UIP__UIP_refl U UIP)). Qed.



Lemma Streicher_K :
forall (x:U) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDep.Streicher_K". Restart. exact ((K_dec_type eq_dec)). Qed.



Lemma inj_pairT2 :
forall (P:U -> Type) (p:U) (x y:P p),
existT P p x = existT P p y -> x = y.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDep.inj_pairT2". Restart. exact (eq_dep_eq__inj_pairT2 U eq_dep_eq). Qed.



Lemma inj_pairP2 :
forall (P:U -> Prop) (x:U) (p q:P x),
ex_intro P x p = ex_intro P x q -> p = q.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDep.inj_pairP2". Restart. 
intros.
apply inj_right_pair with (A:=U).
intros x0 y0; case (eq_dec x0 y0); [left|right]; assumption.
assumption.
Qed.

End DecidableEqDep.






Module Type DecidableSet.

Parameter U:Set.
Axiom eq_dec : forall x y:U, {x = y} + {x <> y}.

End DecidableSet.



Module DecidableEqDepSet (M:DecidableSet).

Import M.
Module N:=DecidableEqDep(M).



Lemma eq_rect_eq :
forall (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDepSet.eq_rect_eq". Restart. exact (eq_rect_eq_dec eq_dec). Qed.



Theorem eq_dep_eq :
forall (P:U->Type) (p:U) (x y:P p), eq_dep U P p x p y -> x = y.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDepSet.eq_dep_eq". Restart. exact ((eq_rect_eq__eq_dep_eq U eq_rect_eq)). Qed.



Lemma UIP : forall (x y:U) (p1 p2:x = y), p1 = p2.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDepSet.UIP". Restart. exact ((eq_dep_eq__UIP U eq_dep_eq)). Qed.



Lemma UIP_refl : forall (x:U) (p:x = x), p = eq_refl x.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDepSet.UIP_refl". Restart. exact ((UIP__UIP_refl U UIP)). Qed.



Lemma Streicher_K :
forall (x:U) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDepSet.Streicher_K". Restart. exact ((K_dec_type eq_dec)). Qed.



Lemma inj_pairP2 :
forall (P:U -> Prop) (x:U) (p q:P x),
ex_intro P x p = ex_intro P x q -> p = q.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDepSet.inj_pairP2". Restart. exact (N.inj_pairP2). Qed.



Lemma inj_pair2 :
forall (P:U -> Type) (p:U) (x y:P p),
existT P p x = existT P p y -> x = y.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.DecidableEqDepSet.inj_pair2". Restart. exact (eq_dep_eq__inj_pair2 U N.eq_dep_eq). Qed.



Notation inj_pairT2 := inj_pair2.

End DecidableEqDepSet.


Lemma inj_pair2_eq_dec : forall A:Type, (forall x y:A, {x=y}+{x<>y}) ->
( forall (P:A -> Type) (p:A) (x y:P p), existT P p x = existT P p y -> x = y ).
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.inj_pair2_eq_dec". Restart. 
intros A eq_dec.
apply eq_dep_eq__inj_pair2.
apply eq_rect_eq__eq_dep_eq.
unfold Eq_rect_eq, Eq_rect_eq_on.
intros; apply eq_rect_eq_dec.
apply eq_dec.
Qed.



Lemma UIP_refl_unit (x : tt = tt) : x = eq_refl tt.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.UIP_refl_unit". Restart. 
change (match tt as b return tt = b -> Prop with
| tt => fun x => x = eq_refl tt
end x).
destruct x; reflexivity.
Defined.

Lemma UIP_refl_bool (b:bool) (x : b = b) : x = eq_refl.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.UIP_refl_bool". Restart. 
destruct b.
- change (match true as b return true=b -> Prop with
| true => fun x => x = eq_refl
| _ => fun _ => True
end x).
destruct x; reflexivity.
- change (match false as b return false=b -> Prop with
| false => fun x => x = eq_refl
| _ => fun _ => True
end x).
destruct x; reflexivity.
Defined.

Lemma UIP_refl_nat (n:nat) (x : n = n) : x = eq_refl.
Proof. hammer_hook "Eqdep_dec" "Eqdep_dec.UIP_refl_nat". Restart. 
induction n.
- change (match 0 as n return 0=n -> Prop with
| 0 => fun x => x = eq_refl
| _ => fun _ => True
end x).
destruct x; reflexivity.
- specialize IHn with (f_equal pred x).
change eq_refl with (f_equal S (@eq_refl _ n)).
rewrite <- IHn; clear IHn.
change (match S n as n' return S n = n' -> Prop with
| 0 => fun _ => True
| S n' => fun x =>
x = f_equal S (f_equal pred x)
end x).
pattern (S n) at 2 3, x.
destruct x; reflexivity.
Defined.
