From Hammer Require Import Hammer.











Set Implicit Arguments.

Unset Elimination Schemes.

Inductive JMeq (A:Type) (x:A) : forall B:Type, B -> Prop :=
JMeq_refl : JMeq x x.

Set Elimination Schemes.

Arguments JMeq_refl {A x} , [A] x.

Hint Resolve JMeq_refl.

Definition JMeq_hom {A : Type} (x y : A) := JMeq x y.

Lemma JMeq_sym : forall (A B:Type) (x:A) (y:B), JMeq x y -> JMeq y x.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_sym".  
intros; destruct H; trivial.
Qed.

Hint Immediate JMeq_sym.

Lemma JMeq_trans :
forall (A B C:Type) (x:A) (y:B) (z:C), JMeq x y -> JMeq y z -> JMeq x z.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_trans".  
destruct 2; trivial.
Qed.

Axiom JMeq_eq : forall (A:Type) (x y:A), JMeq x y -> x = y.

Lemma JMeq_ind : forall (A:Type) (x:A) (P:A -> Prop),
P x -> forall y, JMeq x y -> P y.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_ind".  
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rec : forall (A:Type) (x:A) (P:A -> Set),
P x -> forall y, JMeq x y -> P y.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_rec".  
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_rect : forall (A:Type) (x:A) (P:A->Type),
P x -> forall y, JMeq x y -> P y.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_rect".  
intros A x P H y H'; case JMeq_eq with (1 := H'); trivial.
Qed.

Lemma JMeq_ind_r : forall (A:Type) (x:A) (P:A -> Prop),
P x -> forall y, JMeq y x -> P y.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_ind_r".  
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_rec_r : forall (A:Type) (x:A) (P:A -> Set),
P x -> forall y, JMeq y x -> P y.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_rec_r".  
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_rect_r : forall (A:Type) (x:A) (P:A -> Type),
P x -> forall y, JMeq y x -> P y.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_rect_r".  
intros A x P H y H'; case JMeq_eq with (1 := JMeq_sym H'); trivial.
Qed.

Lemma JMeq_congr :
forall (A:Type) (x:A) (B:Type) (f:A->B) (y:A), JMeq x y -> f x = f y.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_congr".  
intros A x B f y H; case JMeq_eq with (1 := H); trivial.
Qed.



Require Import Eqdep.

Lemma JMeq_eq_dep_id :
forall (A B:Type) (x:A) (y:B), JMeq x y -> eq_dep Type (fun X => X) A x B y.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_eq_dep_id".  
destruct 1.
apply eq_dep_intro.
Qed.

Lemma eq_dep_id_JMeq :
forall (A B:Type) (x:A) (y:B), eq_dep Type (fun X => X) A x B y -> JMeq x y.
Proof. try hammer_hook "JMeq" "JMeq.eq_dep_id_JMeq".  
destruct 1.
apply JMeq_refl.
Qed.



Lemma eq_dep_JMeq :
forall U P p x q y, eq_dep U P p x q y -> JMeq x y.
Proof. try hammer_hook "JMeq" "JMeq.eq_dep_JMeq".  
destruct 1.
apply JMeq_refl.
Qed.

Lemma eq_dep_strictly_stronger_JMeq :
exists U P p q x y, JMeq x y /\ ~ eq_dep U P p x q y.
Proof. try hammer_hook "JMeq" "JMeq.eq_dep_strictly_stronger_JMeq".  
exists bool. exists (fun _ => True). exists true. exists false.
exists I. exists I.
split.
trivial.
intro H.
assert (true=false) by (destruct H; reflexivity).
discriminate.
Qed.



Lemma JMeq_eq_dep :
forall U (P:U->Type) p q (x:P p) (y:P q),
p = q -> JMeq x y -> eq_dep U P p x q y.
Proof. try hammer_hook "JMeq" "JMeq.JMeq_eq_dep".  
intros.
destruct H.
apply JMeq_eq in H0 as ->.
reflexivity.
Qed.



Notation sym_JMeq := JMeq_sym (only parsing).
Notation trans_JMeq := JMeq_trans (only parsing).
