From Hammer Require Import Hammer.











Set Implicit Arguments.

Section Berardis_paradox.


Hypothesis EM : forall P:Prop, P \/ ~ P.


Definition IFProp (P B:Prop) (e1 e2:P) :=
match EM B with
| or_introl _ => e1
| or_intror _ => e2
end.


Lemma AC_IF :
forall (P B:Prop) (e1 e2:P) (Q:P -> Prop),
(B -> Q e1) -> (~ B -> Q e2) -> Q (IFProp B e1 e2).
Proof. hammer_hook "Berardi" "Berardi.AC_IF".  
intros P B e1 e2 Q p1 p2.
unfold IFProp.
case (EM B); assumption.
Qed.



Variable Bool : Prop.
Variable T : Bool.
Variable F : Bool.


Definition pow (P:Prop) := P -> Bool.



Section Retracts.

Variables A B : Prop.

Record retract : Prop :=
{i : A -> B; j : B -> A; inv : forall a:A, j (i a) = a}.
Record retract_cond : Prop :=
{i2 : A -> B; j2 : B -> A; inv2 : retract -> forall a:A, j2 (i2 a) = a}.



Lemma AC : forall r:retract_cond, retract -> forall a:A, r.(j2) (r.(i2) a) = a.
Proof. hammer_hook "Berardi" "Berardi.AC".   intros r. exact r.(inv2). Qed.

End Retracts.



Lemma L1 : forall A B:Prop, retract_cond (pow A) (pow B).
Proof. hammer_hook "Berardi" "Berardi.L1".  
intros A B.
destruct (EM (retract (pow A) (pow B))) as [(f0,g0,e) | hf].
exists f0 g0; trivial.
exists (fun (x:pow A) (y:B) => F) (fun (x:pow B) (y:A) => F); intros;
destruct hf; auto.
Qed.



Definition U := forall P:Prop, pow P.


Definition f (u:U) : pow U := u U.

Definition g (h:pow U) : U :=
fun X => let lX := j2 (L1 X U) in let rU := i2 (L1 U U) in lX (rU h).


Lemma retract_pow_U_U : retract (pow U) U.
Proof. hammer_hook "Berardi" "Berardi.retract_pow_U_U".  
exists g f.
intro a.
unfold f, g; simpl.
apply AC.
exists (fun x:pow U => x) (fun x:pow U => x).
trivial.
Qed.




Definition Not_b (b:Bool) := IFProp (b = T) F T.


Definition R : U := g (fun u:U => Not_b (u U u)).


Lemma not_has_fixpoint : R R = Not_b (R R).
Proof. hammer_hook "Berardi" "Berardi.not_has_fixpoint".  
unfold R at 1.
unfold g.
rewrite AC.
trivial.
exists (fun x:pow U => x) (fun x:pow U => x).
trivial.
Qed.


Theorem classical_proof_irrelevence : T = F.
Proof. hammer_hook "Berardi" "Berardi.classical_proof_irrelevence".  
generalize not_has_fixpoint.
unfold Not_b.
apply AC_IF.
intros is_true is_false.
elim is_true; elim is_false; trivial.

intros not_true is_true.
elim not_true; trivial.
Qed.

End Berardis_paradox.
