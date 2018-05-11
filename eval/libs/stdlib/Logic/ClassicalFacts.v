From Hammer Require Import Hammer.

















Definition prop_degeneracy := forall A:Prop, A = True \/ A = False.


Definition prop_extensionality := forall A B:Prop, (A <-> B) -> A = B.


Definition excluded_middle := forall A:Prop, A \/ ~ A.



Lemma prop_degen_ext : prop_degeneracy -> prop_extensionality.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.prop_degen_ext".  
intros H A B [Hab Hba].
destruct (H A); destruct (H B).
rewrite H1; exact H0.
absurd B.
rewrite H1; exact (fun H => H).
apply Hab; rewrite H0; exact I.
absurd A.
rewrite H0; exact (fun H => H).
apply Hba; rewrite H1; exact I.
rewrite H1; exact H0.
Qed.

Lemma prop_degen_em : prop_degeneracy -> excluded_middle.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.prop_degen_em".  
intros H A.
destruct (H A).
left; rewrite H0; exact I.
right; rewrite H0; exact (fun x => x).
Qed.

Lemma prop_ext_em_degen :
prop_extensionality -> excluded_middle -> prop_degeneracy.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.prop_ext_em_degen".  
intros Ext EM A.
destruct (EM A).
left; apply (Ext A True); split;
[ exact (fun _ => I) | exact (fun _ => H) ].
right; apply (Ext A False); split; [ exact H | apply False_ind ].
Qed.



Require Import PropExtensionalityFacts.

Definition provable_prop_extensionality := forall A:Prop, A -> A = True.

Lemma provable_prop_ext :
prop_extensionality -> provable_prop_extensionality.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.provable_prop_ext".  
exact PropExt_imp_ProvPropExt.
Qed.









Local Notation inhabited A := A (only parsing).

Lemma prop_ext_A_eq_A_imp_A :
prop_extensionality -> forall A:Prop, inhabited A -> (A -> A) = A.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.prop_ext_A_eq_A_imp_A".  
intros Ext A a.
apply (Ext (A -> A) A); split; [ exact (fun _ => a) | exact (fun _ _ => a) ].
Qed.

Record retract (A B:Prop) : Prop :=
{f1 : A -> B; f2 : B -> A; f1_o_f2 : forall x:B, f1 (f2 x) = x}.

Lemma prop_ext_retract_A_A_imp_A :
prop_extensionality -> forall A:Prop, inhabited A -> retract A (A -> A).
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.prop_ext_retract_A_A_imp_A".  
intros Ext A a.
rewrite (prop_ext_A_eq_A_imp_A Ext A a).
exists (fun x:A => x) (fun x:A => x).
reflexivity.
Qed.

Record has_fixpoint (A:Prop) : Prop :=
{F : (A -> A) -> A; Fix : forall f:A -> A, F f = f (F f)}.

Lemma ext_prop_fixpoint :
prop_extensionality -> forall A:Prop, inhabited A -> has_fixpoint A.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.ext_prop_fixpoint".  
intros Ext A a.
case (prop_ext_retract_A_A_imp_A Ext A a); intros g1 g2 g1_o_g2.
exists (fun f => (fun x:A => f (g1 x x)) (g2 (fun x => f (g1 x x)))).
intro f.
pattern (g1 (g2 (fun x:A => f (g1 x x)))) at 1.
rewrite (g1_o_g2 (fun x:A => f (g1 x x))).
reflexivity.
Qed.







Definition proof_irrelevance := forall (A:Prop) (a1 a2:A), a1 = a2.



Section Proof_irrelevance_gen.

Variable bool : Prop.
Variable true : bool.
Variable false : bool.
Hypothesis bool_elim : forall C:Prop, C -> C -> bool -> C.
Hypothesis
bool_elim_redl : forall (C:Prop) (c1 c2:C), c1 = bool_elim C c1 c2 true.
Hypothesis
bool_elim_redr : forall (C:Prop) (c1 c2:C), c2 = bool_elim C c1 c2 false.
Let bool_dep_induction :=
forall P:bool -> Prop, P true -> P false -> forall b:bool, P b.

Lemma aux : prop_extensionality -> bool_dep_induction -> true = false.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.aux".  
intros Ext Ind.
case (ext_prop_fixpoint Ext bool true); intros G Gfix.
set (neg := fun b:bool => bool_elim bool false true b).
generalize (eq_refl (G neg)).
pattern (G neg) at 1.
apply Ind with (b := G neg); intro Heq.
rewrite (bool_elim_redl bool false true).
change (true = neg true); rewrite Heq; apply Gfix.
rewrite (bool_elim_redr bool false true).
change (neg false = false); rewrite Heq; symmetry ;
apply Gfix.
Qed.

Lemma ext_prop_dep_proof_irrel_gen :
prop_extensionality -> bool_dep_induction -> proof_irrelevance.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.ext_prop_dep_proof_irrel_gen".  
intros Ext Ind A a1 a2.
set (f := fun b:bool => bool_elim A a1 a2 b).
rewrite (bool_elim_redl A a1 a2).
change (f true = a2).
rewrite (bool_elim_redr A a1 a2).
change (f true = f false).
rewrite (aux Ext Ind).
reflexivity.
Qed.

End Proof_irrelevance_gen.



Section Proof_irrelevance_Prop_Ext_CC.

Definition BoolP := forall C:Prop, C -> C -> C.
Definition TrueP : BoolP := fun C c1 c2 => c1.
Definition FalseP : BoolP := fun C c1 c2 => c2.
Definition BoolP_elim C c1 c2 (b:BoolP) := b C c1 c2.
Definition BoolP_elim_redl (C:Prop) (c1 c2:C) :
c1 = BoolP_elim C c1 c2 TrueP := eq_refl c1.
Definition BoolP_elim_redr (C:Prop) (c1 c2:C) :
c2 = BoolP_elim C c1 c2 FalseP := eq_refl c2.

Definition BoolP_dep_induction :=
forall P:BoolP -> Prop, P TrueP -> P FalseP -> forall b:BoolP, P b.

Lemma ext_prop_dep_proof_irrel_cc :
prop_extensionality -> BoolP_dep_induction -> proof_irrelevance.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.ext_prop_dep_proof_irrel_cc".  
exact (ext_prop_dep_proof_irrel_gen BoolP TrueP FalseP BoolP_elim BoolP_elim_redl
BoolP_elim_redr).
Qed.

End Proof_irrelevance_Prop_Ext_CC.








Section Proof_irrelevance_CIC.

Inductive boolP : Prop :=
| trueP : boolP
| falseP : boolP.
Definition boolP_elim_redl (C:Prop) (c1 c2:C) :
c1 = boolP_ind C c1 c2 trueP := eq_refl c1.
Definition boolP_elim_redr (C:Prop) (c1 c2:C) :
c2 = boolP_ind C c1 c2 falseP := eq_refl c2.
Scheme boolP_indd := Induction for boolP Sort Prop.

Lemma ext_prop_dep_proof_irrel_cic : prop_extensionality -> proof_irrelevance.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.ext_prop_dep_proof_irrel_cic".  
exact (fun pe =>
ext_prop_dep_proof_irrel_gen boolP trueP falseP boolP_ind boolP_elim_redl
boolP_elim_redr pe boolP_indd).
Qed.

End Proof_irrelevance_CIC.








Require Import Hurkens.

Section Proof_irrelevance_EM_CC.

Variable or : Prop -> Prop -> Prop.
Variable or_introl : forall A B:Prop, A -> or A B.
Variable or_intror : forall A B:Prop, B -> or A B.
Hypothesis or_elim : forall A B C:Prop, (A -> C) -> (B -> C) -> or A B -> C.
Hypothesis
or_elim_redl :
forall (A B C:Prop) (f:A -> C) (g:B -> C) (a:A),
f a = or_elim A B C f g (or_introl A B a).
Hypothesis
or_elim_redr :
forall (A B C:Prop) (f:A -> C) (g:B -> C) (b:B),
g b = or_elim A B C f g (or_intror A B b).
Hypothesis
or_dep_elim :
forall (A B:Prop) (P:or A B -> Prop),
(forall a:A, P (or_introl A B a)) ->
(forall b:B, P (or_intror A B b)) -> forall b:or A B, P b.

Hypothesis em : forall A:Prop, or A (~ A).
Variable B : Prop.
Variables b1 b2 : B.



Let p2b A := or_elim A (~ A) B (fun _ => b1) (fun _ => b2) (em A).
Let b2p b := b1 = b.

Lemma p2p1 : forall A:Prop, A -> b2p (p2b A).
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.p2p1".  
unfold p2b; intro A; apply or_dep_elim with (b := em A);
unfold b2p; intros.
apply (or_elim_redl A (~ A) B (fun _ => b1) (fun _ => b2)).
destruct (b H).
Qed.

Lemma p2p2 : b1 <> b2 -> forall A:Prop, b2p (p2b A) -> A.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.p2p2".  
intro not_eq_b1_b2.
unfold p2b; intro A; apply or_dep_elim with (b := em A);
unfold b2p; intros.
assumption.
destruct not_eq_b1_b2.
rewrite <- (or_elim_redr A (~ A) B (fun _ => b1) (fun _ => b2)) in H.
assumption.
Qed.



Theorem proof_irrelevance_cc : b1 = b2.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.proof_irrelevance_cc".  
refine (or_elim _ _ _ _ _ (em (b1 = b2))); intro H.
trivial.
apply (NoRetractFromSmallPropositionToProp.paradox B p2b b2p (p2p2 H) p2p1).
Qed.

End Proof_irrelevance_EM_CC.



Section Proof_irrelevance_WEM_CC.

Variable or : Prop -> Prop -> Prop.
Variable or_introl : forall A B:Prop, A -> or A B.
Variable or_intror : forall A B:Prop, B -> or A B.
Hypothesis or_elim : forall A B C:Prop, (A -> C) -> (B -> C) -> or A B -> C.
Hypothesis
or_elim_redl :
forall (A B C:Prop) (f:A -> C) (g:B -> C) (a:A),
f a = or_elim A B C f g (or_introl A B a).
Hypothesis
or_elim_redr :
forall (A B C:Prop) (f:A -> C) (g:B -> C) (b:B),
g b = or_elim A B C f g (or_intror A B b).
Hypothesis
or_dep_elim :
forall (A B:Prop) (P:or A B -> Prop),
(forall a:A, P (or_introl A B a)) ->
(forall b:B, P (or_intror A B b)) -> forall b:or A B, P b.

Hypothesis wem : forall A:Prop, or (~~A) (~ A).

Local Notation NProp := NoRetractToNegativeProp.NProp.
Local Notation El := NoRetractToNegativeProp.El.

Variable B : Prop.
Variables b1 b2 : B.



Let p2b (A:NProp) := or_elim (~~El A) (~El A) B (fun _ => b1) (fun _ => b2) (wem (El A)).
Let b2p b : NProp := exist (fun P=>~~P -> P) (~~(b1 = b)) (fun h x => h (fun k => k x)).

Lemma wp2p1 : forall A:NProp, El A -> El (b2p (p2b A)).
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.wp2p1".  
intros A. unfold p2b.
apply or_dep_elim with  (b := wem (El A)).
+ intros nna a.
rewrite <- or_elim_redl.
cbn. auto.
+ intros n x.
destruct (n x).
Qed.

Lemma wp2p2 : b1 <> b2 -> forall A:NProp, El (b2p (p2b A)) -> El A.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.wp2p2".  
intro not_eq_b1_b2.
intros A. unfold p2b.
apply or_dep_elim with  (b := wem (El A)).
+ cbn.
intros x _.
destruct A. cbn in x |- *.
auto.
+ intros na.
rewrite <- or_elim_redr. cbn.
intros h. destruct (h not_eq_b1_b2).
Qed.



Theorem wproof_irrelevance_cc : ~~(b1 = b2).
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.wproof_irrelevance_cc".  
intros h.
unshelve (refine (let NB := exist (fun P=>~~P -> P) B _ in _)).
{ exact (fun _ => b1). }
pose proof (NoRetractToNegativeProp.paradox NB p2b b2p (wp2p2 h) wp2p1) as paradox.
unshelve (refine (let F := exist (fun P=>~~P->P) False _ in _)).
{ auto. }
exact (paradox F).
Qed.

End Proof_irrelevance_WEM_CC.






Section Proof_irrelevance_CCI.

Hypothesis em : forall A:Prop, A \/ ~ A.

Definition or_elim_redl (A B C:Prop) (f:A -> C) (g:B -> C)
(a:A) : f a = or_ind f g (or_introl B a) := eq_refl (f a).
Definition or_elim_redr (A B C:Prop) (f:A -> C) (g:B -> C)
(b:B) : g b = or_ind f g (or_intror A b) := eq_refl (g b).
Scheme or_indd := Induction for or Sort Prop.

Theorem proof_irrelevance_cci : forall (B:Prop) (b1 b2:B), b1 = b2.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.proof_irrelevance_cci".  
exact (proof_irrelevance_cc or or_introl or_intror or_ind or_elim_redl
or_elim_redr or_indd em).
Qed.

End Proof_irrelevance_CCI.





Section Weak_proof_irrelevance_CCI.

Hypothesis wem : forall A:Prop, ~~A \/ ~ A.

Theorem wem_proof_irrelevance_cci : forall (B:Prop) (b1 b2:B), ~~b1 = b2.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.wem_proof_irrelevance_cci".  
exact (wproof_irrelevance_cc or or_introl or_intror or_ind or_elim_redl
or_elim_redr or_indd wem).
Qed.

End Weak_proof_irrelevance_CCI.











Definition weak_excluded_middle :=
forall A:Prop, ~~A \/ ~A.



Definition weak_generalized_excluded_middle :=
forall A B:Prop, ((A -> B) -> B) \/ (A -> B).





Definition GodelDummett := forall A B:Prop, (A -> B) \/ (B -> A).

Lemma excluded_middle_Godel_Dummett : excluded_middle -> GodelDummett.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.excluded_middle_Godel_Dummett".  
intros EM A B. destruct (EM B) as [HB|HnotB].
left; intros _; exact HB.
right; intros HB; destruct (HnotB HB).
Qed.



Definition RightDistributivityImplicationOverDisjunction :=
forall A B C:Prop, (C -> A\/B) -> (C->A) \/ (C->B).

Lemma Godel_Dummett_iff_right_distr_implication_over_disjunction :
GodelDummett <-> RightDistributivityImplicationOverDisjunction.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.Godel_Dummett_iff_right_distr_implication_over_disjunction".  
split.
intros GD A B C HCAB.
destruct (GD B A) as [HBA|HAB]; [left|right]; intro HC;
destruct (HCAB HC) as [HA|HB]; [ | apply HBA | apply HAB | ]; assumption.
intros Distr A B.
destruct (Distr A B (A\/B)) as [HABA|HABB].
intro HAB; exact HAB.
right; intro HB; apply HABA; right; assumption.
left; intro HA; apply HABB; left; assumption.
Qed.



Lemma Godel_Dummett_weak_excluded_middle :
GodelDummett -> weak_excluded_middle.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.Godel_Dummett_weak_excluded_middle".  
intros GD A. destruct (GD (~A) A) as [HnotAA|HAnotA].
left; intro HnotA; apply (HnotA (HnotAA HnotA)).
right; intro HA; apply (HAnotA HA HA).
Qed.





Definition IndependenceOfGeneralPremises :=
forall (A:Type) (P:A -> Prop) (Q:Prop),
inhabited A -> (Q -> exists x, P x) -> exists x, Q -> P x.

Lemma
independence_general_premises_right_distr_implication_over_disjunction :
IndependenceOfGeneralPremises -> RightDistributivityImplicationOverDisjunction.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.IndependenceOfGeneralPremises".  
intros IP A B C HCAB.
destruct (IP bool (fun b => if b then A else B) C true) as ([|],H).
intro HC; destruct (HCAB HC); [exists true|exists false]; assumption.
left; assumption.
right; assumption.
Qed.

Lemma independence_general_premises_Godel_Dummett :
IndependenceOfGeneralPremises -> GodelDummett.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.independence_general_premises_Godel_Dummett".  
destruct Godel_Dummett_iff_right_distr_implication_over_disjunction.
auto using independence_general_premises_right_distr_implication_over_disjunction.
Qed.



Definition DrinkerParadox :=
forall (A:Type) (P:A -> Prop),
inhabited A -> exists x, (exists x, P x) -> P x.

Lemma independence_general_premises_drinker :
IndependenceOfGeneralPremises <-> DrinkerParadox.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.independence_general_premises_drinker".  
split.
intros IP A P InhA; apply (IP A P (exists x, P x) InhA); intro Hx; exact Hx.
intros Drinker A P Q InhA H; destruct (Drinker A P InhA) as (x,Hx).
exists x; intro HQ; apply (Hx (H HQ)).
Qed.



Definition generalized_excluded_middle :=
forall A B:Prop, A \/ (A -> B).

Lemma excluded_middle_independence_general_premises :
generalized_excluded_middle -> DrinkerParadox.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.excluded_middle_independence_general_premises".  
intros GEM A P x0.
destruct (GEM (exists x, P x) (P x0)) as [(x,Hx)|Hnot].
exists x; intro; exact Hx.
exists x0; exact Hnot.
Qed.





Require Import Coq.Arith.PeanoNat.

Definition Minimal (P:nat -> Prop) (n:nat) : Prop :=
P n /\ forall k, P k -> n<=k.

Definition Minimization_Property (P : nat -> Prop) : Prop :=
forall n, P n -> exists m, Minimal P m.

Section Unrestricted_minimization_entails_excluded_middle.

Hypothesis unrestricted_minimization: forall P, Minimization_Property P.

Theorem unrestricted_minimization_entails_excluded_middle : forall A, A\/~A.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.unrestricted_minimization_entails_excluded_middle".  
intros A.
pose (P := fun n:nat => n=0/\A \/ n=1).
assert (P 1) as h.
{ unfold P. intuition. }
assert (P 0 <-> A) as p₀.
{ split.
+ intros [[_ h₀]|[=]]. assumption.
+ unfold P. tauto. }
apply unrestricted_minimization in h as ([|[|m]] & hm & hmm).
+ intuition.
+ right.
intros HA. apply p₀, hmm, PeanoNat.Nat.nle_succ_0 in HA. assumption.
+ destruct hm as [([=],_) | [=] ].
Qed.

End Unrestricted_minimization_entails_excluded_middle.

Require Import Wf_nat.

Section Excluded_middle_entails_unrestricted_minimization.

Hypothesis em : forall A, A\/~A.

Theorem excluded_middle_entails_unrestricted_minimization :
forall P, Minimization_Property P.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.excluded_middle_entails_unrestricted_minimization".  
intros P n HPn.
assert (dec : forall n, P n \/ ~ P n) by auto using em.
assert (ex : exists n, P n) by (exists n; assumption).
destruct (dec_inh_nat_subset_has_unique_least_element P dec ex) as (n' & HPn' & _).
exists n'. assumption.
Qed.

End Excluded_middle_entails_unrestricted_minimization.



Section Example_of_undecidable_predicate_with_the_minimization_property.

Variable s : nat -> bool.

Let P n := exists k, n<=k /\ s k = true.

Example undecidable_predicate_with_the_minimization_property :
Minimization_Property P.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.undecidable_predicate_with_the_minimization_property".  
unfold Minimization_Property.
intros h hn.
exists 0. split.
+ unfold P in *. destruct hn as (k&hk₁&hk₂).
exists k. split.
* rewrite <- hk₁.
apply PeanoNat.Nat.le_0_l.
* assumption.
+ intros **. apply PeanoNat.Nat.le_0_l.
Qed.

End Example_of_undecidable_predicate_with_the_minimization_property.





Require Import RelationClasses.

Local Notation representative_boolean_partition :=
(forall R:bool->bool->Prop,
Equivalence R -> exists f, forall x, R x (f x) /\ forall y, R x y -> f x = f y).

Theorem representative_boolean_partition_imp_excluded_middle :
representative_boolean_partition -> excluded_middle.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.representative_boolean_partition_imp_excluded_middle".  
intros ReprFunChoice P.
pose (R (b1 b2 : bool) := b1 = b2 \/ P).
assert (Equivalence R).
{ split.
- now left.
- destruct 1. now left. now right.
- destruct 1, 1; try now right. left; now transitivity y. }
destruct (ReprFunChoice R H) as (f,Hf). clear H.
destruct (Bool.bool_dec (f true) (f false)) as [Heq|Hneq].
+ left.
destruct (Hf false) as ([Hfalse|HP],_); try easy.
destruct (Hf true) as ([Htrue|HP],_); try easy.
congruence.
+ right. intro HP.
destruct (Hf true) as (_,H). apply Hneq, H. now right.
Qed.

Theorem excluded_middle_imp_representative_boolean_partition :
excluded_middle -> representative_boolean_partition.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.excluded_middle_imp_representative_boolean_partition".  
intros EM R H.
destruct (EM (R true false)).
- exists (fun _ => true).
intros []; firstorder.
- exists (fun b => b).
intro b. split.
+ reflexivity.
+ destruct b, y; intros HR; easy || now symmetry in HR.
Qed.

Theorem excluded_middle_iff_representative_boolean_partition :
excluded_middle <-> representative_boolean_partition.
Proof. try hammer_hook "ClassicalFacts" "ClassicalFacts.excluded_middle_iff_representative_boolean_partition".  
split; auto using excluded_middle_imp_representative_boolean_partition,
representative_boolean_partition_imp_excluded_middle.
Qed.
