From Hammer Require Import Hammer.














Set Implicit Arguments.
Local Unset Intuition Negation Unfolding.









Section ChoiceSchemes.

Variables A B :Type.

Variable P:A->Prop.





Definition RelationalChoice_on :=
forall R:A->B->Prop,
(forall x : A, exists y : B, R x y) ->
(exists R' : A->B->Prop, subrelation R' R /\ forall x, exists! y, R' x y).





Definition FunctionalChoice_on_rel (R:A->B->Prop) :=
(forall x:A, exists y : B, R x y) ->
exists f : A -> B, (forall x:A, R x (f x)).

Definition FunctionalChoice_on :=
forall R:A->B->Prop,
(forall x : A, exists y : B, R x y) ->
(exists f : A->B, forall x : A, R x (f x)).


Definition DependentFunctionalChoice_on (A:Type) (B:A -> Type) :=
forall R:forall x:A, B x -> Prop,
(forall x:A, exists y : B x, R x y) ->
(exists f : (forall x:A, B x), forall x:A, R x (f x)).


Definition InhabitedForallCommute_on (A : Type) (B : A -> Type) :=
(forall x, inhabited (B x)) -> inhabited (forall x, B x).



Definition FunctionalDependentChoice_on :=
forall (R:A->A->Prop),
(forall x, exists y, R x y) -> forall x0,
(exists f : nat -> A, f 0 = x0 /\ forall n, R (f n) (f (S n))).



Definition FunctionalCountableChoice_on :=
forall (R:nat->A->Prop),
(forall n, exists y, R n y) ->
(exists f : nat -> A, forall n, R n (f n)).



Definition FunctionalRelReification_on :=
forall R:A->B->Prop,
(forall x : A, exists! y : B, R x y) ->
(exists f : A->B, forall x : A, R x (f x)).


Definition DependentFunctionalRelReification_on (A:Type) (B:A -> Type) :=
forall (R:forall x:A, B x -> Prop),
(forall x:A, exists! y : B x, R x y) ->
(exists f : (forall x:A, B x), forall x:A, R x (f x)).





Require Import RelationClasses Logic.

Definition RepresentativeFunctionalChoice_on :=
forall R:A->A->Prop,
(Equivalence R) ->
(exists f : A->A, forall x : A, (R x (f x)) /\ forall x', R x x' -> f x = f x').



Definition SetoidFunctionalChoice_on :=
forall R : A -> A -> Prop,
forall T : A -> B -> Prop,
Equivalence R ->
(forall x x' y, R x x' -> T x y -> T x' y) ->
(forall x, exists y, T x y) ->
exists f : A -> B, forall x : A, T x (f x) /\ (forall x' : A, R x x' -> f x = f x').





Definition GeneralizedSetoidFunctionalChoice_on :=
forall R : A -> A -> Prop,
forall S : B -> B -> Prop,
forall T : A -> B -> Prop,
Equivalence R ->
Equivalence S ->
(forall x x' y y', R x x' -> S y y' -> T x y -> T x' y') ->
(forall x, exists y, T x y) ->
exists f : A -> B,
forall x : A, T x (f x) /\ (forall x' : A, R x x' -> S (f x) (f x')).



Definition SimpleSetoidFunctionalChoice_on A B :=
forall R : A -> A -> Prop,
forall T : A -> B -> Prop,
Equivalence R ->
(forall x, exists y, forall x', R x x' -> T x' y) ->
exists f : A -> B, forall x : A, T x (f x) /\ (forall x' : A, R x x' -> f x = f x').



Definition ConstructiveIndefiniteDescription_on :=
forall P:A->Prop,
(exists x, P x) -> { x:A | P x }.



Definition ConstructiveDefiniteDescription_on :=
forall P:A->Prop,
(exists! x, P x) -> { x:A | P x }.





Definition GuardedRelationalChoice_on :=
forall P : A->Prop, forall R : A->B->Prop,
(forall x : A, P x -> exists y : B, R x y) ->
(exists R' : A->B->Prop,
subrelation R' R /\ forall x, P x -> exists! y, R' x y).



Definition GuardedFunctionalChoice_on :=
forall P : A->Prop, forall R : A->B->Prop,
inhabited B ->
(forall x : A, P x -> exists y : B, R x y) ->
(exists f : A->B, forall x, P x -> R x (f x)).



Definition GuardedFunctionalRelReification_on :=
forall P : A->Prop, forall R : A->B->Prop,
inhabited B ->
(forall x : A, P x -> exists! y : B, R x y) ->
(exists f : A->B, forall x : A, P x -> R x (f x)).



Definition OmniscientRelationalChoice_on :=
forall R : A->B->Prop,
exists R' : A->B->Prop,
subrelation R' R /\ forall x : A, (exists y : B, R x y) -> exists! y, R' x y.



Definition OmniscientFunctionalChoice_on :=
forall R : A->B->Prop,
inhabited B ->
exists f : A->B, forall x : A, (exists y : B, R x y) -> R x (f x).



Definition EpsilonStatement_on :=
forall P:A->Prop,
inhabited A -> { x:A | (exists x, P x) -> P x }.



Definition IotaStatement_on :=
forall P:A->Prop,
inhabited A -> { x:A | (exists! x, P x) -> P x }.

End ChoiceSchemes.



Notation RelationalChoice :=
(forall A B : Type, RelationalChoice_on A B).
Notation FunctionalChoice :=
(forall A B : Type, FunctionalChoice_on A B).
Notation DependentFunctionalChoice :=
(forall A (B:A->Type), DependentFunctionalChoice_on B).
Notation InhabitedForallCommute :=
(forall A (B : A -> Type), InhabitedForallCommute_on B).
Notation FunctionalDependentChoice :=
(forall A : Type, FunctionalDependentChoice_on A).
Notation FunctionalCountableChoice :=
(forall A : Type, FunctionalCountableChoice_on A).
Notation FunctionalChoiceOnInhabitedSet :=
(forall A B : Type, inhabited B -> FunctionalChoice_on A B).
Notation FunctionalRelReification :=
(forall A B : Type, FunctionalRelReification_on A B).
Notation DependentFunctionalRelReification :=
(forall A (B:A->Type), DependentFunctionalRelReification_on B).
Notation RepresentativeFunctionalChoice :=
(forall A : Type, RepresentativeFunctionalChoice_on A).
Notation SetoidFunctionalChoice :=
(forall A  B: Type, SetoidFunctionalChoice_on A B).
Notation GeneralizedSetoidFunctionalChoice :=
(forall A B : Type, GeneralizedSetoidFunctionalChoice_on A B).
Notation SimpleSetoidFunctionalChoice :=
(forall A B : Type, SimpleSetoidFunctionalChoice_on A B).

Notation GuardedRelationalChoice :=
(forall A B : Type, GuardedRelationalChoice_on A B).
Notation GuardedFunctionalChoice :=
(forall A B : Type, GuardedFunctionalChoice_on A B).
Notation GuardedFunctionalRelReification :=
(forall A B : Type, GuardedFunctionalRelReification_on A B).

Notation OmniscientRelationalChoice :=
(forall A B : Type, OmniscientRelationalChoice_on A B).
Notation OmniscientFunctionalChoice :=
(forall A B : Type, OmniscientFunctionalChoice_on A B).

Notation ConstructiveDefiniteDescription :=
(forall A : Type, ConstructiveDefiniteDescription_on A).
Notation ConstructiveIndefiniteDescription :=
(forall A : Type, ConstructiveIndefiniteDescription_on A).

Notation IotaStatement :=
(forall A : Type, IotaStatement_on A).
Notation EpsilonStatement :=
(forall A : Type, EpsilonStatement_on A).




Definition ProofIrrelevance :=
forall (A:Prop) (a1 a2:A), a1 = a2.


Definition IndependenceOfGeneralPremises :=
forall (A:Type) (P:A -> Prop) (Q:Prop),
inhabited A ->
(Q -> exists x, P x) -> exists x, Q -> P x.


Definition SmallDrinker'sParadox :=
forall (A:Type) (P:A -> Prop), inhabited A ->
exists x, (exists x, P x) -> P x.


Definition ExcludedMiddle :=
forall P:Prop, P \/ ~ P.




Local Notation ExtensionalPropositionRepresentative :=
(forall (A:Type),
exists h : Prop -> Prop,
forall P : Prop, (P <-> h P) /\ forall Q, (P <-> Q) -> h P = h Q).


Local Notation ExtensionalPredicateRepresentative :=
(forall (A:Type),
exists h : (A->Prop) -> (A->Prop),
forall (P : A -> Prop), (forall x, P x <-> h P x) /\ forall Q, (forall x, P x <-> Q x) -> h P = h Q).


Local Notation ExtensionalFunctionRepresentative :=
(forall (A B:Type),
exists h : (A->B) -> (A->B),
forall (f : A -> B), (forall x, f x = h f x) /\ forall g, (forall x, f x = g x) -> h f = h g).














Lemma functional_rel_reification_and_rel_choice_imp_fun_choice :
forall A B : Type,
FunctionalRelReification_on A B -> RelationalChoice_on A B -> FunctionalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.functional_rel_reification_and_rel_choice_imp_fun_choice".  
intros A B Descr RelCh R H.
destruct (RelCh R H) as (R',(HR'R,H0)).
destruct (Descr R') as (f,Hf).
firstorder.
exists f; intro x.
destruct (H0 x) as (y,(HR'xy,Huniq)).
rewrite <- (Huniq (f x) (Hf x)).
apply HR'R; assumption.
Qed.

Lemma fun_choice_imp_rel_choice :
forall A B : Type, FunctionalChoice_on A B -> RelationalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_choice_imp_rel_choice".  
intros A B FunCh R H.
destruct (FunCh R H) as (f,H0).
exists (fun x y => f x = y).
split.
intros x y Heq; rewrite <- Heq; trivial.
intro x; exists (f x); split.
reflexivity.
trivial.
Qed.

Lemma fun_choice_imp_functional_rel_reification :
forall A B : Type, FunctionalChoice_on A B -> FunctionalRelReification_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_choice_imp_functional_rel_reification".  
intros A B FunCh R H.
destruct (FunCh R) as [f H0].

intro x.
destruct (H x) as (y,(HRxy,_)).
exists y; exact HRxy.

exists f; exact H0.
Qed.

Corollary fun_choice_iff_rel_choice_and_functional_rel_reification :
forall A B : Type, FunctionalChoice_on A B <->
RelationalChoice_on A B /\ FunctionalRelReification_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_choice_iff_rel_choice_and_functional_rel_reification".  
intros A B. split.
intro H; split;
[ exact (fun_choice_imp_rel_choice H)
| exact (fun_choice_imp_functional_rel_reification H) ].
intros [H H0]; exact (functional_rel_reification_and_rel_choice_imp_fun_choice H0 H).
Qed.









Lemma rel_choice_and_proof_irrel_imp_guarded_rel_choice :
RelationalChoice -> ProofIrrelevance -> GuardedRelationalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.rel_choice_and_proof_irrel_imp_guarded_rel_choice".  
intros rel_choice proof_irrel.
red; intros A B P R H.
destruct (rel_choice _ _ (fun (x:sigT P) (y:B) => R (projT1 x) y)) as (R',(HR'R,H0)).
intros (x,HPx).
destruct (H x HPx) as (y,HRxy).
exists y; exact HRxy.
set (R'' := fun (x:A) (y:B) => exists H : P x, R' (existT P x H) y).
exists R''; split.
intros x y (HPx,HR'xy).
change x with (projT1 (existT P x HPx)); apply HR'R; exact HR'xy.
intros x HPx.
destruct (H0 (existT P x HPx)) as (y,(HR'xy,Huniq)).
exists y; split. exists HPx; exact HR'xy.
intros y' (H'Px,HR'xy').
apply Huniq.
rewrite proof_irrel with (a1 := HPx) (a2 := H'Px); exact HR'xy'.
Qed.

Lemma rel_choice_indep_of_general_premises_imp_guarded_rel_choice :
forall A B : Type, inhabited B -> RelationalChoice_on A B ->
IndependenceOfGeneralPremises -> GuardedRelationalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.rel_choice_indep_of_general_premises_imp_guarded_rel_choice".  
intros A B Inh AC_rel IndPrem P R H.
destruct (AC_rel (fun x y => P x -> R x y)) as (R',(HR'R,H0)).
intro x. apply IndPrem. exact Inh. intro Hx.
apply H; assumption.
exists (fun x y => P x /\ R' x y).
firstorder.
Qed.

Lemma guarded_rel_choice_imp_rel_choice :
forall A B : Type, GuardedRelationalChoice_on A B -> RelationalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.guarded_rel_choice_imp_rel_choice".  
intros A B GAC_rel R H.
destruct (GAC_rel (fun _ => True) R) as (R',(HR'R,H0)).
firstorder.
exists R'; firstorder.
Qed.

Lemma subset_types_imp_guarded_rel_choice_iff_rel_choice :
ProofIrrelevance -> (GuardedRelationalChoice <-> RelationalChoice).
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.subset_types_imp_guarded_rel_choice_iff_rel_choice".  
intuition auto using
guarded_rel_choice_imp_rel_choice,
rel_choice_and_proof_irrel_imp_guarded_rel_choice.
Qed.



Corollary guarded_iff_omniscient_rel_choice :
GuardedRelationalChoice <-> OmniscientRelationalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.guarded_iff_omniscient_rel_choice".  
split.
intros GAC_rel A B R.
apply (GAC_rel A B (fun x => exists y, R x y) R); auto.
intros OAC_rel A B P R H.
destruct (OAC_rel A B R) as (f,Hf); exists f; firstorder.
Qed.






Lemma guarded_fun_choice_imp_indep_of_general_premises :
GuardedFunctionalChoice -> IndependenceOfGeneralPremises.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.guarded_fun_choice_imp_indep_of_general_premises".  
intros GAC_fun A P Q Inh H.
destruct (GAC_fun unit A (fun _ => Q) (fun _ => P) Inh) as (f,Hf).
tauto.
exists (f tt); auto.
Qed.


Lemma guarded_fun_choice_imp_fun_choice :
GuardedFunctionalChoice -> FunctionalChoiceOnInhabitedSet.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.guarded_fun_choice_imp_fun_choice".  
intros GAC_fun A B Inh R H.
destruct (GAC_fun A B (fun _ => True) R Inh) as (f,Hf).
firstorder.
exists f; auto.
Qed.

Lemma fun_choice_and_indep_general_prem_imp_guarded_fun_choice :
FunctionalChoiceOnInhabitedSet -> IndependenceOfGeneralPremises
-> GuardedFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_choice_and_indep_general_prem_imp_guarded_fun_choice".  
intros AC_fun IndPrem A B P R Inh H.
apply (AC_fun A B Inh (fun x y => P x -> R x y)).
intro x; apply IndPrem; eauto.
Qed.

Corollary fun_choice_and_indep_general_prem_iff_guarded_fun_choice :
FunctionalChoiceOnInhabitedSet /\ IndependenceOfGeneralPremises
<-> GuardedFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_choice_and_indep_general_prem_iff_guarded_fun_choice".  
intuition auto using
guarded_fun_choice_imp_indep_of_general_premises,
guarded_fun_choice_imp_fun_choice,
fun_choice_and_indep_general_prem_imp_guarded_fun_choice.
Qed.





Lemma omniscient_fun_choice_imp_small_drinker :
OmniscientFunctionalChoice -> SmallDrinker'sParadox.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.omniscient_fun_choice_imp_small_drinker".  
intros OAC_fun A P Inh.
destruct (OAC_fun unit A (fun _ => P)) as (f,Hf).
auto.
exists (f tt); firstorder.
Qed.

Lemma omniscient_fun_choice_imp_fun_choice :
OmniscientFunctionalChoice -> FunctionalChoiceOnInhabitedSet.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.omniscient_fun_choice_imp_fun_choice".  
intros OAC_fun A B Inh R H.
destruct (OAC_fun A B R Inh) as (f,Hf).
exists f; firstorder.
Qed.

Lemma fun_choice_and_small_drinker_imp_omniscient_fun_choice :
FunctionalChoiceOnInhabitedSet -> SmallDrinker'sParadox
-> OmniscientFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_choice_and_small_drinker_imp_omniscient_fun_choice".  
intros AC_fun Drinker A B R Inh.
destruct (AC_fun A B Inh (fun x y => (exists y, R x y) -> R x y)) as (f,Hf).
intro x; apply (Drinker B (R x) Inh).
exists f; assumption.
Qed.

Corollary fun_choice_and_small_drinker_iff_omniscient_fun_choice :
FunctionalChoiceOnInhabitedSet /\ SmallDrinker'sParadox
<-> OmniscientFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_choice_and_small_drinker_iff_omniscient_fun_choice".  
intuition auto using
omniscient_fun_choice_imp_small_drinker,
omniscient_fun_choice_imp_fun_choice,
fun_choice_and_small_drinker_imp_omniscient_fun_choice.
Qed.





Theorem guarded_iff_omniscient_fun_choice :
GuardedFunctionalChoice <-> OmniscientFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.guarded_iff_omniscient_fun_choice".  
split.
intros GAC_fun A B R Inh.
apply (GAC_fun A B (fun x => exists y, R x y) R); auto.
intros OAC_fun A B P R Inh H.
destruct (OAC_fun A B R Inh) as (f,Hf).
exists f; firstorder.
Qed.






Lemma iota_imp_constructive_definite_description :
IotaStatement -> ConstructiveDefiniteDescription.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.iota_imp_constructive_definite_description".  
intros D_iota A P H.
destruct D_iota with (P:=P) as (x,H1).
destruct H; red in H; auto.
exists x; apply H1; assumption.
Qed.



Lemma epsilon_imp_constructive_indefinite_description:
EpsilonStatement -> ConstructiveIndefiniteDescription.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.epsilon_imp_constructive_indefinite_description".  
intros D_epsilon A P H.
destruct D_epsilon with (P:=P) as (x,H1).
destruct H; auto.
exists x; apply H1; assumption.
Qed.

Lemma constructive_indefinite_description_and_small_drinker_imp_epsilon :
SmallDrinker'sParadox -> ConstructiveIndefiniteDescription ->
EpsilonStatement.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.constructive_indefinite_description_and_small_drinker_imp_epsilon".  
intros Drinkers D_epsilon A P Inh;
apply D_epsilon; apply Drinkers; assumption.
Qed.

Lemma epsilon_imp_small_drinker :
EpsilonStatement -> SmallDrinker'sParadox.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.epsilon_imp_small_drinker".  
intros D_epsilon A P Inh; edestruct D_epsilon; eauto.
Qed.

Theorem constructive_indefinite_description_and_small_drinker_iff_epsilon :
(SmallDrinker'sParadox * ConstructiveIndefiniteDescription ->
EpsilonStatement) *
(EpsilonStatement ->
SmallDrinker'sParadox * ConstructiveIndefiniteDescription).
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.constructive_indefinite_description_and_small_drinker_iff_epsilon".  
intuition auto using
epsilon_imp_constructive_indefinite_description,
constructive_indefinite_description_and_small_drinker_imp_epsilon,
epsilon_imp_small_drinker.
Qed.






Require Import Wf_nat.
Require Import Decidable.

Lemma classical_denumerable_description_imp_fun_choice :
forall A:Type,
FunctionalRelReification_on A nat ->
forall R:A->nat->Prop,
(forall x y, decidable (R x y)) -> FunctionalChoice_on_rel R.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.classical_denumerable_description_imp_fun_choice".  
intros A Descr.
red; intros R Rdec H.
set (R':= fun x y => R x y /\ forall y', R x y' -> y <= y').
destruct (Descr R') as (f,Hf).
intro x.
apply (dec_inh_nat_subset_has_unique_least_element (R x)).
apply Rdec.
apply (H x).
exists f.
intros x.
destruct (Hf x) as (Hfx,_).
assumption.
Qed.








Theorem dep_non_dep_functional_choice :
DependentFunctionalChoice -> FunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.dep_non_dep_functional_choice".  
intros AC_depfun A B R H.
destruct (AC_depfun A (fun _ => B) R H) as (f,Hf).
exists f; trivial.
Qed.



Scheme and_indd := Induction for and Sort Prop.
Scheme eq_indd := Induction for eq Sort Prop.

Definition proj1_inf (A B:Prop) (p : A/\B) :=
let (a,b) := p in a.

Theorem non_dep_dep_functional_choice :
FunctionalChoice -> DependentFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.non_dep_dep_functional_choice".  
intros AC_fun A B R H.
pose (B' := { x:A & B x }).
pose (R' := fun (x:A) (y:B') => projT1 y = x /\ R (projT1 y) (projT2 y)).
destruct (AC_fun A B' R') as (f,Hf).
intros x. destruct (H x) as (y,Hy).
exists (existT (fun x => B x) x y). split; trivial.
exists (fun x => eq_rect _ _ (projT2 (f x)) _ (proj1_inf (Hf x))).
intro x; destruct (Hf x) as (Heq,HR) using and_indd.
destruct (f x); simpl in *.
destruct Heq using eq_indd; trivial.
Qed.



Theorem functional_choice_to_inhabited_forall_commute :
FunctionalChoice -> InhabitedForallCommute.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.functional_choice_to_inhabited_forall_commute".  
intros choose0 A B Hinhab.
pose proof (non_dep_dep_functional_choice choose0) as choose;clear choose0.
assert (Hexists : forall x, exists _ : B x, True).
{ intros x;apply inhabited_sig_to_exists.
refine (inhabited_covariant _ (Hinhab x)).
intros y;exists y;exact I. }
apply choose in Hexists.
destruct Hexists as [f _].
exact (inhabits f).
Qed.

Theorem inhabited_forall_commute_to_functional_choice :
InhabitedForallCommute -> FunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.inhabited_forall_commute_to_functional_choice".  
intros choose A B R Hexists.
assert (Hinhab : forall x, inhabited {y : B | R x y}).
{ intros x;apply exists_to_inhabited_sig;trivial. }
apply choose in Hinhab. destruct Hinhab as [f].
exists (fun x => proj1_sig (f x)).
exact (fun x => proj2_sig (f x)).
Qed.





Theorem dep_non_dep_functional_rel_reification :
DependentFunctionalRelReification -> FunctionalRelReification.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.dep_non_dep_functional_rel_reification".  
intros DepFunReify A B R H.
destruct (DepFunReify A (fun _ => B) R H) as (f,Hf).
exists f; trivial.
Qed.



Theorem non_dep_dep_functional_rel_reification :
FunctionalRelReification -> DependentFunctionalRelReification.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.non_dep_dep_functional_rel_reification".  
intros AC_fun A B R H.
pose (B' := { x:A & B x }).
pose (R' := fun (x:A) (y:B') => projT1 y = x /\ R (projT1 y) (projT2 y)).
destruct (AC_fun A B' R') as (f,Hf).
intros x. destruct (H x) as (y,(Hy,Huni)).
exists (existT (fun x => B x) x y). repeat split; trivial.
intros (x',y') (Heqx',Hy').
simpl in *.
destruct Heqx'.
rewrite (Huni y'); trivial.
exists (fun x => eq_rect _ _ (projT2 (f x)) _ (proj1_inf (Hf x))).
intro x; destruct (Hf x) as (Heq,HR) using and_indd.
destruct (f x); simpl in *.
destruct Heq using eq_indd; trivial.
Qed.

Corollary dep_iff_non_dep_functional_rel_reification :
FunctionalRelReification <-> DependentFunctionalRelReification.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.dep_iff_non_dep_functional_rel_reification".  
intuition auto using
non_dep_dep_functional_rel_reification,
dep_non_dep_functional_rel_reification.
Qed.






Lemma relative_non_contradiction_of_indefinite_descr :
forall C:Prop, (ConstructiveIndefiniteDescription -> C)
-> (FunctionalChoice -> C).
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.relative_non_contradiction_of_indefinite_descr".  
intros C H AC_fun.
assert (AC_depfun := non_dep_dep_functional_choice AC_fun).
pose (A0 := { A:Type & { P:A->Prop & exists x, P x }}).
pose (B0 := fun x:A0 => projT1 x).
pose (R0 := fun x:A0 => fun y:B0 x => projT1 (projT2 x) y).
pose (H0 := fun x:A0 => projT2 (projT2 x)).
destruct (AC_depfun A0 B0 R0 H0) as (f, Hf).
apply H.
intros A P H'.
exists (f (existT _ A (existT _ P H'))).
pose (Hf' := Hf (existT _ A (existT _ P H'))).
assumption.
Qed.

Lemma constructive_indefinite_descr_fun_choice :
ConstructiveIndefiniteDescription -> FunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.constructive_indefinite_descr_fun_choice".  
intros IndefDescr A B R H.
exists (fun x => proj1_sig (IndefDescr B (R x) (H x))).
intro x.
apply (proj2_sig (IndefDescr B (R x) (H x))).
Qed.



Lemma relative_non_contradiction_of_definite_descr :
forall C:Prop, (ConstructiveDefiniteDescription -> C)
-> (FunctionalRelReification -> C).
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.relative_non_contradiction_of_definite_descr".  
intros C H FunReify.
assert (DepFunReify := non_dep_dep_functional_rel_reification FunReify).
pose (A0 := { A:Type & { P:A->Prop & exists! x, P x }}).
pose (B0 := fun x:A0 => projT1 x).
pose (R0 := fun x:A0 => fun y:B0 x => projT1 (projT2 x) y).
pose (H0 := fun x:A0 => projT2 (projT2 x)).
destruct (DepFunReify A0 B0 R0 H0) as (f, Hf).
apply H.
intros A P H'.
exists (f (existT _ A (existT _ P H'))).
pose (Hf' := Hf (existT _ A (existT _ P H'))).
assumption.
Qed.

Lemma constructive_definite_descr_fun_reification :
ConstructiveDefiniteDescription -> FunctionalRelReification.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.constructive_definite_descr_fun_reification".  
intros DefDescr A B R H.
exists (fun x => proj1_sig (DefDescr B (R x) (H x))).
intro x.
apply (proj2_sig (DefDescr B (R x) (H x))).
Qed.










Require Import Setoid.

Theorem constructive_definite_descr_excluded_middle :
(forall A : Type, ConstructiveDefiniteDescription_on A) ->
(forall P:Prop, P \/ ~ P) -> (forall P:Prop, {P} + {~ P}).
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.constructive_definite_descr_excluded_middle".  
intros Descr EM P.
pose (select := fun b:bool => if b then P else ~P).
assert { b:bool | select b } as ([|],HP).
red in Descr.
apply Descr.
rewrite <- unique_existence; split.
destruct (EM P).
exists true; trivial.
exists false; trivial.
intros [|] [|] H1 H2; simpl in *; reflexivity || contradiction.
left; trivial.
right; trivial.
Qed.

Corollary fun_reification_descr_computational_excluded_middle_in_prop_context :
FunctionalRelReification ->
(forall P:Prop, P \/ ~ P) ->
forall C:Prop, ((forall P:Prop, {P} + {~ P}) -> C) -> C.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_reification_descr_computational_excluded_middle_in_prop_context".  
intros FunReify EM C H. intuition auto using
constructive_definite_descr_excluded_middle,
(relative_non_contradiction_of_definite_descr (C:=C)).
Qed.





Require Import Arith.

Theorem functional_choice_imp_functional_dependent_choice :
FunctionalChoice -> FunctionalDependentChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.functional_choice_imp_functional_dependent_choice".  
intros FunChoice A R HRfun x0.
apply FunChoice in HRfun as (g,Rg).
set (f:=fix f n := match n with 0 => x0 | S n' => g (f n') end).
exists f; firstorder.
Qed.

Theorem functional_dependent_choice_imp_functional_countable_choice :
FunctionalDependentChoice -> FunctionalCountableChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.functional_dependent_choice_imp_functional_countable_choice".  
intros H A R H0.
set (R' (p q:nat*A) := fst q = S (fst p) /\ R (fst p) (snd q)).
destruct (H0 0) as (y0,Hy0).
destruct H with (R:=R') (x0:=(0,y0)) as (f,(Hf0,HfS)).
intro x; destruct (H0 (fst x)) as (y,Hy).
exists (S (fst x),y).
red. auto.
assert (Heq:forall n, fst (f n) = n).
induction n.
rewrite Hf0; reflexivity.
specialize HfS with n; destruct HfS as (->,_); congruence.
exists (fun n => snd (f (S n))).
intro n'. specialize HfS with n'.
destruct HfS as (_,HR).
rewrite Heq in HR.
assumption.
Qed.




Require Import ClassicalFacts PropExtensionalityFacts.




Theorem repr_fun_choice_imp_ext_prop_repr :
RepresentativeFunctionalChoice -> ExtensionalPropositionRepresentative.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.repr_fun_choice_imp_ext_prop_repr".  
intros ReprFunChoice A.
pose (R P Q := P <-> Q).
assert (Hequiv:Equivalence R) by (split; firstorder).
apply (ReprFunChoice _ R Hequiv).
Qed.

Theorem repr_fun_choice_imp_ext_pred_repr :
RepresentativeFunctionalChoice -> ExtensionalPredicateRepresentative.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.repr_fun_choice_imp_ext_pred_repr".  
intros ReprFunChoice A.
pose (R P Q := forall x : A, P x <-> Q x).
assert (Hequiv:Equivalence R) by (split; firstorder).
apply (ReprFunChoice _ R Hequiv).
Qed.

Theorem repr_fun_choice_imp_ext_function_repr :
RepresentativeFunctionalChoice -> ExtensionalFunctionRepresentative.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.repr_fun_choice_imp_ext_function_repr".  
intros ReprFunChoice A B.
pose (R (f g : A -> B) := forall x : A, f x = g x).
assert (Hequiv:Equivalence R).
{ split; try easy. firstorder using eq_trans. }
apply (ReprFunChoice _ R Hequiv).
Qed.



Theorem repr_fun_choice_imp_excluded_middle :
RepresentativeFunctionalChoice -> ExcludedMiddle.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.repr_fun_choice_imp_excluded_middle".  
intros ReprFunChoice.
apply representative_boolean_partition_imp_excluded_middle, ReprFunChoice.
Qed.

Theorem repr_fun_choice_imp_relational_choice :
RepresentativeFunctionalChoice -> RelationalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.repr_fun_choice_imp_relational_choice".  
intros ReprFunChoice A B T Hexists.
pose (D := (A*B)%type).
pose (R (z z':D) :=
let x := fst z in
let x' := fst z' in
let y := snd z in
let y' := snd z' in
x = x' /\ (T x y -> y = y' \/ T x y') /\ (T x y' -> y = y' \/ T x y)).
assert (Hequiv : Equivalence R).
{ split.
- split. easy. firstorder.
- intros (x,y) (x',y') (H1,(H2,H2')). split. easy. simpl fst in *. simpl snd in *.
subst x'. split; intro H.
+ destruct (H2' H); firstorder.
+ destruct (H2 H); firstorder.
- intros (x,y) (x',y') (x'',y'') (H1,(H2,H2')) (H3,(H4,H4')).
simpl fst in *. simpl snd in *. subst x'' x'. split. easy. split; intro H.
+ simpl fst in *. simpl snd in *. destruct (H2 H) as [<-|H0].
* destruct (H4 H); firstorder.
* destruct (H2' H0), (H4 H0); try subst y'; try subst y''; try firstorder.
+ simpl fst in *. simpl snd in *. destruct (H4' H) as [<-|H0].
* destruct (H2' H); firstorder.
* destruct (H2' H0), (H4 H0); try subst y'; try subst y''; try firstorder. }
destruct (ReprFunChoice D R Hequiv) as (g,Hg).
set (T' x y := T x y /\ exists y', T x y' /\ g (x,y') = (x,y)).
exists T'. split.
- intros x y (H,_); easy.
- intro x. destruct (Hexists x) as (y,Hy).
exists (snd (g (x,y))).
destruct (Hg (x,y)) as ((Heq1,(H',H'')),Hgxyuniq); clear Hg.
destruct (H' Hy) as [Heq2|Hgy]; clear H'.
+ split. split.
* rewrite <- Heq2. assumption.
* exists y. destruct (g (x,y)) as (x',y'). simpl in Heq1, Heq2. subst; easy.
* intros y' (Hy',(y'',(Hy'',Heq))).
rewrite (Hgxyuniq (x,y'')), Heq. easy. split. easy.
split; right; easy.
+ split. split.
* assumption.
* exists y. destruct (g (x,y)) as (x',y'). simpl in Heq1. subst x'; easy.
* intros y' (Hy',(y'',(Hy'',Heq))).
rewrite (Hgxyuniq (x,y'')), Heq. easy. split. easy.
split; right; easy.
Qed.




Theorem gen_setoid_fun_choice_imp_setoid_fun_choice  :
forall A B, GeneralizedSetoidFunctionalChoice_on A B -> SetoidFunctionalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.gen_setoid_fun_choice_imp_setoid_fun_choice".  
intros A B GenSetoidFunChoice R T Hequiv Hcompat Hex.
apply GenSetoidFunChoice; try easy.
apply eq_equivalence.
intros * H <-. firstorder.
Qed.

Theorem setoid_fun_choice_imp_gen_setoid_fun_choice :
forall A B, SetoidFunctionalChoice_on A B -> GeneralizedSetoidFunctionalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.setoid_fun_choice_imp_gen_setoid_fun_choice".  
intros A B SetoidFunChoice R S T HequivR HequivS Hcompat Hex.
destruct SetoidFunChoice with (R:=R) (T:=T) as (f,Hf); try easy.
{ intros; apply (Hcompat x x' y y); try easy. }
exists f. intros x; specialize Hf with x as (Hf,Huniq). intuition. now erewrite Huniq.
Qed.

Corollary setoid_fun_choice_iff_gen_setoid_fun_choice :
forall A B, SetoidFunctionalChoice_on A B <-> GeneralizedSetoidFunctionalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.setoid_fun_choice_iff_gen_setoid_fun_choice".  
split; auto using gen_setoid_fun_choice_imp_setoid_fun_choice, setoid_fun_choice_imp_gen_setoid_fun_choice.
Qed.

Theorem setoid_fun_choice_imp_simple_setoid_fun_choice  :
forall A B, SetoidFunctionalChoice_on A B -> SimpleSetoidFunctionalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.setoid_fun_choice_imp_simple_setoid_fun_choice".  
intros A B SetoidFunChoice R T Hequiv Hexists.
pose (T' x y := forall x', R x x' -> T x' y).
assert (Hcompat : forall (x x' : A) (y : B), R x x' -> T' x y -> T' x' y) by firstorder.
destruct (SetoidFunChoice R T' Hequiv Hcompat Hexists) as (f,Hf).
exists f. firstorder.
Qed.

Theorem simple_setoid_fun_choice_imp_setoid_fun_choice :
forall A B, SimpleSetoidFunctionalChoice_on A B -> SetoidFunctionalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.simple_setoid_fun_choice_imp_setoid_fun_choice".  
intros A B SimpleSetoidFunChoice R T Hequiv Hcompat Hexists.
destruct (SimpleSetoidFunChoice R T Hequiv) as (f,Hf); firstorder.
Qed.

Corollary setoid_fun_choice_iff_simple_setoid_fun_choice :
forall A B, SetoidFunctionalChoice_on A B <-> SimpleSetoidFunctionalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.setoid_fun_choice_iff_simple_setoid_fun_choice".  
split; auto using simple_setoid_fun_choice_imp_setoid_fun_choice, setoid_fun_choice_imp_simple_setoid_fun_choice.
Qed.




Theorem setoid_fun_choice_imp_fun_choice :
forall A B, SetoidFunctionalChoice_on A B -> FunctionalChoice_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.setoid_fun_choice_imp_fun_choice".  
intros A B SetoidFunChoice T Hexists.
destruct SetoidFunChoice with (R:=@eq A) (T:=T) as (f,Hf).
- apply eq_equivalence.
- now intros * ->.
- assumption.
- exists f. firstorder.
Qed.

Corollary setoid_fun_choice_imp_functional_rel_reification :
forall A B, SetoidFunctionalChoice_on A B -> FunctionalRelReification_on A B.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.setoid_fun_choice_imp_functional_rel_reification".  
intros A B SetoidFunChoice.
apply fun_choice_imp_functional_rel_reification.
now apply setoid_fun_choice_imp_fun_choice.
Qed.

Theorem setoid_fun_choice_imp_repr_fun_choice :
SetoidFunctionalChoice -> RepresentativeFunctionalChoice .
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.setoid_fun_choice_imp_repr_fun_choice".  
intros SetoidFunChoice A R Hequiv.
apply SetoidFunChoice; firstorder.
Qed.

Theorem functional_rel_reification_and_repr_fun_choice_imp_setoid_fun_choice :
FunctionalRelReification -> RepresentativeFunctionalChoice -> SetoidFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.functional_rel_reification_and_repr_fun_choice_imp_setoid_fun_choice".  
intros FunRelReify ReprFunChoice A B R T Hequiv Hcompat Hexists.
assert (FunChoice : FunctionalChoice).
{ intros A' B'. apply functional_rel_reification_and_rel_choice_imp_fun_choice.
- apply FunRelReify.
- now apply repr_fun_choice_imp_relational_choice. }
destruct (FunChoice _ _ T Hexists) as (f,Hf).
destruct (ReprFunChoice A R Hequiv) as (g,Hg).
exists (fun a => f (g a)).
intro x. destruct (Hg x) as (Hgx,HRuniq).
split.
- eapply Hcompat. symmetry. apply Hgx. apply Hf.
- intros y Hxy. f_equal. auto.
Qed.

Theorem functional_rel_reification_and_repr_fun_choice_iff_setoid_fun_choice :
FunctionalRelReification /\ RepresentativeFunctionalChoice <-> SetoidFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.functional_rel_reification_and_repr_fun_choice_iff_setoid_fun_choice".  
split; intros.
- now apply functional_rel_reification_and_repr_fun_choice_imp_setoid_fun_choice.
- split.
+ now intros A B; apply setoid_fun_choice_imp_functional_rel_reification.
+ now apply setoid_fun_choice_imp_repr_fun_choice.
Qed.






Import EqNotations.





Theorem fun_choice_and_ext_functions_repr_and_excluded_middle_imp_setoid_fun_choice :
FunctionalChoice -> ExtensionalFunctionRepresentative -> ExcludedMiddle -> RepresentativeFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_choice_and_ext_functions_repr_and_excluded_middle_imp_setoid_fun_choice".  
intros FunChoice SetoidFunRepr EM A R (Hrefl,Hsym,Htrans).
assert (H:forall P:Prop, exists b, b = true <-> P).
{ intros P. destruct (EM P).
- exists true; firstorder.
- exists false; easy. }
destruct (FunChoice _ _ _ H) as (c,Hc).
pose (class_of a y := c (R a y)).
pose (isclass f := exists x:A, f x = true).
pose (class := {f:A -> bool | isclass f}).
pose (contains (c:class) (a:A) := proj1_sig c a = true).
destruct (FunChoice class A contains) as (f,Hf).
- intros f. destruct (proj2_sig f) as (x,Hx).
exists x. easy.
- destruct (SetoidFunRepr A bool) as (h,Hh).
assert (Hisclass:forall a, isclass (h (class_of a))).
{ intro a. exists a. destruct (Hh (class_of a)) as (Ha,Huniqa).
rewrite <- Ha. apply Hc. apply Hrefl. }
pose (f':= fun a => exist _ (h (class_of a)) (Hisclass a) : class).
exists (fun a => f (f' a)).
intros x. destruct (Hh (class_of x)) as (Hx,Huniqx). split.
+ specialize Hf with (f' x). unfold contains in Hf. simpl in Hf. rewrite <- Hx in Hf. apply Hc. assumption.
+ intros y Hxy.
f_equal.
assert (Heq1: h (class_of x) = h (class_of y)).
{ apply Huniqx. intro z. unfold class_of.
destruct (c (R x z)) eqn:Hxz.
- symmetry. apply Hc. apply -> Hc in Hxz. firstorder.
- destruct (c (R y z)) eqn:Hyz.
+ apply -> Hc in Hyz. rewrite <- Hxz. apply Hc. firstorder.
+ easy. }
assert (Heq2:rew Heq1 in Hisclass x = Hisclass y).
{ apply proof_irrelevance_cci, EM. }
unfold f'.
rewrite <- Heq2.
rewrite <- Heq1.
reflexivity.
Qed.

Theorem setoid_functional_choice_first_characterization :
FunctionalChoice /\ ExtensionalFunctionRepresentative /\ ExcludedMiddle <-> SetoidFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.setoid_functional_choice_first_characterization".  
split.
- intros (FunChoice & SetoidFunRepr & EM).
apply functional_rel_reification_and_repr_fun_choice_imp_setoid_fun_choice.
+ intros A B. apply fun_choice_imp_functional_rel_reification, FunChoice.
+ now apply fun_choice_and_ext_functions_repr_and_excluded_middle_imp_setoid_fun_choice.
- intro SetoidFunChoice. repeat split.
+ now intros A B; apply setoid_fun_choice_imp_fun_choice.
+ apply repr_fun_choice_imp_ext_function_repr.
now apply setoid_fun_choice_imp_repr_fun_choice.
+ apply repr_fun_choice_imp_excluded_middle.
now apply setoid_fun_choice_imp_repr_fun_choice.
Qed.






Theorem fun_choice_and_ext_pred_ext_and_proof_irrel_imp_setoid_fun_choice :
FunctionalChoice -> ExtensionalPredicateRepresentative -> ProofIrrelevance -> RepresentativeFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.fun_choice_and_ext_pred_ext_and_proof_irrel_imp_setoid_fun_choice".  
intros FunChoice PredExtRepr PI A R (Hrefl,Hsym,Htrans).
pose (isclass P := exists x:A, P x).
pose (class := {P:A -> Prop | isclass P}).
pose (contains (c:class) (a:A) := proj1_sig c a).
pose (class_of a := R a).
destruct (FunChoice class A contains) as (f,Hf).
- intros c. apply proj2_sig.
- destruct (PredExtRepr A) as (h,Hh).
assert (Hisclass:forall a, isclass (h (class_of a))).
{ intro a. exists a. destruct (Hh (class_of a)) as (Ha,Huniqa).
rewrite <- Ha; apply Hrefl. }
pose (f':= fun a => exist _ (h (class_of a)) (Hisclass a) : class).
exists (fun a => f (f' a)).
intros x. destruct (Hh (class_of x)) as (Hx,Huniqx). split.
+ specialize Hf with (f' x). simpl in Hf. rewrite <- Hx in Hf. assumption.
+ intros y Hxy.
f_equal.
assert (Heq1: h (class_of x) = h (class_of y)).
{ apply Huniqx. intro z. unfold class_of. firstorder. }
assert (Heq2:rew Heq1 in Hisclass x = Hisclass y).
{ apply PI. }
unfold f'.
rewrite <- Heq2.
rewrite <- Heq1.
reflexivity.
Qed.

Theorem setoid_functional_choice_second_characterization :
FunctionalChoice /\ ExtensionalPredicateRepresentative /\ ProofIrrelevance <-> SetoidFunctionalChoice.
Proof. try hammer_hook "ChoiceFacts" "ChoiceFacts.setoid_functional_choice_second_characterization".  
split.
- intros (FunChoice & ExtPredRepr & PI).
apply functional_rel_reification_and_repr_fun_choice_imp_setoid_fun_choice.
+ intros A B. now apply fun_choice_imp_functional_rel_reification.
+ now apply fun_choice_and_ext_pred_ext_and_proof_irrel_imp_setoid_fun_choice.
- intro SetoidFunChoice. repeat split.
+ now intros A B; apply setoid_fun_choice_imp_fun_choice.
+ apply repr_fun_choice_imp_ext_pred_repr.
now apply setoid_fun_choice_imp_repr_fun_choice.
+ red. apply proof_irrelevance_cci.
apply repr_fun_choice_imp_excluded_middle.
now apply setoid_fun_choice_imp_repr_fun_choice.
Qed.



Notation description_rel_choice_imp_funct_choice :=
functional_rel_reification_and_rel_choice_imp_fun_choice (compat "8.6").

Notation funct_choice_imp_rel_choice := fun_choice_imp_rel_choice (compat "8.6").

Notation FunChoice_Equiv_RelChoice_and_ParamDefinDescr :=
fun_choice_iff_rel_choice_and_functional_rel_reification (compat "8.6").

Notation funct_choice_imp_description := fun_choice_imp_functional_rel_reification (compat "8.6").
