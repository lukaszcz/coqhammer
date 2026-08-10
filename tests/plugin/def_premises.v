From Hammer Require Import Hammer.

(* The first pair checks declaration-time defaults.  The Makefile also checks
   the pair after Unset below, so changes to either reset value are caught. *)
Test Hammer DefinitionPremises.
Test Hammer DefinitionFeatures.

(* Force every proof through premise selection and an external prover.  A
   single predictor/prover configuration makes the negative controls below
   deterministic and keeps their premise budget small. *)
Set Hammer SAutoLimit 0.
Set Hammer ATPLimit 5.
Set Hammer GSMode 0.
Set Hammer Predictions 16.
Set Hammer PredictMethod "nbayes".
Unset Hammer CVC4.
Unset Hammer Eprover.
Unset Hammer Z3.
Set Hammer Vampire.
Set Hammer DefinitionFeatures 0.

(* The goal mentions the inductive but not its nullary constructor.  With one
   reserved slot the constructor's typing axiom is found only through the
   inductive-to-constructor group. *)
Inductive premise_token : Prop := premise_token_intro.

Lemma premise_token_provable : premise_token.
Proof.
  Set Hammer DefinitionPremises 0.
  Fail hammer.
  Set Hammer DefinitionPremises 1.
  hammer.
Qed.

(* A fresh definition is absent from the predictor's training history, so its
   unfolding must be reserved from the constants in the goal. *)
Definition goal_seed_dbl (n : nat) := n + n.

Lemma goal_seed_dbl_zero : goal_seed_dbl 0 = 0.
Proof.
  Set Hammer DefinitionPremises 0.
  Fail hammer.
  Set Hammer DefinitionPremises 1.
  hammer.
Qed.

(* Use a distinct fresh definition and introduce the premise explicitly.  The
   constant is then a seed only through H and is absent from the current goal. *)
Definition hypothesis_seed_dbl (n : nat) := n + n.

Lemma hypothesis_seed_dbl_use :
  forall x, hypothesis_seed_dbl x = 4 -> x + x = 4.
Proof.
  intros x H.
  Set Hammer DefinitionPremises 0.
  Fail hammer.
  Set Hammer DefinitionPremises 1.
  hammer.
Qed.

(* Restore the ordinary search configuration before exercising the option
   interface, so these coverage checks do not depend on the controls above. *)
Set Hammer ATPLimit 20.
Set Hammer GSMode 8.
Set Hammer Predictions 1024.
Set Hammer PredictMethod "knn".
Set Hammer CVC4.
Set Hammer Eprover.
Set Hammer Z3.
Set Hammer Vampire.

(* Exercise both runtime options away from their defaults.  The fresh constant
   makes the definition-feature expansion path nonempty even though this goal
   is intentionally independent of selected premises. *)
Set Hammer DefinitionPremises 0.
Set Hammer DefinitionFeatures 4.

Definition feature_marker (n : nat) := n + n.

Lemma nondefault_options : forall n, feature_marker n = feature_marker n.
Proof. hammer. Qed.

Set Hammer DefinitionPremises 32.
Set Hammer DefinitionFeatures 16.

Lemma explicitly_configured_defaults : forall P : Prop, P -> P.
Proof. hammer. Qed.

(* Unset must reset values changed in the current session, rather than merely
   leaving the most recently configured values in place. *)
Set Hammer DefinitionPremises 0.
Set Hammer DefinitionFeatures 0.
Unset Hammer DefinitionPremises.
Unset Hammer DefinitionFeatures.
Test Hammer DefinitionPremises.
Test Hammer DefinitionFeatures.

Lemma unset_options : forall P : Prop, P -> P.
Proof. hammer. Qed.

Set Hammer SAutoLimit 1.
