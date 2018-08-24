From Hammer Require Import Hammer.











Require Export Decidable.
Require Export ZAxioms.
Require Import NZProperties.

Module ZBaseProp (Import Z : ZAxiomsMiniSig').
Include NZProp Z.



Theorem pred_inj : forall n m, P n == P m -> n == m.
Proof. try hammer_hook "ZBase" "ZBase.ZBaseProp.pred_inj". Undo.  
intros n m H. apply succ_wd in H. now rewrite 2 succ_pred in H.
Qed.

Theorem pred_inj_wd : forall n1 n2, P n1 == P n2 <-> n1 == n2.
Proof. try hammer_hook "ZBase" "ZBase.ZBaseProp.pred_inj_wd". Undo.  
intros n1 n2; split; [apply pred_inj | intros; now f_equiv].
Qed.

Lemma succ_m1 : S (-1) == 0.
Proof. try hammer_hook "ZBase" "ZBase.ZBaseProp.succ_m1". Undo.  
now rewrite one_succ, opp_succ, opp_0, succ_pred.
Qed.

End ZBaseProp.

