From Hammer Require Import Hammer.













Require Import Classical_Prop.

Section Generic.
Variable U : Type.



Lemma not_all_not_ex :
forall P:U -> Prop, ~ (forall n:U, ~ P n) ->  exists n : U, P n.
Proof. try hammer_hook "Classical_Pred_Type" "Classical_Pred_Type.not_all_not_ex".  
intros P notall.
apply NNPP.
intro abs.
apply notall.
intros n H.
apply abs; exists n; exact H.
Qed.

Lemma not_all_ex_not :
forall P:U -> Prop, ~ (forall n:U, P n) ->  exists n : U, ~ P n.
Proof. try hammer_hook "Classical_Pred_Type" "Classical_Pred_Type.not_all_ex_not".  
intros P notall.
apply not_all_not_ex with (P:=fun x => ~ P x).
intro all; apply notall.
intro n; apply NNPP.
apply all.
Qed.

Lemma not_ex_all_not :
forall P:U -> Prop, ~ (exists n : U, P n) -> forall n:U, ~ P n.
Proof. try hammer_hook "Classical_Pred_Type" "Classical_Pred_Type.not_ex_all_not".  
unfold not; intros P notex n abs.
apply notex.
exists n; trivial.
Qed.

Lemma not_ex_not_all :
forall P:U -> Prop, ~ (exists n : U, ~ P n) -> forall n:U, P n.
Proof. try hammer_hook "Classical_Pred_Type" "Classical_Pred_Type.not_ex_not_all".  
intros P H n.
apply NNPP.
red; intro K; apply H; exists n; trivial.
Qed.

Lemma ex_not_not_all :
forall P:U -> Prop, (exists n : U, ~ P n) -> ~ (forall n:U, P n).
Proof. try hammer_hook "Classical_Pred_Type" "Classical_Pred_Type.ex_not_not_all".  
unfold not; intros P exnot allP.
elim exnot; auto.
Qed.

Lemma all_not_not_ex :
forall P:U -> Prop, (forall n:U, ~ P n) -> ~ (exists n : U, P n).
Proof. try hammer_hook "Classical_Pred_Type" "Classical_Pred_Type.all_not_not_ex".  
unfold not; intros P allnot exP; elim exP; intros n p.
apply allnot with n; auto.
Qed.

End Generic.
