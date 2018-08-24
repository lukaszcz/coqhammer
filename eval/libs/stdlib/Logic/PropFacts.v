From Hammer Require Import Hammer.













Theorem injection_is_involution_in_Prop
(f : Prop -> Prop)
(inj : forall A B, (f A <-> f B) -> (A <-> B))
(ext : forall A B, A <-> B -> f A <-> f B)
: forall A, f (f A) <-> A.
Proof. try hammer_hook "PropFacts" "PropFacts.injection_is_involution_in_Prop". Undo.  
intros.
enough (f (f (f A)) <-> f A) by (apply inj; assumption).
split; intro H.
- now_show (f A).
enough (f A <-> True) by firstorder.
enough (f (f A) <-> f True) by (apply inj; assumption).
split; intro H'.
+ now_show (f True).
enough (f (f (f A)) <-> f True) by firstorder.
apply ext; firstorder.
+ now_show (f (f A)).
enough (f (f A) <-> True) by firstorder.
apply inj; firstorder.
- now_show (f (f (f A))).
enough (f A <-> f (f (f A))) by firstorder.
apply ext.
split; intro H'.
+ now_show (f (f A)).
enough (f A <-> f (f A)) by firstorder.
apply ext; firstorder.
+ now_show A.
enough (f A <-> A) by firstorder.
apply inj; firstorder.
Defined.
