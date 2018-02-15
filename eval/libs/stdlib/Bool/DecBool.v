From Hammer Require Import Hammer.









Set Implicit Arguments.

Definition ifdec (A B:Prop) (C:Type) (H:{A} + {B}) (x y:C) : C :=
if H then x else y.


Theorem ifdec_left :
forall (A B:Prop) (C:Set) (H:{A} + {B}),
~ B -> forall x y:C, ifdec H x y = x.
Proof. hammer_hook "DecBool" "DecBool.ifdec_left". Restart. 
intros; case H; auto.
intro; absurd B; trivial.
Qed.

Theorem ifdec_right :
forall (A B:Prop) (C:Set) (H:{A} + {B}),
~ A -> forall x y:C, ifdec H x y = y.
Proof. hammer_hook "DecBool" "DecBool.ifdec_right". Restart. 
intros; case H; auto.
intro; absurd A; trivial.
Qed.

Unset Implicit Arguments.
