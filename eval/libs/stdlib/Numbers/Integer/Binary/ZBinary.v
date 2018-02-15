From Hammer Require Import Hammer.












Require Import ZAxioms ZProperties BinInt.

Local Open Scope Z_scope.



Module Z
<: ZAxiomsSig <: UsualOrderedTypeFull <: TotalOrder
<: UsualDecidableTypeFull
:= BinInt.Z.



Ltac z_order := Z.order.



Section TestOrder.
Let test : forall x y, x<=y -> y<=x -> x=y.
Proof. hammer_hook "ZBinary" "ZBinary.TestOrder.test". Restart. 
z_order.
Qed.
End TestOrder.




