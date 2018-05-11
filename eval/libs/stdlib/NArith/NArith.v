From Hammer Require Import Hammer.











Require Export BinNums.
Require Export BinPos.
Require Export BinNat.
Require Export Nnat.
Require Export Ndiv_def.
Require Export Nsqrt_def.
Require Export Ngcd_def.
Require Export Ndigits.
Require Export NArithRing.





Local Open Scope N_scope.

Section TestOrder.
Let test : forall x y, x<=y -> y<=x -> x=y.
Proof. try hammer_hook "NArith" "NArith.TestOrder.test".  
N.order.
Qed.
End TestOrder.
