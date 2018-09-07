From Hammer Require Import Hammer.











Require Import NAxioms NSub NPow NParity NZLog.

Module Type NLog2Prop
(A : NAxiomsSig)
(B : NSubProp A)
(C : NParityProp A B)
(D : NPowProp A B C).



Include NZLog2Prop A A A B D.Private_NZPow.
Include NZLog2UpProp A A A B D.Private_NZPow.
End NLog2Prop.
