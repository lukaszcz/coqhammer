From Hammer Require Import Hammer.











Require Export Bool NZAxioms NZParity NZPow NZSqrt NZLog NZDiv NZGcd NZBits.



Module Type NAxiom (Import NZ : NZDomainSig').
Axiom pred_0 : P 0 == 0.
End NAxiom.

Module Type NAxiomsMiniSig := NZOrdAxiomsSig <+ NAxiom.
Module Type NAxiomsMiniSig' := NZOrdAxiomsSig' <+ NAxiom.





Module Type NDivSpecific (Import N : NAxiomsMiniSig')(Import DM : DivMod' N).
Axiom mod_upper_bound : forall a b, b ~= 0 -> a mod b < b.
End NDivSpecific.





Module Type NAxiomsSig := NAxiomsMiniSig <+ OrderFunctions
<+ NZParity.NZParity <+ NZPow.NZPow <+ NZSqrt.NZSqrt <+ NZLog.NZLog2
<+ NZGcd.NZGcd <+ NZDiv.NZDiv <+ NZBits.NZBits <+ NZSquare.

Module Type NAxiomsSig' := NAxiomsMiniSig' <+ OrderFunctions'
<+ NZParity.NZParity <+ NZPow.NZPow' <+ NZSqrt.NZSqrt' <+ NZLog.NZLog2
<+ NZGcd.NZGcd' <+ NZDiv.NZDiv' <+ NZBits.NZBits' <+ NZSquare.




Module Type NAxiomsRec (Import NZ : NZDomainSig').

Parameter Inline recursion : forall {A : Type}, A -> (t -> A -> A) -> t -> A.

Declare Instance recursion_wd {A : Type} (Aeq : relation A) :
Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) recursion.

Axiom recursion_0 :
forall {A} (a : A) (f : t -> A -> A), recursion a f 0 = a.

Axiom recursion_succ :
forall {A} (Aeq : relation A) (a : A) (f : t -> A -> A),
Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
forall n, Aeq (recursion a f (S n)) (f n (recursion a f n)).

End NAxiomsRec.

Module Type NAxiomsRecSig := NAxiomsMiniSig <+ NAxiomsRec.
Module Type NAxiomsRecSig' := NAxiomsMiniSig' <+ NAxiomsRec.

Module Type NAxiomsFullSig := NAxiomsSig <+ NAxiomsRec.
Module Type NAxiomsFullSig' := NAxiomsSig' <+ NAxiomsRec.
