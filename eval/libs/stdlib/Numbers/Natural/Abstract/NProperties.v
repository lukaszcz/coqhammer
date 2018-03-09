From Hammer Require Import Hammer.









Require Export NAxioms.
Require Import NMaxMin NParity NPow NSqrt NLog NDiv NGcd NLcm NBits.



Module Type NBasicProp (N:NAxiomsMiniSig) := NMaxMinProp N.

Module Type NExtraProp (N:NAxiomsSig)(P:NBasicProp N) :=
NParityProp N P <+ NPowProp N P <+ NSqrtProp N P
<+ NLog2Prop N P <+ NDivProp N P <+ NGcdProp N P <+ NLcmProp N P
<+ NBitsProp N P.
