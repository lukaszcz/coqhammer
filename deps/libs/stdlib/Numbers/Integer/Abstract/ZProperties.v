From Hammer Require Import Hammer.









Require Export ZAxioms ZMaxMin ZSgnAbs ZParity ZPow ZDivTrunc ZDivFloor
ZGcd ZLcm NZLog NZSqrt ZBits.



Module Type ZBasicProp (Z:ZAxiomsMiniSig) := ZMaxMinProp Z.

Module Type ZExtraProp (Z:ZAxiomsSig)(P:ZBasicProp Z) :=
ZSgnAbsProp Z P <+ ZParityProp Z P <+ ZPowProp Z P
<+ NZSqrtProp Z Z P <+ NZSqrtUpProp Z Z P
<+ NZLog2Prop Z Z Z P <+ NZLog2UpProp Z Z Z P
<+ ZDivProp Z P <+ ZQuotProp Z P <+ ZGcdProp Z P <+ ZLcmProp Z P
<+ ZBitsProp Z P.
