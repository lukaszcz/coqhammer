From Hammer Require Import Hammer.









Require Import Bool NZAxioms NZMulOrder NZParity NZPow NZDiv NZLog.



Module Type Bits (Import A : Typ).
Parameter Inline testbit : t -> t -> bool.
Parameters Inline shiftl shiftr land lor ldiff lxor : t -> t -> t.
Parameter Inline div2 : t -> t.
End Bits.

Module Type BitsNotation (Import A : Typ)(Import B : Bits A).
Notation "a .[ n ]" := (testbit a n) (at level 5, format "a .[ n ]").
Infix ">>" := shiftr (at level 30, no associativity).
Infix "<<" := shiftl (at level 30, no associativity).
End BitsNotation.

Module Type Bits' (A:Typ) := Bits A <+ BitsNotation A.

Module Type NZBitsSpec
(Import A : NZOrdAxiomsSig')(Import B : Bits' A).

Declare Instance testbit_wd : Proper (eq==>eq==>Logic.eq) testbit.
Axiom testbit_odd_0 : forall a, (2*a+1).[0] = true.
Axiom testbit_even_0 : forall a, (2*a).[0] = false.
Axiom testbit_odd_succ : forall a n, 0<=n -> (2*a+1).[S n] = a.[n].
Axiom testbit_even_succ : forall a n, 0<=n -> (2*a).[S n] = a.[n].
Axiom testbit_neg_r : forall a n, n<0 -> a.[n] = false.

Axiom shiftr_spec : forall a n m, 0<=m -> (a >> n).[m] = a.[m+n].
Axiom shiftl_spec_high : forall a n m, 0<=m -> n<=m -> (a << n).[m] = a.[m-n].
Axiom shiftl_spec_low : forall a n m, m<n -> (a << n).[m] = false.

Axiom land_spec : forall a b n, (land a b).[n] = a.[n] && b.[n].
Axiom lor_spec : forall a b n, (lor a b).[n] = a.[n] || b.[n].
Axiom ldiff_spec : forall a b n, (ldiff a b).[n] = a.[n] && negb b.[n].
Axiom lxor_spec : forall a b n, (lxor a b).[n] = xorb a.[n] b.[n].
Axiom div2_spec : forall a, div2 a == a >> 1.

End NZBitsSpec.

Module Type NZBits (A:NZOrdAxiomsSig) := Bits A <+ NZBitsSpec A.
Module Type NZBits' (A:NZOrdAxiomsSig) := Bits' A <+ NZBitsSpec A.




