(* Regression test for issue #130.

   Prover detection runs lazily, on the first invocation of `hammer` in a
   file.  It must not clobber an explicit prover selection (Set/Unset Hammer
   <Prover>) made before that first invocation: detection may only disable a
   prover whose binary is missing, never re-enable one the user turned off.

   We check the prover-agnostic invariant: with every ATP disabled before the
   first `hammer` call, `hammer` must fail (no prover is enabled to run).
   Before the fix, detection re-enabled every installed prover, so `hammer`
   wrongly succeeded.  Note we cannot assert on `Test Hammer <Prover>`: Coq
   restores the declared option value at command boundaries, hiding the direct
   mutation made by detection. *)

From Hammer Require Import Hammer.
From Stdlib Require Import Arith.

Set Hammer GSMode 0.
Unset Hammer Parallel.
Set Hammer SAutoLimit 0.

Unset Hammer Vampire.
Unset Hammer Z3.
Unset Hammer Eprover.
Unset Hammer CVC4.

Goal le 1 2.
  Fail hammer.
Abort.
