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
   mutation made by detection.

   SAutoLimit 0 is required, not a tidying detail: the goal below is trivial,
   so with the default limit sauto closes it before any ATP is consulted and
   `hammer` succeeds whatever the prover flags say.  The test would still pass,
   but for a reason unrelated to detection. *)

From Hammer Require Import Hammer.
From Stdlib Require Import Arith.

Set Hammer SAutoLimit 0.

Unset Hammer Vampire.
Unset Hammer Z3.
Unset Hammer Eprover.
Unset Hammer CVC4.

Goal le 1 2.
  Fail hammer.
Abort.
