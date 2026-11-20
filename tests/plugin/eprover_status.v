(* Regression test for issue #238.

   E 3.5.x prints its SZS status lines with a `%` prefix (`% SZS status
   Theorem`), where earlier versions used `#`.  The output filter in
   `call_eprover` kept only `# SZS` lines, so a successful E run was rejected
   before reconstruction.  Here E is the only enabled prover and SAutoLimit 0
   skips the sauto pretactic phase, so `hammer` succeeds only if E's success
   status is recognised and its premises are extracted. *)

From Hammer Require Import Hammer.
From Stdlib Require Import Arith.

Set Hammer SAutoLimit 0.
Unset Hammer Vampire.
Unset Hammer Z3.
Unset Hammer CVC4.
Set Hammer Eprover.

Lemma eprover_add_comm : forall n m : nat, n + m = m + n.
Proof. hammer. Qed.
