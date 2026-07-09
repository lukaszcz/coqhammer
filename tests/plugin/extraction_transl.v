(* Translation-shape regression harness for the extraction-factored
   translation plan. The Makefile redirects this file's Hammer_transl output to
   extraction_transl.out and check-extraction-transl.sh performs line-based
   assertions over the printed axioms. *)

From Hammer Require Import Hammer.

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Classes.RelationClasses
  Streams Vectors.Vector Lists.List.

Require Import extraction_matches extraction_deptypes.

Inductive sflag : SProp := sflag_intro : sflag.
Parameter sprop_consumer : sflag -> nat.
Definition sprop_arg_term (h : sflag) : nat := sprop_consumer h.

Goal True.
  Hammer_dump "hammer_dump_smoke.p".
  exact I.
Qed.

(* SProp regression: the sflag argument must be treated like a proof. *)
Hammer_transl "sprop_arg_term".

(* Phase-0 plumbing regression: the later WF-recursion mark must not leak
   between top-level translations. *)
Hammer_test_wf_mark_reset "myadd" "g".

(* Corpus constants from extraction_matches.v. *)
Hammer_transl "myadd".
Hammer_transl "g".
Hammer_transl "k".
Hammer_transl "even".
Hammer_transl "odd".

(* Corpus constants from extraction_deptypes.v. *)
Hammer_transl "h".
Hammer_transl "safe_pred".
Hammer_transl "pval".
Hammer_transl "beq".
Hammer_transl "tag".
Hammer_transl "idiv".

(* Stdlib regression list. Keep these as structural snapshots, not golden files:
   they pin one representative per fallback/coverage row from PLAN.md §10 while
   remaining robust across Rocq point releases. *)
Hammer_transl "Nat.add".
Hammer_transl "app".              (* List.app *)
Hammer_transl "Forall".           (* List.Forall *)
Hammer_transl "eq_ind_r".
Hammer_transl "proj1".
Hammer_transl "Acc_rect".
Hammer_transl "Nat.eq_dec".
Hammer_transl "sumbool".
Hammer_transl "sig".
Hammer_transl "prod".
Hammer_transl "Vector.hd".
Hammer_transl "Streams.hd".
Hammer_transl "Equivalence_Reflexive". (* typeclass method projection *)
