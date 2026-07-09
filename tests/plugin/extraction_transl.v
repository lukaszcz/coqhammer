(* Translation-shape regression harness for extraction-factored translation.
   The Makefile redirects this file's Hammer_transl output to extraction_transl.out,
   and check-extraction-transl.sh performs line-based assertions over the printed
   axioms. *)

From Hammer Require Import Hammer.

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Classes.RelationClasses
  Streams Vectors.Vector Lists.List Strings.String.
From Corelib.ssr Require Import ssrbool.

Require Import extraction_matches extraction_deptypes.

Open Scope string_scope.

Inductive sflag : SProp := sflag_intro : sflag.
Parameter sprop_consumer : sflag -> nat.
Definition sprop_arg_term (h : sflag) : nat := sprop_consumer h.

Definition spec_pruned (n : nat) (p : n = n) : {m : nat | n = m} :=
  exist _ n eq_refl.

Module ShadowTransport.
Definition eq_rect (a b c d e : nat) : nat := e.
End ShadowTransport.

Definition shadow_eq_rect_user (a b c d e : nat) :=
  ShadowTransport.eq_rect a b c d e.

Inductive onebox (A : Type) : Type :=
| onebox_intro (a : A).

Definition box_arg_collision (A : Type) (a : A) (b : onebox A) : A :=
  match b with
  | onebox_intro _ a => a
  end.

Goal True.
  hammer_dump "hammer_dump_smoke.p".
  exact I.
Qed.

(* SProp regression: the sflag argument must be treated like a proof. *)
Hammer_transl "sprop_arg_term".

(* Prop-premise regression: the proof premise must not become an applied term
   argument in the $_typeof_ axiom. *)
Hammer_transl "spec_pruned".

(* Same-basename user constants must not be treated as Coq transports. *)
Hammer_transl "ShadowTransport.eq_rect".
Hammer_transl "shadow_eq_rect_user".

(* Split-case constructor binders must not capture same-named function binders. *)
Hammer_transl "box_arg_collision".

(* WF-recursion marker regression: the mark must not leak between top-level
   translations. *)
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
Hammer_transl "tr".
Hammer_transl "proj1_sig".
Hammer_transl "pval".
Hammer_transl "beq".
Hammer_transl "between".
Hammer_transl "tag".
Hammer_transl "vhead".
Hammer_transl "idiv".
Hammer_transl "idiv2".
Hammer_transl "idiv3".

(* Stdlib regression list. Keep these as structural snapshots, not golden files;
   they pin representative fallback and coverage cases while remaining robust
   across Rocq point releases. *)
Hammer_transl "Nat.add".
Hammer_transl "app".              (* List.app *)
Hammer_transl "Forall".           (* List.Forall *)
Hammer_transl "eq_ind_r".
Hammer_transl "proj1".
Hammer_transl "Acc_rect".
Hammer_transl "Nat.eq_dec".
Hammer_transl "sumbool".
Hammer_transl "reflect".
Hammer_transl "introT".
Hammer_transl "sig".
Hammer_transl "prod".
Hammer_transl "Vector.hd".
Hammer_transl "Streams.hd".
Hammer_transl "Equivalence_Reflexive". (* typeclass method projection *)
