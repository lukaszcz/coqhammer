(* Translation-shape regression harness for extraction-factored translation.
   The Makefile redirects this file's Hammer_transl output to extraction_transl.out,
   and check-extraction-transl.sh performs line-based assertions over the printed
   axioms. *)

From Hammer Require Import Hammer.

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Classes.RelationClasses
  Streams Vectors.Vector Lists.List Strings.String.
From Corelib.ssr Require Import ssrbool.

Require Import extraction_matches extraction_deptypes extraction_indexed.

Open Scope string_scope.

Inductive sflag : SProp := sflag_intro : sflag.
Parameter sprop_consumer : sflag -> nat.
Definition sprop_arg_term (h : sflag) : nat := sprop_consumer h.

Definition spec_pruned (n : nat) (p : n = n) : {m : nat | n = m} :=
  exist _ n eq_refl.

Inductive proof_first_subset (A : Type) (P : A -> Prop) : Type :=
| proof_first_intro (pf : True) (x : A) (px : P x).

Definition proof_first_make (n : nat) : proof_first_subset nat (fun m => n = m) :=
  proof_first_intro nat (fun m => n = m) I n eq_refl.

Module ShadowTransport.
Definition eq_rect (a b c d e : nat) : nat := e.
End ShadowTransport.

Definition shadow_eq_rect_user (a b c d e : nat) :=
  ShadowTransport.eq_rect a b c d e.

Module ShadowProofNames.
Definition False_rect (A : Type) (p : nat) : nat := p.
Definition eq_refl (A : Type) (x : A) : nat := 3.
Definition eq_trans (A : Type) (x y z : A) (p q : nat) : nat := p.
Definition eq_sym (A : Type) (x y : A) (p : nat) : nat := p.
Definition JMeq_refl (A : Type) (x : A) : nat := 5.
End ShadowProofNames.

Definition shadow_false_rect_user (p : nat) : nat :=
  ShadowProofNames.False_rect {m : nat | p = m} p.
Definition shadow_eq_refl_user : nat := ShadowProofNames.eq_refl nat 0.
Definition shadow_eq_trans_user : nat := ShadowProofNames.eq_trans nat 0 1 2 11 12.
Definition shadow_eq_sym_user : nat := ShadowProofNames.eq_sym nat 0 1 13.
Definition shadow_jmeq_refl_user : nat := ShadowProofNames.JMeq_refl nat 0.

Inductive onebox (A : Type) : Type :=
| onebox_intro (a : A).

Definition box_arg_collision (A : Type) (a : A) (b : onebox A) : A :=
  match b with
  | onebox_intro _ a => a
  end.

Inductive depbox (A : Type) (F : A -> Type) : Type :=
| depbox_intro (x : A) (pf : F x).

Definition depbox_project (P : nat -> Prop) (b : depbox nat P) : nat :=
  match b with
  | depbox_intro _ _ x _ => x
  end.

(* The two apparent refinement carriers form a cycle through their mutual
   declarations.  They must stay regular rather than recursively expanding
   each other's guards forever. *)
Inductive mutual_ref_a : Type :=
| mutual_ref_a_intro (b : mutual_ref_b) (pf : True)
with mutual_ref_b : Type :=
| mutual_ref_b_intro (a : mutual_ref_a) (pf : True).

Definition mutual_ref_identity (a : mutual_ref_a) : mutual_ref_a := a.

(* The formal [A] field looks informative, but [A] can be instantiated by a
   proposition.  Its declaration-level structural axioms therefore cannot be
   skipped based on the formal instance. *)
Inductive poly_ref (A : Type) : Type :=
| poly_ref_intro (x : A) (pf : True).

Goal True.
  Hammer_dump "hammer_dump_smoke.p".
  exact I.
Qed.

(* SProp regression: the sflag argument must be treated like a proof. *)
Hammer_transl "sprop_arg_term".

(* Prop-premise regression: the proof premise must not become an applied term
   argument in the $_typeof_ axiom. *)
Hammer_transl "spec_pruned".

(* Prop binders before a subset carrier are pruned from typing guards, but the
   following carrier still has to be erased at the constructor occurrence. *)
Hammer_transl "proof_first_make".

(* Same-basename user constants must not be treated as canonical proof/transport
   constants. *)
Hammer_transl "ShadowTransport.eq_rect".
Hammer_transl "shadow_eq_rect_user".
Hammer_transl "ShadowProofNames.False_rect".
Hammer_transl "shadow_false_rect_user".
Hammer_transl "shadow_eq_refl_user".
Hammer_transl "shadow_eq_trans_user".
Hammer_transl "shadow_eq_sym_user".
Hammer_transl "shadow_jmeq_refl_user".

(* Split-case constructor binders must not capture same-named function binders. *)
Hammer_transl "box_arg_collision".

(* Instance-dependent user inductives must be classified from actual parameters,
   not from a declaration-level cache entry produced for formal parameters. *)
Hammer_transl "depbox_project".

(* Recursive carrier cycles fall back, and parameter-dependent declarations
   retain their structural axioms. *)
Hammer_transl "mutual_ref_identity".
Hammer_transl "poly_ref".

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
Hammer_transl "extraction_deptypes.vhead".
Hammer_transl "idiv".
Hammer_transl "idiv2".
Hammer_transl "idiv3".

(* Fording makes split equations independent of index guards read from the
   scrutinee's declared type.  This includes type-level function and fixpoint
   wrappers that are only convertible to the matched family. *)
Hammer_transl "dsize".
Hammer_transl "dheight".
Hammer_transl "dstack_size".

(* The nested indexed match also exercises rigid-clash pruning: only its leaf
   branch is possible at index zero. *)
Hammer_transl "dnested".

(* Indexed-family fixtures.  Commands in an imported .vo are not replayed, so
   invoke them here to put their emissions under the shape-assertion harness. *)
Hammer_transl "breflect".
Hammer_transl "tagged".
Hammer_transl "untag".
Hammer_transl "ibounded".
Hammer_transl "ibval".
Hammer_transl "okp".
Hammer_transl "fromok".
Hammer_transl "isT".
Hammer_transl "fromisT".
Hammer_transl "istrue".
Hammer_transl "fromtrue".
Hammer_transl "cast".
Hammer_transl "vec".
Hammer_transl "extraction_indexed.vhead".
Hammer_transl "dheight2".
Hammer_transl "jmeq_match".

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
Hammer_transl "Nat.eqb_spec".
Hammer_transl "sumbool".
Hammer_transl "reflect".
Hammer_transl "introT".
Hammer_transl "sig".
Hammer_transl "prod".
Hammer_transl "Vector.hd".
Hammer_transl "Streams.hd".
Hammer_transl "Equivalence_Reflexive". (* typeclass method projection *)
