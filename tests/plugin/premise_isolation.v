(* Bounded regression for ATP problem isolation and the POPLMark1a
   [scope_le_app_len] translation.  Sequentially growing selections used to
   retain translation state from the preceding ATP problem, while repeated
   lambda-side-axiom replay could grow memory without a bound. *)

From Hammer Require Import HammerHook.
From Stdlib Require Import Program.
From Equations.Prop Require Import Equations.
From Stdlib Require Import EquivDec.
From Stdlib Require Import Arith.

Definition scope := nat.

Inductive var : scope -> Set :=
| FO : forall {n}, var (S n)
| FS : forall {n}, var n -> var (S n).

Derive Signature NoConfusion NoConfusionHom for var.

Inductive scope_le : scope -> scope -> Set :=
| scope_le_n : forall {n m}, n = m -> scope_le n m
| scope_le_S : forall {n m}, scope_le n m -> scope_le n (S m)
| scope_le_map : forall {n m}, scope_le n m -> scope_le (S n) (S m).

Derive Signature NoConfusion NoConfusionHom Subterm for scope_le.

Equations scope_le_app {a b c} (p : scope_le a b) (q : scope_le b c) : scope_le a c :=
scope_le_app p (scope_le_n eq_refl) := p;
scope_le_app p (scope_le_S q) := scope_le_S (scope_le_app p q);
scope_le_app p (scope_le_map q) with p :=
{ | scope_le_n eq_refl := scope_le_map q;
  | scope_le_S p' := scope_le_S (scope_le_app p' q);
  | scope_le_map p' := scope_le_map (scope_le_app p' q) }.

Lemma scope_le_app_len n m (q : scope_le n m) :
  scope_le_app (scope_le_n eq_refl) q = q.
Proof.
  Unset Hammer Blacklist.
  Set Hammer FilterProgram.
  Set Hammer FilterClasses.
  Set Hammer FilterHurkens.
  Set Hammer PredictMethod "knn".
  Set Hammer Predictions 32.
  hammer_dump "premise_seq32.p".
  Set Hammer Predictions 64.
  hammer_dump "premise_seq64.p".
  Set Hammer Predictions 128.
  hammer_dump "premise_seq128.p".
Abort.

(* Include an explicit reset as well as the per-problem reset in [hammer_dump]:
   this makes the second dump the fresh-process reference for the comparison in
   the Makefile. *)
Hammer_cleanup.

Lemma scope_le_app_len_fresh n m (q : scope_le n m) :
  scope_le_app (scope_le_n eq_refl) q = q.
Proof.
  Unset Hammer Blacklist.
  Set Hammer FilterProgram.
  Set Hammer FilterClasses.
  Set Hammer FilterHurkens.
  Set Hammer PredictMethod "knn".
  Set Hammer Predictions 128.
  hammer_dump "premise_fresh128.p".
Abort.
