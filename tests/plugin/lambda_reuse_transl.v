(* Focused regressions for lambda-schema reuse and cache replay.  Reuse is
   allowed only after the schema bundle is available to the current declaration
   and the translated schema application has its full arity. *)

From Hammer Require Import Hammer.

Parameter use_endo : forall Z : Type, (Z -> Z) -> nat.
Parameter use_nat_fun : forall Z : Type, (Z -> nat) -> nat.
Parameter consume_fun : forall Z : Type, Z -> (nat -> nat) -> nat.
Parameter X Y U : Type.
Parameter x : X.
Parameter gx : X -> X.
Parameter gy : Y -> Y.
Parameter R : Prop.

(* The second lambda is a ground instance of the first one. *)
Definition reuse_ok (Z : Type) (f : Z -> Z) : nat :=
  Nat.add (use_endo Z (fun z : Z => f z))
          (use_endo X (fun x : X => gx x)).

(* The syntactic match exists, but the lambda binder survives only in the
   schema.  Reuse must be rejected before it can identify a value with a
   function. *)
Definition reject_binder_erasure (Z : Type) : nat :=
  Nat.add (use_nat_fun Z (fun _ : Z => O))
          (use_nat_fun R (fun _ : R => O)).

(* Both lambda binders survive.  The schema context, however, contains [c : Z].
   In the instance [c := p : R], and conversion erases that proof from the
   candidate schema-symbol application.  Its actual spine is therefore shorter
   than the schema definition arity, so reuse must fall back to a fresh lift. *)
Definition reject_context_arity
    (Z : Type) (c : Z) (f : nat -> nat) (p : R) : nat :=
  Nat.add
    (use_nat_fun nat (fun _ : nat => consume_fun Z c f))
    (use_nat_fun nat
       (fun _ : nat =>
          consume_fun R p
            (fun n : nat => match n with O => O | S m => m end))).

Inductive replay_box : Type := replay_left | replay_right.
Parameter choose : forall Z : Type, Z -> replay_box.

(* A schema translated in another declaration is not available here merely
   because its registry entry survives.  This lift's bundle also contains a
   case dependency, allowing replay to be observed independently of symbol
   reuse. *)
Definition owner_seed (Z : Type) (z : Z) : nat :=
  use_nat_fun Z
    (fun x : Z =>
       match choose Z x with replay_left => O | replay_right => S O end).

Definition owner_isolated : nat :=
  use_endo Y (fun y : Y => gy y).

(* The first lambda is an exact cross-owner hit on [owner_seed].  Replaying its
   bundle makes the schema available here, so the previously unseen [U]
   instance reuses it; it must also deliver [replay_box]'s structural theory to
   this owner. *)
Definition owner_replay (Z : Type) (z : Z) : nat :=
  Nat.add
    (use_nat_fun Z
       (fun x : Z =>
          match choose Z x with replay_left => O | replay_right => S O end))
    (use_nat_fun U
       (fun u : U =>
          match choose U u with replay_left => O | replay_right => S O end)).

(* A lambda whose body lifts a second, nested lambda: the bundle cached for the
   outer one therefore defines two symbols, and replaying it must make both of
   them available, not only its head. *)
Parameter V : Type.
Parameter gv : V -> V.

Definition nested_seed : nat :=
  use_nat_fun (V -> V) (fun g : V -> V => use_endo V (fun a : V => g a)).

(* The first summand is an exact hit on [nested_seed]'s outer bundle.  The
   second is a ground instance of the lambda nested inside that bundle, so it
   can only reuse the nested symbol if replaying the bundle recorded ownership
   for every symbol the bundle defines. *)
Definition nested_replay : nat :=
  Nat.add
    (use_nat_fun (V -> V) (fun g : V -> V => use_endo V (fun a : V => g a)))
    (use_endo V (fun a : V => gv a)).

Inductive attr_marker : Type := attr_left | attr_right.
Parameter attr_mark : attr_marker.

(* The second summand reuses that nested lambda again, but here the matching
   substitution is a [match], so translating the schema application contributes
   [attr_marker]'s structural theory.  That dependency belongs to this
   occurrence, not to the shared symbol. *)
Definition attr_instance : nat :=
  Nat.add
    (use_nat_fun (V -> V) (fun g : V -> V => use_endo V (fun a : V => g a)))
    (use_endo V
       (fun a : V =>
          (match attr_mark with attr_left => gv | attr_right => gv end) a)).

(* An exact hit on the nested lambda alone -- the enclosing lambda differs, so
   only the inner one is replayed.  It must receive that symbol's own theory
   and nothing [attr_instance]'s substitution happened to need. *)
Definition attr_probe : nat :=
  use_nat_fun (V -> V) (fun g : V -> V => S (use_endo V (fun a : V => g a))).

(* Goal-level translation names every goal [_HAMMER_GOAL] and keeps the
   translation caches across goals, so ownership recorded while translating one
   goal must not survive into the next. *)
Parameter W : Type.
Parameter gw : W -> W.

Hammer_transl "reuse_ok".
Hammer_transl "reject_binder_erasure".
Hammer_cleanup.
Hammer_transl "reject_context_arity".
(* The rejected candidate above translates the substituted lambda before the
   later proof argument makes its schema spine too short.  Its effects are
   captured and discarded; the counter makes that rollback path behavioral
   rather than a source-shape assertion. *)
Hammer_speculation_stats.
Hammer_transl "owner_seed".
Hammer_transl "owner_isolated".
Hammer_transl "owner_replay".
(* The closure contains [owner_replay] but not [owner_seed], so its structural
   axioms disappear if the exact lambda hit stops replaying dependencies. *)
Hammer_dump_transl "owner_replay" "lambda-reuse-structural.p".

Set Hammer Predictions 0.
Set Hammer SAutoLimit 0.

(* Both definitions are translated in one problem.  [owner_seed] first makes
   its schema bundle available only to itself; the exact occurrence at the
   start of [owner_replay] must replay that full bundle and mark the second
   owner before its ground instance is reached. *)
Goal owner_seed X x = owner_seed X x /\
     owner_replay X x = owner_replay X x.
  hammer_dump "lambda-reuse-owners.p".
Abort.

Hammer_transl "nested_seed".
Hammer_transl "nested_replay".
Hammer_transl "attr_instance".
Hammer_dump_transl "attr_instance" "lambda-reuse-attribution-instance.p".
Hammer_dump_transl "attr_probe" "lambda-reuse-attribution-probe.p".

Goal use_nat_fun (W -> W) (fun g : W -> W => use_endo W (fun a : W => g a)) = O.
  hammer_transl.
Abort.

(* A ground instance of the previous goal's nested lambda.  The previous goal
   carried the same declaration name, so without dropping its ownership this
   would reuse a lift a fresh process would have minted anew. *)
Goal use_endo W (fun a : W => gw a) = O.
  hammer_transl.
Abort.
