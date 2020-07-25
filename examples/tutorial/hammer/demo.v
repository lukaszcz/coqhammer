(* "hammer" demo *)

(* The "hammer" tactic works in three phases: *)
(* 1. Machine-learning premise selection. *)
(* 2. Translation to automated theorem provers (ATPs). *)
(* 3. Proof search in the logic of Coq with the dependencies returned
   by the ATPs. *)

(* CoqHammer uses classical first-order ATPs just to select the right
   dependencies. The goal must then be re-proven from scratch in the
   intuitionistic logic of Coq, using the dependencies returned by the
   ATPs. *)

(* The target external tools of CoqHammer are general first-order
   ATPs, not SMT-solvers. CoqHammer can use some SMT-solvers because
   in practice they may often be used in the same way as general
   ATPs. But CoqHammer will never use any of the "modulo theory"
   features of SMT-solvers. Natural numbers, lists, etc., are not
   translated in any special way and the SMT-solvers will see them as
   uninterpreted data types. *)

From Hammer Require Import Hammer.

(* To use the Hammer module which contains the "hammer" tactic you
   need to install the full CoqHammer system:

   opam install coq-hammer

   Or from source: make && make install
 *)

Hammer_version.
Hammer_objects.

Require Import Arith.

Lemma lem_odd : forall n : nat, Nat.Odd n \/ Nat.Odd (n + 1).
Proof.
  (* hammer. *)
  hauto lq: on use: Nat.Odd_succ, Nat.Even_or_Odd, Nat.add_1_r.
Qed.

Lemma lem_even : forall n : nat, Nat.Even n \/ Nat.Even (n + 1).
Proof.
  (* predict 16. *)
  (* hammer. *)
  hauto lq: on use: Nat.add_1_r, Nat.Even_or_Odd, Nat.Even_succ.
Qed.

Lemma lem_pow : forall n : nat, 3 * 3 ^ n = 3 ^ (n + 1).
Proof.
  Fail sauto.
  (* hammer. *)
  hauto lq: on use: Nat.pow_succ_r, Nat.le_0_l, Nat.add_1_r.
Qed.

Require List.
Import List.ListNotations.
Open Scope list_scope.

Lemma lem_incl_concat
  : forall (A : Type) (l m n : list A),
    List.incl l n ->
    List.incl l (n ++ m) /\ List.incl l (m ++ n) /\ List.incl l (l ++ l).
Proof.
  (* hammer. *)
  strivial use: List.incl_appr, List.incl_refl, List.incl_appl.
Qed.

Lemma lem_lst_1 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  (* The "hammer" tactic can't do induction. If induction is necessary
  to carry out the proof, then one needs to start the induction
  manually. *)
  induction l'.
  - (* hammer. *)
    scongruence use: List.app_nil_end.
  - (* hammer. *)
    srun eauto use: List.NoDup_remove_1.
Qed.

Require Import Sorting.Permutation.

Lemma lem_perm_0 {A} : forall (x y : A) l1 l2 l3,
    Permutation l1 (y :: l2) ->
    Permutation (l1 ++ l3) (y :: l2 ++ l3).
Proof.
  (* hammer. *)
  (* Coq.Lists.List.app_comm_cons, Coq.Sorting.Permutation.Permutation_refl, Coq.Sorting.Permutation.Permutation_app *)
  intros.
  hauto lq: on drew: off use: List.app_comm_cons, Permutation_refl, Permutation_app.
Qed.

Lemma lem_perm_1 {A} : forall (x y : A) l1 l2 l3,
    Permutation l1 (y :: l2) ->
    Permutation (x :: l1 ++ l3) (y :: x :: l2 ++ l3).
Proof.
  (* hammer. *)
  eauto using Permutation, Permutation_app, Permutation_refl.
Qed.

Lemma lem_perm_2 : forall (x : nat) l1 l2 l3,
    Permutation (x :: l1) l2 -> Permutation (x :: l3 ++ l1) (l3 ++ l2).
Proof.
  (* hammer. *)
  srun eauto use: Permutation_app_head, Permutation_trans, Permutation_app_comm, Permutation_cons_app.
Qed.

Lemma lem_perm_3 : forall (x y : nat) l1 l2 l3,
    Permutation (x :: l1) l2 -> Permutation (x :: y :: l1 ++ l3) (y :: l2 ++ l3).
Proof.
  (* hammer. *)
  srun eauto use: Permutation_sym, @lem_perm_1.
Qed.

Lemma lem_perm_4 : forall (x y : nat) l1 l2 l3,
    Permutation (x :: l1) l2 -> Permutation (x :: y :: l3 ++ l1) (y :: l3 ++ l2).
Proof.
  (* hammer. *)
  intros.
  rewrite List.app_comm_cons.
  pattern (y :: l3).
  rewrite List.app_comm_cons.
  apply lem_perm_2; assumption.
Qed.

(*
Lemma lem_classic : forall P : Prop, P \/ ~P.
Proof.
  hammer.
Qed.*)
