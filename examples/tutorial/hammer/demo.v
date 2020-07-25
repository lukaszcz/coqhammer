(* "hammer" demo *)

From Hammer Require Import Hammer.

Require List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Sorting.Permutation.

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
  srun eauto use: @Permutation_app_head, @Permutation_trans, @Permutation_app_comm, @Permutation_cons_app.
Qed.

Lemma lem_perm_3 : forall (x y : nat) l1 l2 l3,
    Permutation (x :: l1) l2 -> Permutation (x :: y :: l1 ++ l3) (y :: l2 ++ l3).
Proof.
  (* hammer. *)
  srun eauto use: @Permutation_sym, @lem_perm_1.
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

Lemma lem_perm_5 {A} : forall (x y z : A) l1 l2 l3 l,
    Permutation (x :: l1 ++ l2) (y :: l3) ->
    Permutation (z :: l ++ x :: l1 ++ l2) (y :: z :: l ++ l3).
Proof.
  (* hammer. *)
  intros *.
  intro H.
  rewrite List.app_comm_cons.
  eapply perm_trans.
  - eapply Permutation_app; [ apply Permutation_refl | eassumption ].
  - rewrite List.app_comm_cons.
    apply Permutation_sym.
    apply Permutation_middle.
Qed.

Lemma lem_lst_1 : forall (A : Type) (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l.
Proof.
  (* The "hammer" tactic can't do induction. If induction is necessary
  to carry out the proof, then one needs to start the induction
  manually. *)
  induction l'.
  - (* hammer. *)
    scongruence use: @List.app_nil_end.
  - (* hammer. *)
    srun eauto use: @List.NoDup_remove_1.
Qed.

(*
Lemma lem_false : False.
Proof.
  hammer.
Qed.*)

(*
Lemma lem_classic : forall P : Prop, P \/ ~P.
Proof.
  hammer.
Qed.*)
