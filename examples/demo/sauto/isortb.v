(******************************************************************)
(* Insertion sort (boolean version) *)

From Hammer Require Import Tactics.
From Hammer Require Import Reflect.
(* The Reflect module declares "is_true" as a coercion and defines
   some tactics related to boolean reflection. *)

Require List.
Import List.ListNotations.
Open Scope list_scope.

Require Import Arith.
Require Import Lia.
Require Import Bool.

Inductive Sorted : list nat -> Prop :=
| Sorted_0 : Sorted []
| Sorted_1 : forall x, Sorted [x]
| Sorted_2 : forall x y l, Sorted (y :: l) -> x <= y ->
                           Sorted (x :: y :: l).

Fixpoint sortedb (l : list nat) : bool :=
  match l with
  | [] => true
  | [x] => true
  | x :: (y :: l') as t => (x <=? y) && sortedb t
  end.

Lemma lem_sortedb_iff_sorted : forall l, sortedb l <-> Sorted l.
Proof.
  induction l; simpl; sauto brefl: on eager: off.
  (* The "brefl: on" option enables boolean reflection - automatic
     conversion of boolean statements (arguments to the "is_true"
     coercion) into corresponding propositions in Prop. *)
  (* The option "eager: off" disables all eager heuristics:
     - eager reduction ("ered: off")
     - eager elimination of discriminees in match expressions ("ecases: off")
     - eager directed rewriting ("erew: off")
     - eager inversion of some hypotheses ("einv: off" and "sinv: off")
     - others (see README.md at https://github.com/lukaszcz/coqhammer) *)
  (* The "brelf: on" option often works best in combination with disabling
     some or all of the eager heuristics. *)
  (* But after disabling eager reduction ("ered: off" implied by
     "eager: off") we need to perform "simpl" before invoking
     "sauto". *)
  Undo.
  (* Actually, for this lemma it suffices to disable eager elimination
     of discriminees in match expressions. *)
  induction l; sauto brefl: on ecases: off.
Qed.

Lemma lem_sortedb_to_sorted_step_by_step : forall l, sortedb l -> Sorted l.
Proof.
  induction l as [| x l IH].
  - sauto.
  - simpl.
    case_split; try strivial.
    breflect.
    (* "breflect" performs boolean reflection - it implements the
       "brefl:" option *)
    (* sauto. *)
    (* simpl.
    case_splitting. (* "case_splitting" implements the "cases:" and
                       "ecases:" options *) *)
    sauto ecases: off.
Qed.

(* insert a number into a sorted list preserving the sortedness *)
Fixpoint insert (l : list nat) (x : nat) : list nat :=
  match l with
  | [] => [x]
  | h :: t => if x <=? h then x :: l else h :: insert t x
  end.

(* insertion sort *)
Fixpoint isort (l : list nat) : list nat :=
  match l with
  | [] => []
  | h :: t => insert (isort t) h
  end.

Lemma lem_insert_sorted_hlp : forall l y z,
    y <= z -> sortedb (y :: l) -> sortedb (y :: insert l z).
Proof.
  time (induction l; sauto ecases: off brefl: on db: arith).
  Undo.
  (* We do not need inversions in this proof: set "inv: -" or use "hauto" *)
  time (induction l; sauto ecases: off brefl: on inv: - db: arith).
Qed.

Lemma lem_insert_sorted : forall l x,
    sortedb l -> sortedb (insert l x).
Proof.
  destruct l; hauto ecases: off brefl: on use: lem_insert_sorted_hlp db: arith.
  (* "hauto" is "sauto inv: - ctrs: -" *)
Qed.

Lemma lem_isort_sorted : forall l, sortedb (isort l).
Proof.
  induction l; sauto use: lem_insert_sorted.
Qed.

(* We have proven that the result of "isort" is a sorted list. Now we
   prove that the result is a permutation of the argument. *)

Lemma lem_insert_perm :
  forall l x, Permutation (insert l x) (x :: l).
Proof.
  induction l as [|y ? ?].
  - eauto using Permutation.
  - intro x.
    simpl.
    destruct (Nat.leb_spec x y) as [H|H];
      eauto using Permutation.
Qed.

Lemma lem_insert_perm' :
  forall l x, Permutation (insert l x) (x :: l).
Proof.
  induction l; sauto.
Qed.

Lemma lem_isort_perm : forall l, Permutation (isort l) l.
Proof.
  induction l; simpl; eauto using Permutation, lem_insert_perm.
Qed.

Lemma lem_isort_perm' : forall l, Permutation (isort l) l.
Proof.
  induction l; sauto use: lem_insert_perm.
Qed.
