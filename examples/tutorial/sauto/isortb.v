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
  induction l; sauto brefl: on.
  (* The "brefl: on" option enables boolean reflection - automatic
     conversion of boolean statements (arguments to the "is_true"
     coercion) into corresponding propositions in Prop. *)
Qed.

Lemma lem_sortedb_to_sorted_step_by_step : forall l, sortedb l -> Sorted l.
Proof.
  induction l as [| x l IH].
  - sauto.
  - simpl.
    case_split; try strivial.
    (* "case_split" eliminates one discriminee of a match expression
       occurring in the goal or in a hypothesis *)
    breflect.
    (* "breflect" performs boolean reflection - it implements the
       "brefl:" option *)
    (* sauto. *)
    (* By default "sauto" eagerly eliminates discriminees of all 
       match expressions. This behaviour is controlled by the
       "ecases:" option. *)
    (* simpl.
       case_splitting. *)
    (* "case_splitting" repeatedly runs "case_split", "subst" and
       "simpl" - it implements the "cases:" and "ecases:" options *)
    sauto ecases: off.
    Undo.
    sauto cases: -.
    (* One case specify the inductive types whose elements should be
       eliminated when they appear as a discriminee of a match
       expression *)
    Undo.
    sauto brefl: on.
    (* Setting "brefl: on" implies "ecases: off" because eager case
       splitting is often detrimental in combination with boolean
       reflection. *)
    (* Setting "brefl!: on" enables boolean reflection only without
       affecting other options. *)
    (* Some options by default affect other options. A primitive
       version "opt!:" of an option "opt:" never affects any other
       options. *)
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
  time (induction l; sauto brefl: on db: arith).
  Undo.
  (* We do not need inversions in this proof: set "inv: -" or use "hauto" *)
  time (induction l; sauto brefl: on inv: - ctrs: - db: arith).
Qed.

Lemma lem_insert_sorted : forall l x,
    sortedb l -> sortedb (insert l x).
Proof.
  destruct l; hauto brefl: on use: lem_insert_sorted_hlp db: arith.
  (* "hauto" is "sauto inv: - ctrs: -" *)
Qed.

Lemma lem_isort_sorted : forall l, sortedb (isort l).
Proof.
  induction l; sauto use: lem_insert_sorted.
Qed.

Hint Rewrite -> lem_sortedb_iff_sorted : brefl.
(* Boolean reflection can be customised by adding rewrite hints to the
   "brefl" database. *)

Lemma lem_insert_sorted_hlp' : forall l y z,
    y <= z -> sortedb (y :: l) -> sortedb (y :: insert l z).
Proof.
  breflect.
  induction l; sauto db: arith.
  Restart.
  (* induction l; sauto brefl: on db: arith. *)
  (* Eager case splitting is usually a good idea for non-boolean goals
     involving inductive types *)
  induction l; sauto brefl!: on db: arith.
  (* "brefl!:" enables boolean reflection without affecting "ecases:" *)
Qed.

Lemma lem_insert_sorted' : forall l x,
    sortedb l -> sortedb (insert l x).
Proof.
  destruct l; hauto brefl!: on use: lem_insert_sorted_hlp
                db: arith ctrs: Sorted.
Qed.

Lemma lem_isort_sorted' : forall l, sortedb (isort l).
Proof.
  induction l; sauto use: lem_insert_sorted.
Qed.
