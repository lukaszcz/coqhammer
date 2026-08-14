(* Focused translation regression for the G-reading of proposition-valued
   case expressions. *)

From Hammer Require Import Hammer.

Definition case_prop (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Definition compound_case_prop (n : nat) : Prop :=
  match S n with
  | O => True
  | S _ => False
  end.

Definition false_case_prop (h : False) : Prop :=
  match h with end.

Definition eq_case_prop (A : Type) (x y : A) (e : x = y) : Prop :=
  match e with
  | eq_refl => True
  end.

Definition two_false_case_props (h1 h2 : False) : Prop :=
  (match h1 with end) /\ (match h2 with end).

Definition sumbool_case_prop (P Q : Prop) (s : {P} + {Q}) : Prop :=
  match s with
  | left _ => P
  | right _ => Q
  end.

Inductive case_vec (A : Type) : nat -> Type :=
| case_vnil : case_vec A O
| case_vcons : forall n, A -> case_vec A n -> case_vec A (S n).

Definition vec_case_prop (A : Type) (n : nat) (v : case_vec A n) : Prop :=
  match v with
  | case_vnil _ => True
  | case_vcons _ _ _ _ => False
  end.

Axiom compound_eq_proof : forall (A : Type) (x : A), x = x.

Definition compound_eq_case_prop (A : Type) (x : A) : Prop :=
  match compound_eq_proof A x with
  | eq_refl => True
  end.

Axiom proof_choice : bool.
Axiom left_eq_proof : forall (A : Type) (x : A), x = x.
Axiom right_eq_proof : forall (A : Type) (x : A), x = x.

Definition nested_eq_case_prop (A : Type) (x : A) : Prop :=
  match (if proof_choice then left_eq_proof A x else right_eq_proof A x) with
  | eq_refl => True
  end.

Axiom false_id : False -> False.

Definition compound_false_case_prop (h : False) : Prop :=
  match false_id h with end.

Inductive delivery_box : Type :=
| delivery_left (n : nat)
| delivery_right (n : nat).

Definition delivery_value (b : delivery_box) : nat :=
  match b with
  | delivery_left n => n
  | delivery_right n => S n
  end.

Axiom hidden_delivery : delivery_box.

Definition delivery_cache_warm : nat :=
  S (match hidden_delivery with
     | delivery_left n => n
     | delivery_right n => S n
     end).

Definition delivery_cache_hit : nat :=
  Nat.add
    (match hidden_delivery with
     | delivery_left n => n
     | delivery_right n => S n
     end)
    (match hidden_delivery with
     | delivery_left n => n
     | delivery_right n => S n
     end).

Inductive prop_case_box : Type :=
| prop_case_left
| prop_case_right.

Definition prop_case_only (b : prop_case_box) : Prop :=
  match b with
  | prop_case_left => True
  | prop_case_right => False
  end.

(* The inspected inductive is hidden from this declaration's type and from the
   dump goal, so its structural axioms can arrive only through case dependency
   replay. *)
Definition prop_case_closed : Prop :=
  match prop_case_left with
  | prop_case_left => True
  | prop_case_right => False
  end.

Hammer_transl "case_prop".
Hammer_transl "compound_case_prop".
Hammer_transl "false_case_prop".
Hammer_transl "eq_case_prop".
Hammer_transl "two_false_case_props".
Hammer_transl "sumbool_case_prop".
Hammer_transl "vec_case_prop".
Hammer_transl "compound_eq_case_prop".
Hammer_transl "nested_eq_case_prop".
Hammer_transl "compound_false_case_prop".
Hammer_transl "delivery_cache_warm".
(* A different owner hits the exact case lift warmed above.  Dumping this
   declaration's closure without premise selection excludes the warm owner, so
   [delivery_box]'s structural theory can arrive only through hit replay. *)
Hammer_transl "delivery_cache_hit".
Hammer_dump_transl "delivery_cache_hit" "case-structural-cache-hit.p".
Hammer_transl "prop_case_only".
Hammer_transl "prop_case_closed".

Set Hammer Predictions 1024.
Set Hammer SAutoLimit 0.

Goal case_prop O.
Proof. hammer. Qed.

Goal forall n, ~ case_prop (S n).
Proof. hammer. Qed.

Goal forall b, delivery_value b = delivery_value b.
  hammer_dump "case-structural-delivery.p".
Abort.

Set Hammer Predictions 0.

(* This goal does not expose [prop_case_box], but translating the selected
   closed definition still needs its case structure. *)
Goal prop_case_closed <-> prop_case_closed.
  hammer_dump "prop-case-structural.p".
Abort.
