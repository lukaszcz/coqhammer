From Hammer Require Import Hammer.

From Stdlib Require Import Lists.List Bool.Bool Arith.PeanoNat.

Set Hammer SAutoLimit 0.

Definition mypred (n : nat) := match n with 0 => 0 | S m => m end.
Fixpoint myadd (n m : nat) := match n with 0 => m | S k => S (myadd k m) end.
Definition g (x : nat) :=
  match x with 0 => 0 | S y => match y with 0 => 1 | S z => z end end.
Definition k (b : bool) :=
  match negb b with true => 0 | false => 1 end.
Definition is_zero (n : nat) : Prop :=
  match n with 0 => True | S _ => False end.
Definition hd_d {A} (d : A) (l : list A) :=
  match l with nil => d | cons x _ => x end.
Fixpoint even (n : nat) : bool :=
  match n with 0 => true | S m => odd m end
with odd (n : nat) : bool :=
  match n with 0 => false | S m => even m end.
Inductive tree := L | N (l : tree) (x : nat) (r : tree).
Fixpoint tsize (t : tree) :=
  match t with L => 0 | N l _ r => S (myadd (tsize l) (tsize r)) end.
Fixpoint tmirror (t : tree) :=
  match t with L => L | N l x r => N (tmirror r) x (tmirror l) end.
Inductive rose := Rose (children : list rose).
Fixpoint rsize (r : rose) : nat :=
  match r with Rose cs => S (List.fold_right (fun c acc => rsize c + acc) 0 cs) end.

Lemma extraction_myadd_ground : myadd 2 2 = 4.
Proof. hammer. Qed.

Lemma extraction_myadd_succ : forall n m, myadd (S n) m = S (myadd n m).
Proof. hammer. Qed.

Lemma extraction_mypred_succ : forall n, mypred (S n) = n.
Proof. hammer. Qed.

Lemma extraction_mypred_nonzero : forall n, n <> 0 -> S (mypred n) = n.
Proof. hammer. Qed.

Lemma extraction_match_goal : forall n (m : nat), (match n with 0 => m | S _ => m end) = m.
Proof. hammer. Qed.

Lemma extraction_k_true : k true = 1.
Proof. hammer. Qed.

Lemma extraction_k_cases : forall b, k b = 0 \/ k b = 1.
Proof. hammer. Qed.

Lemma extraction_g_deep : forall x, g (S (S x)) = x.
Proof. hammer. Qed.

Lemma extraction_g_one : g 1 = 1.
Proof. hammer. Qed.

Lemma extraction_is_zero_zero : is_zero 0.
Proof. hammer. Qed.

Lemma extraction_is_zero_succ : forall n, ~ is_zero (S n).
Proof. hammer. Qed.

Lemma extraction_hd_d_cons : forall (d x : nat) l, hd_d d (cons x l) = x.
Proof. hammer. Qed.

Lemma extraction_even_ss : forall n, even (S (S n)) = even n.
Proof. hammer. Qed.

Lemma extraction_tsize_node : forall l x r, tsize (N l x r) = S (myadd (tsize l) (tsize r)).
Proof. hammer. Qed.

Lemma extraction_tmirror_node :
  forall l x r,
    tmirror (tmirror (N l x r)) =
    N (tmirror (tmirror l)) x (tmirror (tmirror r)).
Proof. hammer. Qed.

Lemma tmirror_invol : forall t, tmirror (tmirror t) = t.
Proof.
  induction t as [|l IHl x r IHr]; simpl; [reflexivity|].
  now rewrite IHl, IHr.
Qed.

Lemma extraction_tmirror_injective : forall t u, tmirror t = tmirror u -> t = u.
Proof. hammer. Qed.

Lemma extraction_list_map_cons :
  forall (A B : Type) (f : A -> B) (x : A) l,
    List.map f (cons x l) = cons (f x) (List.map f l).
Proof. hammer. Qed.

Lemma extraction_nat_eqb_refl : Nat.eqb 5 5 = true.
Proof. hammer. Qed.

Lemma extraction_rsize_nil : rsize (Rose nil) = 1.
Proof. hammer. Qed.
