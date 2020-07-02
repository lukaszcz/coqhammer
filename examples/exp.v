(* Dependently typed expressions *)

From Hammer Require Import Tactics.
Require Import Program.Equality.
Require Import Arith.

Inductive type := Nat | Bool | Prod (ty1 ty2 : type).

Fixpoint tyeval (ty : type) : Type :=
  match ty with
  | Nat => nat
  | Bool => bool
  | Prod ty1 ty2 => tyeval ty1 * tyeval ty2
  end.

Inductive expr : type -> Type :=
| Var : nat -> expr Nat
| Plus : expr Nat -> expr Nat -> expr Nat
| Equal : expr Nat -> expr Nat -> expr Bool
| Pair : forall {A B}, expr A -> expr B -> expr (Prod A B)
| Fst : forall {A B}, expr (Prod A B) -> expr A
| Snd : forall {A B}, expr (Prod A B) -> expr B
| Const : forall A, tyeval A -> expr A
| Ite : forall {A}, expr Bool -> expr A -> expr A -> expr A.

Definition store := nat -> nat.

Fixpoint eval {A} (s : store) (e : expr A) : tyeval A :=
  match e with
  | Var n => s n
  | Plus e1 e2 => eval s e1 + eval s e2
  | Equal e1 e2 => eval s e1 =? eval s e2
  | Pair e1 e2 => (eval s e1, eval s e2)
  | Fst e => fst (eval s e)
  | Snd e => snd (eval s e)
  | Const _ c => c
  | Ite b e1 e2 => if eval s b then eval s e1 else eval s e2
  end.

Definition simp_plus (e1 e2 : expr Nat) :=
  match e1, e2 with
  | Const Nat n1, Const Nat n2 => Const Nat (n1 + n2)
  | _, Const Nat 0 => e1
  | Const Nat 0, _ => e2
  | _, _ => Plus e1 e2
  end.

Lemma lem_plus : forall s e1 e2, eval s (simp_plus e1 e2) = eval s e1 + eval s e2.
Proof.
  time (depind e1; depelim e2; sauto). (* ~ 0.3s *)
Qed.

Lemma lem_plus' : forall s e1 e2, eval s (simp_plus e1 e2) = eval s e1 + eval s e2.
Proof.
  Fail depind e1; sauto.
  time (depind e1; sauto dep: on). (* ~ 0.4s *)
Qed.

Hint Rewrite lem_plus : simp_db.

Definition simp_equal (e1 e2 : expr Nat) :=
  match e1, e2 with
  | Const Nat n1, Const Nat n2 => Const Bool (n1 =? n2)
  | _, _ => Equal e1 e2
  end.

Lemma lem_equal : forall s e1 e2, eval s (simp_equal e1 e2) = (eval s e1 =? eval s e2).
Proof.
  Fail depind e1; sauto.
  time (depind e1; sauto dep: on). (* ~ 0.1s *)
  (* depind e1; depelim e2; sauto. (* 0.3s *) *)
Qed.

Hint Rewrite lem_equal : simp_db.

Definition unpair_type (T : type) :=
  option (match T with Prod A B => expr A * expr B | _ => unit end).

Definition unpair {A B : type} (e : expr (Prod A B)) : option (expr A * expr B) :=
  match e in expr T return unpair_type T with
  | Pair e1 e2 => Some (e1, e2)
  | _ => None
  end.

Definition simp_fst {A B : type} (e : expr (Prod A B)) : expr A :=
  match unpair e with
  | Some (e1, e2) => e1
  | None => Fst e
  end.

Lemma lem_fst {A B} :
  forall s (e : expr (Prod A B)), eval s (simp_fst e) = fst (eval s e).
Proof.
  depind e; sauto.
Qed.

Hint Rewrite @lem_fst : simp_db.

Definition simp_snd {A B : type} (e : expr (Prod A B)) : expr B :=
  match unpair e with
  | Some (e1, e2) => e2
  | None => Snd e
  end.

Lemma lem_snd {A B} :
  forall s (e : expr (Prod A B)), eval s (simp_snd e) = snd (eval s e).
Proof.
  depind e; sauto.
Qed.

Hint Rewrite @lem_snd : simp_db.

Definition simp_ite {A} (e : expr Bool) (e1 e2 : expr A) : expr A :=
  match e with
  | Const Bool true => e1
  | Const Bool false => e2
  | _ => Ite e e1 e2
  end.

Lemma lem_ite {A} : forall s e (e1 e2 : expr A),
    eval s (simp_ite e e1 e2) = if eval s e then eval s e1 else eval s e2.
Proof.
  depind e; sauto.
Qed.

Hint Rewrite @lem_ite : simp_db.

Fixpoint simp {A} (e : expr A) : expr A :=
  match e with
  | Var n => Var n
  | Plus e1 e2 => simp_plus (simp e1) (simp e2)
  | Equal e1 e2 => simp_equal (simp e1) (simp e2)
  | Pair e1 e2 => Pair (simp e1) (simp e2)
  | Fst e => simp_fst (simp e)
  | Snd e => simp_snd (simp e)
  | Const t c => Const t c
  | Ite e e1 e2 => simp_ite (simp e) (simp e1) (simp e2)
  end.

Lemma lem_simp {A} : forall s (e : expr A), eval s (simp e) = eval s e.
Proof.
  time (depind e; sauto use: lem_plus, lem_equal, @lem_fst, @lem_snd, @lem_ite). (* ~ 0.4s *)
  Undo.
  time (depind e; sauto db: simp_db). (* ~ 0.12s *)
  Undo.
  time (depind e; simpl; autorewrite with simp_db; sauto). (* ~ 0.08s *)
Qed.
