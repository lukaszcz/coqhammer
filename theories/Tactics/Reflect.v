(* Boolean reflection tactics *)
(* Authors: Burak Ekici, Lukasz Czajka *)

Coercion is_true : bool >-> Sortclass.

Require Export Bool.
Require Import Setoid.
Require Import Lia.
Require Import BinInt BinNat PeanoNat.
Require Import ssreflect ssrbool.

(* bool *)

Lemma andE : forall b1 b2, b1 && b2 <-> b1 /\ b2.
Proof.
  split; move /andP; done.
Qed.

Lemma orE : forall b1 b2, b1 || b2 <-> b1 \/ b2.
Proof.
  split; move /orP; done.
Qed.

Lemma negE : forall b, negb b <-> ~b.
Proof.
  split; move /negP; done.
Qed.

Lemma implE : forall b1 b2, implb b1 b2 <-> (b1 -> b2).
Proof.
  split; destruct b1, b2; intuition.
Qed.

Lemma iffE : forall b1 b2, eqb b1 b2 <-> (b1 <-> b2).
Proof.
  split; destruct b1, b2; intuition.
Qed.

Lemma falseE : false <-> False.
Proof. split; [ congruence | auto ]. Qed.

Lemma trueE : true <-> True.
Proof. split; auto. Qed.

(* Z *)

Lemma Z_eqb_eq: forall a b: Z, Z.eqb a b <-> a = b.
Proof. intros; unfold is_true; now rewrite Z.eqb_eq. Qed.

Lemma Z_gtb_gt: forall a b: Z, Z.gtb a b <-> Z.gt a b.
Proof.
  split.
  - rewrite /is_true Z.gtb_lt. now apply Z.lt_gt.
  - rewrite /is_true Z.gtb_lt. now apply Z.gt_lt.
Qed.

Lemma Z_geb_ge: forall a b: Z, Z.geb a b <-> Z.ge a b.
Proof.
  split.
  - rewrite /is_true Z.geb_le. now apply Z.le_ge.
  - rewrite /is_true Z.geb_le. now apply Z.ge_le.
Qed.

Lemma Z_ltb_lt: forall a b: Z, Z.ltb a b <-> Z.lt a b.
Proof.
  split; now rewrite /is_true Z.ltb_lt.
Qed.

Lemma Z_leb_le: forall a b: Z, Z.leb a b <-> Z.le a b.
Proof.
  split; now rewrite /is_true Z.leb_le.
Qed.

(* N *)

Lemma N_eqb_eq: forall a b, N.eqb a b <-> a = b.
Proof. intros; unfold is_true; now rewrite N.eqb_eq. Qed.

Lemma N_ltb_lt: forall a b, N.ltb a b <-> N.lt a b.
Proof.
  split; now rewrite /is_true N.ltb_lt.
Qed.

Lemma N_leb_le: forall a b, N.leb a b <-> N.le a b.
Proof.
  split; now rewrite /is_true N.leb_le.
Qed.

Lemma N_gt_ltb: forall a b, N.gt a b <-> N.ltb b a.
Proof.
  split; rewrite N_ltb_lt; lia.
Qed.

Lemma N_ge_leb: forall a b, N.ge a b <-> N.leb b a.
Proof.
  split; rewrite N_leb_le; lia.
Qed.

(* nat *)

Lemma Nat_eqb_eq: forall a b, Nat.eqb a b <-> a = b.
Proof. intros; unfold is_true; now rewrite Nat.eqb_eq. Qed.

Lemma Nat_ltb_lt: forall a b, Nat.ltb a b <-> a < b.
Proof.
  split; now rewrite /is_true Nat.ltb_lt.
Qed.

Lemma Nat_leb_le: forall a b, Nat.leb a b <-> a <= b.
Proof.
  split; now rewrite /is_true Nat.leb_le.
Qed.

Lemma Nat_gt_ltb: forall a b, a > b <-> Nat.ltb b a.
Proof.
  split; rewrite Nat_ltb_lt; auto with arith.
Qed.

Lemma Nat_ge_leb: forall a b, a >= b <-> Nat.leb b a.
Proof.
  split; rewrite Nat_leb_le; auto with arith.
Qed.

(* bool to Prop reflection *)

Create HintDb brefl discriminated.

Global Hint Rewrite -> andE : brefl.
Global Hint Rewrite -> orE : brefl.
Global Hint Rewrite -> negE : brefl.
Global Hint Rewrite -> implE : brefl.
Global Hint Rewrite -> iffE : brefl.
Global Hint Rewrite -> falseE : brefl.
Global Hint Rewrite -> trueE : brefl.

Global Hint Rewrite -> Z_eqb_eq : brefl.
Global Hint Rewrite -> Z_gtb_gt : brefl.
Global Hint Rewrite -> Z_geb_ge : brefl.
Global Hint Rewrite -> Z_ltb_lt : brefl.
Global Hint Rewrite -> Z_leb_le : brefl.

Global Hint Rewrite -> N_eqb_eq : brefl.
Global Hint Rewrite -> N_ltb_lt : brefl.
Global Hint Rewrite -> N_leb_le : brefl.

Global Hint Rewrite -> Nat_eqb_eq : brefl.
Global Hint Rewrite -> Nat_ltb_lt : brefl.
Global Hint Rewrite -> Nat_leb_le : brefl.

Tactic Notation "breflect" :=
  try rewrite_strat topdown hints brefl.

Tactic Notation "breflect" "in" hyp(H) :=
  try rewrite_strat topdown hints brefl in H.

Tactic Notation "breflect" "in" "*" :=
  breflect;
  repeat match goal with
         | [H : _ |- _ ] => rewrite_strat topdown hints brefl in H
         end.

(* Prop to bool reification *)

Create HintDb breif discriminated.

Global Hint Rewrite <- andE : breif.
Global Hint Rewrite <- orE : breif.
Global Hint Rewrite <- negE : breif.
Global Hint Rewrite <- implE : breif.
Global Hint Rewrite <- iffE : breif.
Global Hint Rewrite <- falseE : breif.
Global Hint Rewrite <- trueE : breif.

Global Hint Rewrite <- Z_eqb_eq : breif.
Global Hint Rewrite <- Z_gtb_gt : breif.
Global Hint Rewrite <- Z_geb_ge : breif.
Global Hint Rewrite <- Z_ltb_lt : breif.
Global Hint Rewrite <- Z_leb_le : breif.

Global Hint Rewrite <- N_eqb_eq : breif.
Global Hint Rewrite <- N_ltb_lt : breif.
Global Hint Rewrite <- N_leb_le : breif.
Global Hint Rewrite -> N_gt_ltb : breif.
Global Hint Rewrite -> N_ge_leb : breif.

Global Hint Rewrite <- Nat_eqb_eq : breif.
Global Hint Rewrite <- Nat_ltb_lt : breif.
Global Hint Rewrite <- Nat_leb_le : breif.
Global Hint Rewrite -> Nat_gt_ltb : breif.
Global Hint Rewrite -> Nat_ge_leb : breif.

Tactic Notation "breify" :=
  try rewrite_strat topdown hints breif.

Tactic Notation "breify" "in" hyp(H) :=
  try rewrite_strat topdown hints breif in H.

Tactic Notation "breify" "in" "*" :=
  breify;
  repeat match goal with
         | [H : _ |- _ ] => rewrite_strat topdown hints breif in H
         end.

(* Boolean simplification *)

Create HintDb bsimpl discriminated.

Global Hint Rewrite -> Bool.orb_true_r : bsimpl.
Global Hint Rewrite -> Bool.orb_true_l : bsimpl.
Global Hint Rewrite -> Bool.orb_false_r : bsimpl.
Global Hint Rewrite -> Bool.orb_false_l : bsimpl.
Global Hint Rewrite -> Bool.andb_true_r : bsimpl.
Global Hint Rewrite -> Bool.andb_true_l : bsimpl.
Global Hint Rewrite -> Bool.andb_false_r : bsimpl.
Global Hint Rewrite -> Bool.andb_false_l : bsimpl.
Global Hint Rewrite <- N.leb_antisym : bsimpl.
Global Hint Rewrite <- N.ltb_antisym : bsimpl.
Global Hint Rewrite <- Nat.leb_antisym : bsimpl.
Global Hint Rewrite <- Nat.ltb_antisym : bsimpl.

Tactic Notation "bsimpl" :=
  try rewrite_strat topdown hints bsimpl.

Tactic Notation "bsimpl" "in" hyp(H) :=
  try rewrite_strat topdown hints bsimpl in H.

Tactic Notation "bsimpl" "in" "*" :=
  bsimpl;
  repeat match goal with
         | [H : _ |- _ ] => rewrite_strat topdown hints bsimpl in H
         end.

(* hardcoded one-step reflection *)

Tactic Notation "brefl" :=
  lazymatch goal with
  | [ |- is_true (andb _ _) ] => rewrite -> andE
  | [ |- is_true (orb _ _) ] => rewrite -> orE
  | [ |- is_true (negb _) ] => rewrite -> negE
  | [ |- is_true (implb _ _) ] => rewrite -> implE
  | [ |- is_true (eqb _ _) ] => rewrite -> iffE
  | [ |- is_true true ] => rewrite -> trueE
  | [ |- is_true false ] => rewrite -> falseE
  | [ |- _ ] => fail "'brefl' failed. Did you mean 'breflect'?"
  end.

Tactic Notation "brefl" "in" hyp(H) :=
  lazymatch type of H with
  | is_true (andb _ _) => rewrite -> andE in H
  | is_true (orb _ _) => rewrite -> orE in H
  | is_true (negb _) => rewrite -> negE in H
  | is_true (implb _ _) => rewrite -> implE in H
  | is_true (eqb _ _) => rewrite -> iffE in H
  | is_true true => try clear H
  | is_true false => discriminate H
  | _ => fail "'brefl' failed. Did you mean 'breflect'?"
  end.

Tactic Notation "breif" :=
  lazymatch goal with
  | [ |- _ /\ _ ] => rewrite <- andE
  | [ |- _ \/ _ ] => rewrite <- orE
  | [ |- ~ _ ] => rewrite <- negE
  | [ |- _ -> _ ] => rewrite <- implE
  | [ |- _ <-> _ ] => rewrite <- iffE
  | [ |- True ] => rewrite <- trueE
  | [ |- False ] => rewrite <- falseE
  | [ |- _ ] => fail "'breif' failed. Did you mean 'breify'?"
  end.

Tactic Notation "breif" "in" hyp(H) :=
  lazymatch type of H with
  | _ /\ _ => rewrite <- andE in H
  | _ \/ _ => rewrite <- orE in H
  | ~ _ => rewrite <- negE in H
  | _ -> _ => rewrite <- implE in H
  | _ <-> _ => rewrite <- iffE in H
  | True => try clear H
  | False => destruct H
  | _ => fail "'breif' failed. Did you mean 'breify'?"
  end.

(* boolean tactics *)

Tactic Notation "bdestr" constr(b) "as" ident(H) :=
  lazymatch type of b with
  | bool =>
    destruct b eqn:H;
    [ replace (b = true) with (is_true b) in H by reflexivity |
      let H1 := fresh "H" in
      assert (H1: is_true (negb b)) by (rewrite H; simpl; constructor);
      clear H; rename H1 into H ]
  | _ => fail "not a boolean term"
  end.

Tactic Notation "bdestr" constr(b) :=
  let H := fresh "H" in bdestr b as H.

Tactic Notation "bdestruct" constr(b) "as" ident(H) :=
  lazymatch b with
  | Z.eqb ?b1 ?b2 => destruct (Z.eqb_spec b1 b2) as [H|H]
  | Z.gtb ?b1 ?b2 => destruct (Z.gtb_spec b1 b2) as [H|H]
  | Z.geb ?b1 ?b2 => destruct (Z.geb_spec b1 b2) as [H|H]
  | Z.ltb ?b1 ?b2 => destruct (Z.ltb_spec b1 b2) as [H|H]
  | Z.leb ?b1 ?b2 => destruct (Z.leb_spec b1 b2) as [H|H]
  | N.eqb ?b1 ?b2 => destruct (N.eqb_spec b1 b2) as [H|H]
  | N.leb ?b1 ?b2 => destruct (N.leb_spec b1 b2) as [H|H]
  | N.ltb ?b1 ?b2 => destruct (N.ltb_spec b1 b2) as [H|H]
  | Nat.eqb ?b1 ?b2 => destruct (Nat.eqb_spec b1 b2) as [H|H]
  | Nat.leb ?b1 ?b2 => destruct (Nat.leb_spec b1 b2) as [H|H]
  | Nat.ltb ?b1 ?b2 => destruct (Nat.ltb_spec b1 b2) as [H|H]
  | _ => bdestr b as H; bsimpl in H; breflect in H
  end.

Tactic Notation "bdestruct" constr(b) :=
  let H := fresh "H" in bdestruct b as H.

Tactic Notation "binvert" constr(b) :=
  lazymatch type of b with
  | is_true (andb _ _) => move /andP: b; let H := fresh "H" in intro H; destruct H
  | is_true (orb _ _) => move /orP: b; let H := fresh "H" in intro H; destruct H
  | is_true true => try clear b
  | is_true false => discriminate b
  | _ => fail
  end.

Tactic Notation "binvert" constr(b) "as" simple_intropattern(pat) :=
  lazymatch type of b with
  | is_true (andb _ _) => move /andP: b; intros pat
  | is_true (orb _ _) => move /orP: b; intros pat
  | is_true true => try clear b
  | is_true false => discriminate b
  | _ => fail
  end.

Ltac bleft := apply /orP; left.
Ltac bright := apply /orP; right.
Ltac bsplit := apply /andP; split.
Ltac blia := bsimpl in *; breflect in *; lia.
Ltac bcongruence := breflect in *; congruence.
