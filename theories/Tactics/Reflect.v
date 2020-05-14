(* Boolean reflection tactics *)
(* Authors: Burak Ekici, Lukasz Czajka *)

Coercion is_true : bool >-> Sortclass.

Require Export Bool.
Require Psatz.
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

Lemma eqE : forall b1 b2, eqb b1 b2 <-> (b1 = b2).
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

(* bool to Prop reflection *)

Create HintDb brefl_hints discriminated.

Hint Rewrite -> andE : brefl_hints.
Hint Rewrite -> orE : brefl_hints.
Hint Rewrite -> negE : brefl_hints.
Hint Rewrite -> implE : brefl_hints.
Hint Rewrite -> iffE : brefl_hints.
Hint Rewrite -> falseE : brefl_hints.
Hint Rewrite -> trueE : brefl_hints.

Hint Rewrite -> Z_eqb_eq : brefl_hints.
Hint Rewrite -> Z_gtb_gt : brefl_hints.
Hint Rewrite -> Z_geb_ge : brefl_hints.
Hint Rewrite -> Z_ltb_lt : brefl_hints.
Hint Rewrite -> Z_leb_le : brefl_hints.

Hint Rewrite -> N_eqb_eq : brefl_hints.
Hint Rewrite -> N_ltb_lt : brefl_hints.
Hint Rewrite -> N_leb_le : brefl_hints.

Hint Rewrite -> Nat_eqb_eq : brefl_hints.
Hint Rewrite -> Nat_ltb_lt : brefl_hints.
Hint Rewrite -> Nat_leb_le : brefl_hints.

Tactic Notation "breflect" :=
  unfold Nat.lt, Nat.le; autorewrite with brefl_hints.

Tactic Notation "breflect" "in" hyp(H) :=
  unfold Nat.lt, Nat.le in H; autorewrite with brefl_hints in H.

Tactic Notation "breflect" "in" "*" :=
  unfold Nat.lt, Nat.le in *; autorewrite with brefl_hints in *.

(* Prop to bool reflection *)

Create HintDb prefl_hints discriminated.

Hint Rewrite <- andE : prefl_hints.
Hint Rewrite <- orE : prefl_hints.
Hint Rewrite <- negE : prefl_hints.
Hint Rewrite <- implE : prefl_hints.
Hint Rewrite <- iffE : prefl_hints.
Hint Rewrite <- falseE : prefl_hints.
Hint Rewrite <- trueE : prefl_hints.

Hint Rewrite <- Z_eqb_eq : prefl_hints.
Hint Rewrite <- Z_gtb_gt : prefl_hints.
Hint Rewrite <- Z_geb_ge : prefl_hints.
Hint Rewrite <- Z_ltb_lt : prefl_hints.
Hint Rewrite <- Z_leb_le : prefl_hints.

Hint Rewrite <- N_eqb_eq : prefl_hints.
Hint Rewrite <- N_ltb_lt : prefl_hints.
Hint Rewrite <- N_leb_le : prefl_hints.

Hint Rewrite <- Nat_eqb_eq : prefl_hints.
Hint Rewrite <- Nat_ltb_lt : prefl_hints.
Hint Rewrite <- Nat_leb_le : prefl_hints.

Tactic Notation "preflect" :=
  unfold Nat.lt, Nat.le; autorewrite with prefl_hints.

Tactic Notation "preflect" "in" hyp(H) :=
  unfold Nat.lt, Nat.le in H; autorewrite with prefl_hints in H.

Tactic Notation "preflect" "in" "*" :=
  unfold Nat.lt, Nat.le in *; autorewrite with prefl_hints in *.

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
  end.

Tactic Notation "prefl" :=
  lazymatch goal with
  | [ |- _ /\ _ ] => rewrite <- andE
  | [ |- _ \/ _ ] => rewrite <- orE
  | [ |- ~ _ ] => rewrite <- negE
  | [ |- _ -> _ ] => rewrite <- implE
  | [ |- _ <-> _ ] => rewrite <- iffE
  | [ |- True ] => rewrite <- trueE
  | [ |- False ] => rewrite <- falseE
  end.

Tactic Notation "prefl" "in" hyp(H) :=
  lazymatch type of H with
  | _ /\ _ => rewrite <- andE in H
  | _ \/ _ => rewrite <- orE in H
  | ~ _ => rewrite <- negE in H
  | _ -> _ => rewrite <- implE in H
  | _ <-> _ => rewrite <- iffE in H
  | True => try clear H
  | False => destruct H
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
  | Z.gtb ?b1 ?b2 => destruct (Z.gtb_spec b1 b2) as [H|H]
  | Z.geb ?b1 ?b2 => destruct (Z.geb_spec b1 b2) as [H|H]
  | Z.ltb ?b1 ?b2 => destruct (Z.ltb_spec b1 b2) as [H|H]
  | Z.leb ?b1 ?b2 => destruct (Z.leb_spec b1 b2) as [H|H]
  | N.leb ?b1 ?b2 => destruct (N.leb_spec b1 b2) as [H|H]
  | N.ltb ?b1 ?b2 => destruct (N.ltb_spec b1 b2) as [H|H]
  | Nat.leb ?b1 ?b2 => destruct (Nat.leb_spec b1 b2) as [H|H]
  | Nat.ltb ?b1 ?b2 => destruct (Nat.ltb_spec b1 b2) as [H|H]
  | _ => bdestr b as H; breflect in H
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
Ltac blia := breflect in *; Psatz.lia.
Ltac bcongruence := breflect in *; congruence.
