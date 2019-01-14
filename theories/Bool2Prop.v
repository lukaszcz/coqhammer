Require Import Bool BinInt Nat.
(*From mathcomp Require Import all_ssreflect.*)

Infix "-->" := implb (at level 60, right associativity) : bool_scope.
Infix "<-->" := Bool.eqb (at level 60, right associativity) : bool_scope.
Local Coercion is_true : bool >-> Sortclass.


Lemma reflect_iff : forall P b, reflect P b -> (P<->b=true).
Proof.
 intros; destruct H; intuition.
 discriminate H.
Qed.

Lemma iff_reflect : forall P b, (P<->b=true) -> reflect P b.
Proof.
 intros.
 destr_bool; constructor; try now apply H.
 unfold not. intros. apply H in H0. destruct H. easy.
Qed.

Lemma reflect_dec : forall P b, reflect P b -> {P} + {~P}.
Proof. intros; destruct H; [now left | now right]. Qed.

 Lemma implyP : forall (b1 b2: bool), reflect (b1 -> b2) (b1 --> b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma iffP : forall (b1 b2: bool), reflect (b1 <-> b2) (Bool.eqb b1 b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma implyP2 : forall (b1 b2 b3: bool), reflect (b1 -> b2 -> b3) (b1 --> b2 --> b3).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma andP : forall (b1 b2: bool), reflect (b1 /\ b2) (b1 && b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma orP : forall (b1 b2: bool), reflect (b1 \/ b2) (b1 || b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *.
        destruct H1 as [H1a | H1b ]; easy. left. easy. left. easy.
        right. easy.
 Qed.

 Lemma negP : forall (b: bool), reflect (~ b) (negb b).
 Proof. intros; apply iff_reflect; split;
        case_eq b; intros; try easy; try compute in *.
        contradict H0. easy.
 Qed.

 Lemma eqP : forall (b1 b2: bool), reflect (b1 = b2) (Bool.eqb b1 b2).
 Proof. intros; apply iff_reflect; split;
        case_eq b1; case_eq b2; intros; try easy; try compute in *; now apply H1.
 Qed.

 Lemma FalseB : (false = true) <-> False.
 Proof. split; auto; try congruence. Qed.

 Lemma TrueB : (true = true) <-> True.
Proof. split; auto. Qed.

Lemma beq_eq: forall b1 b2, b1 <--> b2 <-> b1 = b2.
Proof. intros; case_eq b1; case_eq b2; intros; subst; try easy. Qed.

Lemma Z_eqb_eq: forall a b: Z, Z.eqb a b = true <-> a = b.
Proof. intros; now rewrite Z.eqb_eq. Qed.

Lemma Z_gtb_gt: forall a b: Z, Z.gtb a b = true <-> Z.gt a b.
Proof. split; intros. rewrite Z.gtb_lt in H. now apply Z.lt_gt in H.
       rewrite Z.gtb_lt. now apply Z.gt_lt in H.
Qed.

Lemma Z_geb_ge: forall a b: Z, Z.geb a b = true <-> Z.ge a b.
Proof. split; intros. rewrite Z.geb_le in H. now apply Z.le_ge in H.
       rewrite Z.geb_le. now apply Z.ge_le in H.
Qed.

Lemma Z_ltb_lt: forall a b: Z, Z.ltb a b = true <-> Z.lt a b.
Proof. split; intros. now rewrite Z.ltb_lt in H. now rewrite Z.ltb_lt.
Qed.

Lemma Z_leb_le: forall a b: Z, Z.leb a b = true <-> Z.le a b.
Proof. split; intros. now rewrite Z.leb_le in H. now rewrite Z.leb_le.
Qed.

Ltac prep :=
  repeat
    match goal with
    | [ |- context [ match ?A with _ => _ end ] ] =>
        match type of A with
          | bool       => case_eq A; let Ha := fresh "H" in intro Ha
          | comparison => case_eq A; let Ha := fresh "H" in intro Ha
          | _ => idtac
        end
    | [ |- context [ if ?b then _ else _ ] ] => case_eq b; let Ha := fresh "H" in intro Ha

    | [ H: context [ Bool.eqb ?G0 ?G1 ] |- _ ] => let Ha := fresh "H" in
                                                  let Hb := fresh "H" in unfold is_true in H;
       specialize (@iffP G0 G1); intro Ha; 
       apply reflect_iff in Ha; apply Ha in H; clear Ha
    | [ H: context [ ?G0 && ?G1  ] |- _ ] => let Ha := fresh "H" in
                                             let Hb := fresh "H" in unfold is_true in H;
       specialize (@andP G0 G1); intro Ha; apply reflect_iff in Ha; apply Ha in H; clear Ha;
       destruct H as (Ha, Hb)
    | [ H: context [ ?G0 --> ?G1 ] |- _ ] => let Ha := fresh "H" in
                                             let Hb := fresh "H" in unfold is_true in H;
       specialize (@implyP G0 G1); intro Ha; apply reflect_iff in Ha;
       (assert (Hb: G0 -> G1) by now apply Ha); clear Ha; clear H

    | [ H: context [ ?G0 || ?G1  ] |- _ ] => let Ha := fresh "H" in
                                             let Hb := fresh "H" in unfold is_true in H;
       specialize (@orP G0 G1); intro Ha; apply reflect_iff in Ha; apply Ha in H; clear Ha;
       destruct H as [Ha | Hb]
    | [ H: context [ ?G0 /\ ?G1  ] |- _ ] => let Ha := fresh "H" in
                                             let Hb := fresh "H" in destruct H as (Ha, Hb)
    | [ H: context [ ?G0 \/ ?G1  ] |- _ ] => let Ha := fresh "H" in
                                             let Hb := fresh "H" in destruct H as [Ha | Hb]
     end.

Ltac bool2prop :=
  repeat
    match goal with
    | [ H: context [ Z.eqb _ _]   |- _ ] => unfold is_true in H; rewrite Z_eqb_eq in H
    | [ H: context [ Z.geb _ _]   |- _ ] => unfold is_true in H; rewrite Z_geb_ge in H
    | [ H: context [ Z.gtb _ _]   |- _ ] => unfold is_true in H; rewrite Z_gtb_gt in H
    | [ H: context [ Z.ltb _ _]   |- _ ] => unfold is_true in H; rewrite Z_ltb_lt in H
    | [ H: context [ Z.leb _ _]   |- _ ] => unfold is_true in H; rewrite Z_leb_le in H
    | [ |- context[ Z.eqb _ _ ] ]  => unfold is_true; rewrite Z_eqb_eq
    | [ |- context[ Z.leb _ _ ] ]  => unfold is_true; rewrite Z.leb_le
    | [ |- context[ Z.ltb _ _ ] ]  => unfold is_true; rewrite Z.ltb_lt
    | [ |- context[ Z.gtb _ _ ] ]  => unfold is_true; rewrite Z_gtb_gt
    | [ |- context[ Z.geb _ _ ] ]  => unfold is_true; rewrite Z_geb_ge
    | [ |- context[?G0 --> ?G1 ] ] =>
        rewrite <- (@reflect_iff (G0 = true -> G1 = true)  (G0 --> G1)); 
      [ | apply implyP]
    | [ |- context[?G0 || ?G1 ] ] =>
        rewrite <- (@reflect_iff (G0 = true \/ G1 = true) (G0 || G1)); 
      [ | apply orP]
    | [ |- context[?G0 && ?G1 ] ] =>
        rewrite <- (@reflect_iff (G0 = true /\ G1 = true) (G0 && G1)); 
      [ | apply andP]
    | [ |- context[?G0 <--> ?G1 ] ] =>
        rewrite <- (@reflect_iff (G0 = true <-> G1 = true) (G0 <--> G1)); 
      [ | apply iffP]
    | [ |- context[ negb ?G ] ] =>
        rewrite <- (@reflect_iff (G <> true) (negb G)); 
      [ | apply negP]
    | [ |- context[ false = true ] ] => rewrite FalseB
    | [ |- context[ true = true ] ] => rewrite TrueB
  end.




