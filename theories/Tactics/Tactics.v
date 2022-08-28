(* Coq >= 8.9 required *)
(* author: Lukasz Czajka *)
(* This file contains the Ltac part of the automated reasoning tactics. *)
(* This file may be distributed under the terms of the LGPL 2.1 license. *)

Declare ML Module "coq-hammer-tactics.lib".

Require Import Lia.
Require Import Program.Equality.
From Hammer Require Import Tactics.Reflect.

Create HintDb shints discriminated.

Ltac notHyp P :=
  match goal with
    | [ H : ?P1 |- _ ] => constr_eq P P1; fail 1
    | _ => idtac
  end.

Ltac noteHyp P :=
  match goal with
    | [ H : ?P1 |- _ ] => unify P P1; fail 1
    | _ => idtac
  end.

Ltac isProp t :=
  lazymatch type of t with
    | Prop => idtac
  end.

Ltac notProp t := tryif isProp t then fail else idtac.

Ltac notTrivial P :=
  lazymatch P with
    | True => fail
    | ?A = ?A => fail
    | ?A -> ?A => fail
    | ?A -> ?B = ?B => fail
    | _ => idtac
  end.

Ltac noEvars t := tryif has_evar t then fail else idtac.

Ltac seasy :=
  let rec use_hyp H :=
    match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | prod _ _ => exact H || destruct_hyp H
    | _ => try solve [ inversion H ]
    end
  with do_intro := let H := fresh in intro H; use_hyp H
  with destruct_hyp H := case H; clear H; do_intro; do_intro in
  let rec use_hyps :=
    match goal with
    | H : _ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H : prod _ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H : _ |- _ => solve [ inversion H ]
    | _ => idtac
    end
  in
  let do_atom :=
    solve [ trivial with eq_true | reflexivity | symmetry; trivial | contradiction ] in
  let rec do_ccl n :=
    try do_atom;
    repeat (do_intro; try do_atom);
    lazymatch n with
      | O => fail
      | S ?k =>
        solve [ split; do_ccl k ]
    end
  in
  solve [ do_atom | use_hyps; do_ccl 16 ] ||
  fail "Cannot solve this goal".

Ltac fullunfold h := unfold h in *.
Ltac fullunfold_all :=
  repeat match goal with
         | [ |- context[?c] ] => unfold c in *
         | [ H: context[?c] |- _ ] => unfold c in *
         end.

Ltac vinst e :=
  let tpe := type of e
  in
  lazymatch tpe with
  | ?T -> ?Q =>
    fail
  | forall x : ?T, _ =>
    let v := fresh "v" in
    evar (v : T);
    let v2 := eval unfold v in v in
    clear v;
    vinst (e v2)
  | _ =>
    generalize e
  end.

Ltac einst e :=
  let tpe := type of e
  in
  lazymatch tpe with
  | ?T -> ?Q =>
    generalize e
  | forall x : ?T, _ =>
    let v := fresh "v" in
    evar (v : T);
    let v2 := eval unfold v in v in
    clear v;
    einst (e v2)
  | _ =>
    generalize e
  end.

Ltac sdestruct t :=
  lazymatch t with
  | _ _ =>
    lazymatch type of t with
    | bool => bdestruct t
    | _ => destruct t eqn:?
    end
  | _ =>
    tryif is_evar t then
      lazymatch type of t with
      | bool => bdestruct t
      | _ => destruct t eqn:?
      end
    else
      (is_var t; destruct t)
  end.

Ltac dep_destruct t :=
  let X := fresh "X" in
  let H := fresh "H" in
  remember t as X eqn:H; simpl in X; dependent destruction X;
  try rewrite <- H in *; try clear H.

Ltac sdepdestruct t := sdestruct t || dep_destruct t.

Ltac ssubst := try subst.

Ltac subst_simpl := ssubst; simpl in *.

Ltac xintro x :=
  tryif intro x then
    idtac
  else
    let x1 := fresh x in
    intro x1.

Ltac sintro :=
  lazymatch goal with
  | [ |- ?T -> ?Q ] =>
      let H := fresh "H" in
      (tryif notHyp T then
          (intro H; try simp_hyp H)
        else
          (intro H; try clear H))
  | [ |- forall x : ?T, _ ] =>
      xintro x
  end

with simp_hyp H :=
  let tp := type of H in
  lazymatch tp with
    | True => clear H
    | (exists x, _) => elim H; clear H; xintro x; sintro
    | { x & _ } => elim H; clear H; xintro x; sintro
    | { x | _ } => elim H; clear H; xintro x; sintro
    | ?A = ?A => clear H
    | ?A -> ?A => clear H
    | ?A -> ?B = ?B => clear H
    | ?A /\ ?A => cut A; [ clear H; sintro | destruct H; assumption ]
    | ?A /\ ?B => elim H; clear H; sintro; sintro
    | prod ?A ?B =>
      let H1 := fresh H in
      let H2 := fresh H in
      destruct H as [ H1 H2 ];
      try simp_hyp H1;
      try simp_hyp H2
    | ?A /\ ?B -> ?C => cut (A -> B -> C);
                        [ clear H; sintro
                        | intro; intro; apply H; split; assumption ]
    | ?A = ?A -> ?B => cut B; [ clear H; sintro | apply H; reflexivity ]
    | ?A -> ?A -> ?B => cut (A -> B); [ clear H; sintro | intro; apply H; assumption ]
    | ?A \/ ?A => cut A; [ clear H; sintro | elim H; intro; assumption ]
    | ?A \/ ?B -> ?C =>
      cut (A -> C); [ cut (B -> C); [ clear H; sintro; sintro |
                                      intro; apply H; right; assumption ] |
                      intro; apply H; left; assumption ]
    | Some _ = Some _ => injection H; try clear H
    | ?F ?X = ?F ?Y =>
      (assert (X = Y); [ assumption | fail 1 ])
      || (injection H; try clear H;
          match goal with
          | [ |- _ = _ -> _ ] =>
            sintro; ssubst
          end)
    | ?F ?X ?U = ?F ?Y ?V =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   sintro; ssubst
                 end)
    | ?F ?X ?U ?A = ?F ?Y ?V ?B =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption |
                                           assert (A = B); [ assumption | fail 1 ] ]])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   sintro; ssubst
                 end)
    | existT _ _ _ = existT _ _ _ => inversion_clear H
    | forall x : ?T1, ?A /\ ?B =>
      cut (forall x : T1, A);
        [ cut (forall x : T1, B);
          [ clear H; sintro; sintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2), A);
        [ cut (forall (x : T1) (y : T2), B);
          [ clear H; sintro; sintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3), A);
        [ cut (forall (x : T1) (y : T2) (z : T3), B);
          [ clear H; sintro; sintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4), B);
          [ clear H; sintro; sintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), B);
          [ clear H; sintro; sintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6), B);
          [ clear H; sintro; sintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6) (w1 : ?T7), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6) (w1 : T7), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6) (w1 : T7), B);
          [ clear H; sintro; sintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6)
             (w1 : ?T7) (w2 : ?T8), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6)
                  (w1 : T7) (w2 : T8), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6)
                      (w1 : T7) (w2 : T8), B);
          [ clear H; sintro; sintro | apply H ]
        | apply H ]
    | forall x : ?T1, ?A /\ ?B -> ?C =>
      cut (forall x : T1, A -> B -> C);
        [ clear H; sintro | do 3 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2), A -> B -> C);
        [ clear H; sintro | do 4 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3), A -> B -> C);
        [ clear H; sintro | do 5 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A -> B -> C);
        [ clear H; sintro | do 6 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A -> B -> C);
        [ clear H; sintro | do 7 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1), ?A \/ ?B -> ?C =>
      cut (forall (x : T1), A -> C); [ cut (forall (x : T1), B -> C);
                                       [ clear H; sintro; sintro |
                                         do 2 intro; apply H with (x := x); right; assumption ] |
                                       do 2 intro; apply H with (x := x); left; assumption ]
    | forall (x : ?T1) (y : ?T2), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2), A -> C);
        [ cut (forall (x : T1) (y : T2), B -> C);
          [ clear H; sintro; sintro |
            do 3 intro; apply H with (x := x) (y := y); right; assumption ] |
          do 3 intro; apply H with (x := x) (y := y); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3), B -> C);
          [ clear H; sintro; sintro |
            do 4 intro; apply H with (x := x) (y := y) (z := z); right; assumption ] |
          do 4 intro; apply H with (x := x) (y := y) (z := z); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4), B -> C);
          [ clear H; sintro; sintro |
            do 5 intro; apply H with (x := x) (y := y) (z := z) (u := u); right; assumption ] |
          do 5 intro; apply H with (x := x) (y := y) (z := z) (u := u); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), B -> C);
          [ clear H; sintro; sintro |
            do 6 intro; apply H with (x := x) (y := y) (z := z) (u := u) (v := v);
            right; assumption ] |
          do 6 intro; apply H with (x := x) (y := y) (z := z) (u := u) (v := v);
          left; assumption ]
    | ?A -> ?B =>
      lazymatch goal with
        | [ H1 : A |- _ ] => cut B; [ clear H; sintro | apply H; exact H1 ]
      end
  end.

Ltac sintros :=
  repeat match goal with [ |- ?G ] => isAtom G; fail 1 | [ |- _ ] => sintro end.

Ltac intros_until_atom :=
  repeat match goal with [ |- ?G ] => isAtom G; fail 1 | [ |- _ ] => intro end.

Ltac simp_hyps :=
  unfold iff in *; unfold not in *;
  repeat match goal with
           | [ H2 : ?A -> ?B, H1 : ?A |- _ ] =>
             assert B by (apply H2; exact H1); clear H2
           | [ H1 : ?P, H2 : ?P |- _ ] =>
             isProp P; clear H2 || clear H1
           | [ H : _ |- _ ] =>
             simp_hyp H
         end.

Ltac esimp_hyps :=
  unfold iff in *; unfold not in *;
  repeat match goal with
         | [ H2 : ?A2 -> ?B, H1 : ?A1 |- _ ] =>
           unify A1 A2; notHyp B;
           assert B by (apply H2; exact H1); clear H2
         | [ H1 : ?P, H2 : ?P |- _ ] =>
           isProp P; clear H2 || clear H1
         | [ H : _ |- _ ] =>
           simp_hyp H
         end.

Ltac exsimpl := (* TODO: move to plugin *)
  match goal with
    | [ H : forall (x : ?T1), exists a, _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2), exists a, _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3), exists a, _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), exists a, _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), exists a, _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H; intro; intro
  end.

Ltac isplit := (* TODO: move to plugin *)
  match goal with
    | [ |- ?A /\ _ ] =>
      cut A; [ let H := fresh "H" in
               intro H; split; [ exact H | idtac ] | idtac ]
    | [ |- prod ?A _ ] =>
      cut A; [ let H := fresh "H" in
               intro H; split; [ exact H | idtac ] | idtac ]
    | [ H : _ \/ _ |- _ ] => elim H; clear H; intro
    | [ H : (?a +{ ?b }) |- _ ] => elim H; clear H; intro
    | [ H : ({ ?a }+{ ?b }) |- _ ] => elim H; clear H; intro
    | [ H : (?a + ?b) |- _ ] => elim H; clear H; intro
    | [ H : forall (x : ?T1), _ \/ _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2), _ \/ _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3), _ \/ _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), _ \/ _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), _ \/ _ |- _ ] =>
      vinst H; clear H; intro H; elim H; clear H
  end.

Ltac trysolve :=
  eauto 2 with shints; try solve [ constructor ];
  match goal with
  | [ |- ?t = ?u ] => try solve [ try subst; congruence 8 |
                                  match type of t with nat => lia | ZArith.BinInt.Z => lia end ]
  | [ |- ?t <> ?u ] => try solve [ try subst; congruence 8 |
                                   match type of t with nat => lia | ZArith.BinInt.Z => lia end ]
  | [ |- (?t = ?u) -> False ] => try solve [ intro; try subst; congruence 8 |
                                             match type of t with nat => lia | ZArith.BinInt.Z => lia end ]
  | [ |- False ] => try solve [ try subst; congruence 8 ]
  | [ |- ?t >= ?u ] => try solve [ lia ]
  | [ |- ?t <= ?u ] => try solve [ lia ]
  | [ |- ?t > ?u ] => try solve [ lia ]
  | [ |- ?t < ?u ] => try solve [ lia ]
  | _ => idtac
  end.

Ltac trysolve_nolia :=
  eauto 2 with shints; try solve [ constructor ];
  match goal with
  | [ |- ?t = ?u ] => try solve [ try subst; congruence 8 ]
  | [ |- ?t <> ?u ] => try solve [ try subst; congruence 8 ]
  | [ |- (?t = ?u) -> False ] => try solve [ intro; try subst; congruence 8 ]
  | [ |- False ] => try solve [ try subst; congruence 8 ]
  | _ => idtac
  end.

Ltac sfinal tac :=
  let simp := intros; simp_hyps; repeat exsimpl
  in
  let rec msolve n :=
      simp; repeat (progress isplit; guard numgoals < 20; simp);
      lazymatch goal with
        | [ H : False |- _ ] => elim H
        | _ =>
          lazymatch n with
          | 0 => solve [ tac ]
          | S ?m =>
            solve [ tac | left; msolve m | right; msolve m |
                    eexists; msolve m ]
                  (* TODO: move to plugin, generalize to applying
                     non-recursive constructors *)
          end
      end
  in
  msolve 6.

Ltac isolve := sfinal trysolve.
Ltac isolve_nolia := sfinal trysolve_nolia.

Ltac tryrsolve :=
  let solver tac :=
      lazymatch goal with
      | [ |- ?A = ?A ] => reflexivity
      | [ |- ?A = ?B ] => solve [ unify A B; reflexivity | tac ]
      end
  in
  auto 2 with shints; try subst; try congruence 16;
  match goal with
    | [ |- ?A _ = ?A _ ] => apply f_equal; try solver tryrsolve
    | [ |- ?A _ _ = ?A _ _ ] => apply f_equal2; try solver tryrsolve
    | [ |- ?A _ _ _ = ?A _ _ _ ] => apply f_equal3; try solver tryrsolve
    | [ |- ?A _ _ _ _ = ?A _ _ _ _ ] => apply f_equal4; try solver tryrsolve
    | [ |- ?A _ _ _ _ _ = ?A _ _ _ _ _ ] => apply f_equal5; try solver tryrsolve
  end.

Ltac rsolve :=
  let simp := intros; simp_hyps; repeat exsimpl
  in
  simp; repeat (progress isplit; guard numgoals < 10; simp);
  tryrsolve.

Ltac eqsolve :=
  match goal with
    | [ |- ?A = ?A ] => reflexivity
    | [ |- ?A = ?B ] => unify A B; reflexivity
    | [ |- ?A _ = ?A _ ] => apply f_equal; eqsolve
    | [ |- ?A _ _ = ?A _ _ ] => apply f_equal2; eqsolve
    | [ |- ?A _ _ _ = ?A _ _ _ ] => apply f_equal3; eqsolve
    | [ |- ?A _ _ _ _ = ?A _ _ _ _ ] => apply f_equal4; eqsolve
    | [ |- ?A _ _ _ _ _ = ?A _ _ _ _ _ ] => apply f_equal5; eqsolve
    | [ |- ?A = ?B ] => solve [ rsolve ]
  end.
(* TODO: move eqsolve and rsolve to plugin *)

Ltac rchange tp :=
  lazymatch goal with
  | [ |- tp ] => idtac
  | [ |- ?G1 = ?G2 ] =>
    match tp with
    | ?tp1 = ?tp2 =>
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      assert (H1 : G1 = tp1) by eqsolve;
      assert (H2 : G2 = tp2) by eqsolve;
      try rewrite H1; clear H1;
      try rewrite H2; clear H2
    | ?tp1 = ?tp2 =>
      symmetry;
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      assert (H1 : G1 = tp2) by eqsolve;
      assert (H2 : G2 = tp1) by eqsolve;
      try rewrite H1; clear H1;
      try rewrite H2; clear H2
    end
  | [ |- ?G ] =>
    let H := fresh "H" in
    assert (H : G = tp) by eqsolve;
    try rewrite H; clear H
  end.

Ltac sapply e :=
  let tpe := type of e
  in
  lazymatch tpe with
  | ?T -> ?Q =>
    let H := fresh "H" in
    assert (H : T); [ idtac | sapply (e H) ]
  | forall x : ?T, _ =>
    let v := fresh "v" in
    evar (v : T);
    let v2 := (eval unfold v in v) in
    clear v;
    sapply (e v2)
  | _ =>
    rchange tpe; exact e
  end.

Ltac dsolve := auto with shints; try seasy; try solve [ do 10 constructor ].

Ltac ssolve_gen tac :=
  (intuition (auto with shints)); try solve [ tac ]; try congruence 24;
  try seasy; try solve [ econstructor; tac ].
Ltac ssolve := ssolve_gen isolve.
Ltac ssolve_nolia := ssolve_gen isolve_nolia.

Ltac leaf_solve := solve [ isolve ].
Ltac simpl_solve := solve [ isolve ].
Ltac leaf_solve_nolia := solve [ isolve_nolia ].
Ltac simpl_solve_nolia := solve [ isolve_nolia ].

Ltac bnat_reflect :=
  repeat match goal with
         | [ H : true = false |- _ ] => inversion H
         | [ H : true = ?A |- _ ] =>
           notHyp (A = true);
           assert (A = true) by (symmetry; exact H);
           clear H
         | [ H : false = ?A |- _ ] =>
           notHyp (A = false);
           assert (A = false) by (symmetry; exact H);
           clear H
         | [ H : (Nat.eqb ?A ?B) = true |- _ ] =>
           notHyp (A = B);
           assert (A = B) by (rewrite Coq.Arith.PeanoNat.Nat.eqb_eq in H; apply H);
           try subst
         | [ H : (Nat.eqb ?A ?B) = false |- _ ] =>
           notHyp (A = B -> False);
           assert (A = B -> False) by
               (rewrite <- Coq.Arith.PeanoNat.Nat.eqb_eq; rewrite H; discriminate)
         | [ H : (Nat.leb ?A ?B) = true |- _ ] =>
           notHyp (A <= B);
           assert (A <= B) by (apply Coq.Arith.Compare_dec.leb_complete; apply H)
         | [ H : (Nat.leb ?A ?B) = false |- _ ] =>
           notHyp (B < A);
           assert (B < A) by (apply Coq.Arith.Compare_dec.leb_complete_conv; apply H)
         | [ H : (Nat.ltb ?A ?B) = true |- _ ] =>
           notHyp (A < B);
           assert (A < B) by (apply Coq.Arith.PeanoNat.Nat.ltb_lt; apply H)
         | [ H : (Nat.ltb ?A ?B) = false |- _ ] =>
           notHyp (B <= A);
           assert (B <= A) by (apply Coq.Arith.PeanoNat.Nat.ltb_ge; apply H)
         | [ H : (BinNat.N.eqb ?A ?B) = true |- _ ] =>
           notHyp (A = B);
           assert (A = B) by (apply Coq.NArith.BinNat.N.eqb_eq; apply H);
           try subst
         | [ H : (BinNat.N.eqb ?A ?B) = false |- _ ] =>
           notHyp (A = B -> False);
           assert (A = B -> False) by
               (rewrite <- Coq.NArith.BinNat.N.eqb_eq; rewrite H; discriminate)
         end.

Ltac bool_reflect := bsimpl in *; breflect in *.

Ltac invert_one_subgoal_nored_gen tac H :=
  let ty := type of H in
  tac H; [idtac]; clear H; notHyp ty; ssubst.

Ltac invert_one_subgoal_gen tac H := invert_one_subgoal_nored_gen tac H; simpl in *.

Ltac invert H := inversion H.

Ltac simple_invert H :=
  solve [ inversion H ] || invert_one_subgoal_gen invert H.
Ltac simple_invert_nored H :=
  solve [ inversion H ] || invert_one_subgoal_nored_gen invert H.
Ltac simple_invert_dep H :=
  solve [ depelim H ] || invert_one_subgoal_gen depelim H.
Ltac simple_invert_dep_nored H :=
  solve [ depelim H ] || invert_one_subgoal_nored_gen depelim H.

Ltac simple_inverting_gen tac :=
  repeat match goal with
         | [ H : ?P |- _ ] =>
           lazymatch P with
           | is_true _ => fail
           | _ => tac H
           end
         end.
Ltac simple_inverting := simple_inverting_gen simple_invert.
Ltac simple_inverting_nored := simple_inverting_gen simple_invert_nored.
Ltac simple_inverting_dep := simple_inverting_gen simple_invert_dep.
Ltac simple_inverting_dep_nored := simple_inverting_gen simple_invert_dep_nored.

Ltac case_split :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => sdestruct X
  | [ H : context[match ?X with _ => _ end] |- _ ] => sdestruct X
  end.

Ltac case_split_dep :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => sdepdestruct X
  | [ H : context[match ?X with _ => _ end] |- _ ] => sdepdestruct X
  end.

Ltac case_splitting := repeat (case_split; ssubst; simpl in *).
Ltac case_splitting_nored := repeat (case_split; ssubst).

Ltac case_splitting_dep := repeat (case_split_dep; ssubst; simpl in *).
Ltac case_splitting_dep_nored := repeat (case_split_dep; ssubst).

Ltac case_split_concl :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => sdestruct X
  end.

Ltac case_split_concl_dep :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => sdepdestruct X
  end.

Ltac case_splitting_concl := repeat (case_split_concl; ssubst; simpl).
Ltac case_splitting_concl_nored := repeat (case_split_concl; ssubst).

Ltac case_splitting_concl_dep := repeat (case_split_concl_dep; ssubst; simpl).
Ltac case_splitting_concl_dep_nored := repeat (case_split_concl_dep; ssubst).

Ltac case_split_on_gen tac ind :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] =>
    tryif constr_eq ltac:(type of X) ind then tac X else fail
  | [ H : context[match ?X with _ => _ end] |- _ ] =>
    tryif constr_eq ltac:(type of X) ind then tac X else fail
  end.

Ltac case_split_on ind := case_split_on_gen sdestruct ind.
Ltac case_split_on_dep ind := case_split_on_gen sdepdestruct ind.

Ltac case_splitting_on t := repeat (case_split_on t; ssubst; simpl in *).
Ltac case_splitting_on_nored t := repeat (case_split_on t; ssubst).

Ltac case_splitting_on_dep t := repeat (case_split_on_dep t; ssubst; simpl in *).
Ltac case_splitting_on_dep_nored t := repeat (case_split_on_dep t; ssubst).

Ltac case_split_concl_on_gen tac ind :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] =>
    tryif constr_eq ltac:(type of X) ind then tac X else fail
  end.

Ltac case_split_concl_on ind := case_split_concl_on_gen sdestruct ind.
Ltac case_split_concl_on_dep ind := case_split_concl_on_gen sdepdestruct ind.

Ltac case_splitting_concl_on t := repeat (case_split_concl_on t; ssubst; simpl).
Ltac case_splitting_concl_on_nored t := repeat (case_split_concl_on t; ssubst).

Ltac case_splitting_concl_on_dep t := repeat (case_split_concl_on_dep t; ssubst; simpl).
Ltac case_splitting_concl_on_dep_nored t := repeat (case_split_concl_on_dep t; ssubst).

Ltac generalizing :=
  repeat match goal with
           | [ H : _ |- _ ] => generalize H; clear H
         end.

Ltac fsolve := solve [ eassumption | symmetry; eassumption | econstructor ].

Ltac full_inst e tac :=
  let tpe := type of e
  in
  lazymatch tpe with
  | ?T -> ?Q =>
    cut T; [
      let H := fresh "H" in
      intro H; full_inst (e H) tac; clear H
    | try fsolve ]
  | forall x : ?T, _ =>
    let v := fresh "v" in
    evar (v : T);
    let v2 := (eval unfold v in v) in
    clear v;
    full_inst (e v2) tac;
    try match goal with
        | [ y : T |- _ ] => unify y v2
        end
  | _ =>
    generalize e; tac tt; try fsolve
  end.

Ltac sinv_gen dep H :=
  lazymatch dep with
  | true => depelim H
  | false => inversion H
  end; ssubst.

Ltac sdestr_gen dep H :=
  let ty := type of H in
  tryif isIndexedInd ty then
    lazymatch dep with
    | true => depelim H
    | false => dependent inversion H
    end; ssubst
  else
    destruct H.

Ltac sinvert_gen dep H :=
  let intro_invert tt :=
    let H1 := fresh "H" in
    intro H1; sinv_gen dep H1; try clear H1
  in
  lazymatch type of H with
  | _ -> _ =>
    full_inst H intro_invert
  | _ =>
    lazymatch goal with
    | [ |- context[H] ] => sdestr_gen dep H
    | [ |- _ ] =>
      let ty := type of H in
      sinv_gen dep H; tryif clear H then notHyp ty else idtac
    end
  end.

Ltac sinvert H := sinvert_gen false H.
Ltac sdepinvert H := sinvert_gen true H.

Ltac full_einst e tac :=
  let tpe := type of e
  in
  lazymatch tpe with
  | ?T -> ?Q =>
    cut T; [
      let H := fresh "H" in
      intro H; full_einst (e H) tac; clear H
    | try fsolve ]
  | forall x : ?T, _ =>
    let v := fresh "v" in
    evar (v : T);
    let v2 := (eval unfold v in v) in
    clear v;
    full_einst (e v2) tac
  | _ =>
    generalize e; tac tt; try fsolve
  end.

Ltac seinvert_gen dep H :=
  let intro_invert tt :=
    let H1 := fresh "H" in
    intro H1; sinv_gen dep H1; try clear H1
  in
  lazymatch type of H with
  | _ -> _ =>
    full_einst H intro_invert
  | _ =>
    lazymatch goal with
    | [ |- context[H] ] => sdestr_gen dep H
    | [ |- _ ] =>
      let ty := type of H in
      sinv_gen dep H; tryif clear H then noteHyp ty else idtac
    end
  end.

Ltac seinvert H := seinvert_gen false H.
Ltac sedepinvert H := seinvert_gen true H.

Definition rdone {T : Type} (x : T) := True.

Ltac un_done :=
  repeat match goal with
         | [ H : rdone _ |- _ ] => clear H
         end.

Ltac impl_fwd e :=
  match type of e with
  | ?T -> ?Q =>
    impl_fwd (e ltac:(fsolve))
  | _ =>
    generalize e
  end.

Ltac forward_base tac e :=
  lazymatch type of e with
  | ?P -> ?Q => fail
  | _ =>
    let rec fwd e :=
        lazymatch type of e with
        | ?P -> ?Q =>
          impl_fwd (e (ltac:(fsolve)))
        | forall x : ?T, _ =>
          let v := fresh "v" in
          evar (v : T);
          let v2 := (eval unfold v in v) in
          clear v;
          fwd (e v2);
          try match goal with
              | [ y : T |- _ ] => unify y v2
              end
        end
    in
    fwd e; tac;
    match goal with
    | [ |- ?P -> _ ] =>
      notTrivial P; noEvars P; notHyp P;
      let H := fresh "H" in
      intro H; move H at top
    end
  end.

Ltac forward H := forward_base ltac:(simpl) H.
Ltac forward_nored H := forward_base ltac:(idtac) H.

Ltac forwarding :=
  repeat match goal with
         | [ H : forall x : _,_ |- _ ] => forward H
         end.

Ltac forwarding_nored :=
  repeat match goal with
         | [ H : forall x : _,_ |- _ ] => forward_nored H
         end.

Ltac inList x lst :=
  lazymatch lst with
  | (?t, ?y) => tryif constr_eq x y then idtac else inList x t
  | x => idtac
  | _ => fail
  end.

Ltac notInList x lst := tryif inList x lst then fail else idtac.

Ltac all f ls :=
  match ls with
  | (?LS, ?X) => f X; all f LS
  | (_, _) => fail 1
  | _ => f ls
  end.

Ltac lst_rev lst :=
  let rec hlp lst acc :=
      match lst with
      | tt => acc
      | (?t, ?h) => hlp t (acc, h)
      | ?x => constr:((acc, x))
      end
  in
  hlp lst tt.

Ltac with_hyps p f :=
  let rec hlp acc :=
      match goal with
      | [ H : ?P |- _ ] =>
        p P; notInList H acc; hlp (acc, H)
      | _ =>
        f ltac:(lst_rev acc)
      end
  in
  hlp tt.

Ltac with_prop_hyps := with_hyps isProp.
Ltac all_hyps f := with_hyps ltac:(fun _ => idtac) ltac:(all f).
Ltac all_prop_hyps f := with_prop_hyps ltac:(all f).

Ltac qforward H :=
  lazymatch type of H with
  | ?P -> ?Q => fail
  | _ =>
    einst H;
    progress repeat match goal with
                    | [ H0 : ?P |- (?Q -> _) -> _ ] =>
                      unify P Q;
                      let H1 := fresh "H" in
                      intro H1; generalize (H1 H0); clear H1
                    end;
    match goal with
    | [ |- ?P -> _ ] => notTrivial P; noEvars P; notHyp P
    end;
    intro
  end.

Ltac qforwarding :=
  all_hyps ltac:(fun H => try qforward H).

Tactic Notation "forward_reasoning" int_or_var(n) := do n qforwarding.

Ltac inster0 e trace :=
  match type of e with
  | forall x : ?T, _ =>
    match goal with
    | [ H : _ |- _ ] =>
      inster0 (e H) (trace, H)
    | _ =>
      isProp T;
      let H := fresh "H" in
      assert (H: T) by isolve;
      inster0 (e H) (trace, H)
    | _ => fail 2
    end
  | _ =>
    match trace with
    | (_, _) =>
      match goal with
      | [ H : rdone (trace, _) |- _ ] =>
        fail 1
      | _ =>
        let T := type of e in
        lazymatch type of T with
        | Prop =>
          notHyp T; generalize e; intro;
          assert (rdone (trace, tt)) by constructor
        | _ =>
          all ltac:(fun X =>
                      match goal with
                      | [ H : rdone (_, X) |- _ ] => fail 1
                      | _ => idtac
                      end) trace;
          let i := fresh "i" in
          pose (i := e); assert (rdone (trace, i)) by constructor
        end
      end
    end
  end.

Ltac inster H := inster0 H H.

Ltac instering :=
  repeat match goal with
         | [ H : ?T |- _ ] => isProp T; inster H
         end;
  un_done.

Ltac einster e :=
  let tpe := type of e
  in
  lazymatch tpe with
  | ?T -> ?Q =>
    let H := fresh "H" in
    tryif (assert (H : T) by isolve) then
      einster (e H); clear H
    else
      noteHyp tpe; generalize e; intro
  | forall x : ?T, _ =>
    let v := fresh "v" in
    evar (v : T);
    let v2 := (eval unfold v in v) in
    clear v;
    einster (e v2)
  | _ =>
    noteHyp tpe; generalize e; intro
  end.

Ltac einstering :=
  repeat match goal with
         | [ H : ?P |- _ ] => isProp P; einster H
         end.

Ltac srewrite H := (erewrite H in * by isolve_nolia) || (erewrite <- H in * by isolve_nolia).
Ltac srewrite_in_concl H := (erewrite H by isolve_nolia) || (erewrite <- H by isolve_nolia).

Ltac srewriting :=
  repeat match goal with
         | [ H : ?T |- _ ] => checkTargetLPO T; erewrite H in * by isolve_nolia
         | [ H : ?T |- _ ] => checkTargetRevLPO T; erewrite <- H in * by isolve_nolia
         end.

Ltac red_in_all := simpl in *.
Ltac red_in_concl := simpl.

Ltac destruct_sigma_in_goal :=
  repeat match goal with
         | [ |- context[proj1_sig ?X] ] =>
           destruct X; simpl
         end.

Ltac destruct_sigma :=
  repeat match goal with
         | [H : context[proj1_sig ?X] |- _] =>
           destruct X; simpl in *
         | [ |- context[proj1_sig ?X] ] =>
           destruct X; simpl in *

         end.

Ltac destruct_sigma_dep_in_goal :=
  repeat match goal with
         | [ |- context[proj1_sig ?X] ] =>
           dep_destruct X; simpl
         end.

Ltac destruct_sigma_dep :=
  repeat match goal with
         | [H : context[proj1_sig ?X] |- _] =>
           dep_destruct X; simpl in *
         | [ |- context[proj1_sig ?X] ] =>
           dep_destruct X; simpl in *
         end.

Ltac invert_sigma :=
  repeat match goal with
         | [ H: exist _ _ _ = exist _ _ _ |- _ ] =>
           induction H using eq_sig_rect; ssubst; simpl in *
         | [ H: existT _ _ _ = existT _ _ _ |- _ ] =>
           induction H using eq_sigT_rect; ssubst; simpl in *
         end.

Ltac simpl_sigma := invert_sigma; destruct_sigma.

Ltac unfold_local_defs :=
  repeat match goal with
         | [f := _ |- _] => unfold f in *; try clear f
         end.

Ltac generalize_proofs_in t :=
  lazymatch t with
  | ?X ?Y =>
    (tryif is_var Y then
        idtac
      else
        let ty := type of Y in
        lazymatch type of ty with
        | Prop => try generalize Y
        | _ => generalize_proofs_in Y
        end);
    generalize_proofs_in X
  | ?X -> ?Y =>
    generalize_proofs_in X;
    generalize_proofs_in Y
  | _ =>
    idtac
  end.

Ltac generalize_proofs_in_goal :=
  match goal with
  | [|- ?G] => generalize_proofs_in G
  end.

Ltac generalize_proofs_in_hyp H :=
  let T := type of H in
  try (revert H; progress generalize_proofs_in T).

Ltac generalize_proofs :=
  generalize_proofs_in_goal;
  repeat match goal with
         | [H: ?T |- _] => revert H; progress generalize_proofs_in T
         end.

Tactic Notation "generalize" "proofs" := generalize_proofs_in_goal.
Tactic Notation "generalize" "proofs" "in" ident(H) := generalize_proofs_in_hyp H.
Tactic Notation "generalize" "proofs" "in" "*" := generalize_proofs.

Ltac use_tac :=
  let H := fresh "H" in intro H; try move H at top; try simp_hyp H.

Ltac congr_tac := congruence 400.
Ltac lia_tac := lia.
Ltac f_equal_tac := f_equal.
Ltac firstorder_tac := solve [ firstorder (trysolve; auto) ].
Ltac firstorder_nolia_tac := solve [ firstorder (trysolve_nolia; auto) ].

Declare ML Module "coq-hammer-tactics.tactics".

Ltac sauto_tac := sauto.
Ltac sdone_tac := solve [ trysolve ].
Ltac sdone_nolia_tac := solve [ trysolve_nolia ].

Tactic Notation "sdone" := sdone_tac.
Tactic Notation "sdone" "lia:" "on" := sdone_tac.
Tactic Notation "sdone" "lia:" "off" := sdone_nolia_tac.
