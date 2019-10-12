(* Coq v8.9 required *)
(* author: Lukasz Czajka *)
(* This file contains reconstruction tactics for CoqHammer. *)
(* Copyright (c) 2017-2019, Lukasz Czajka and Cezary Kaliszyk, University of Innsbruck *)
(* This file may be distributed under the terms of the LGPL 2.1 license. *)

Declare ML Module "hammer_lib".

Require List Arith ZArith Bool Psatz.

Create HintDb shints discriminated.

Hint Rewrite -> Arith.PeanoNat.Nat.add_0_r : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.sub_0_r : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_0_r : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_1_r : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.add_assoc : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_assoc : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_add_distr_r : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_add_distr_l : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_sub_distr_r : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_sub_distr_l : shints.
Hint Rewrite -> Arith.PeanoNat.Nat.sub_add_distr : shints.
Hint Rewrite -> ZArith.BinInt.Z.add_0_r : shints.
Hint Rewrite -> ZArith.BinInt.Z.sub_0_r : shints.
Hint Rewrite -> ZArith.BinInt.Z.mul_0_r : shints.
Hint Rewrite -> ZArith.BinInt.Z.mul_1_r : shints.
Hint Rewrite -> ZArith.BinInt.Z.add_assoc : shints.
Hint Rewrite -> ZArith.BinInt.Z.mul_assoc : shints.
Hint Rewrite -> ZArith.BinInt.Z.mul_add_distr_r : shints.
Hint Rewrite -> ZArith.BinInt.Z.mul_add_distr_l : shints.
Hint Rewrite -> ZArith.BinInt.Z.mul_sub_distr_r : shints.
Hint Rewrite -> ZArith.BinInt.Z.mul_sub_distr_l : shints.
Hint Rewrite -> ZArith.BinInt.Z.sub_add_distr : shints.
Hint Rewrite -> List.in_app_iff : shints.
Hint Rewrite -> List.in_map_iff : shints.
Hint Rewrite -> List.in_inv : shints.
Hint Rewrite <- List.app_assoc : shints.
Hint Rewrite -> Bool.orb_true_r : shints.
Hint Rewrite -> Bool.orb_true_l : shints.
Hint Rewrite -> Bool.orb_false_r : shints.
Hint Rewrite -> Bool.orb_false_l : shints.
Hint Rewrite -> Bool.andb_true_r : shints.
Hint Rewrite -> Bool.andb_true_l : shints.
Hint Rewrite -> Bool.andb_false_r : shints.
Hint Rewrite -> Bool.andb_false_l : shints.

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

Ltac tryunfold x :=
  let t := eval unfold x in x in
  lazymatch t with
    | _ _ => unfold x in *
    | (fun x => _ _) => unfold x in *
    | (fun x y => _ _) => unfold x in *
    | (fun x y z => _ _) => unfold x in *
    | (fun x y z u => _ _) => unfold x in *
    | (fun x y z u w => _ _) => unfold x in *
    | (fun x y z u w v => _ _) => unfold x in *
    | (forall s, _) => unfold x in *
    | (fun x => forall s, _) => unfold x in *
    | (fun x y => forall s, _) => unfold x in *
    | (fun x y z => forall s, _) => unfold x in *
    | (fun x y z u => forall s, _) => unfold x in *
    | (fun x y z u w => forall s, _) => unfold x in *
    | (fun x y z u w v => forall s, _) => unfold x in *
    | _ => idtac
  end.

Ltac fullunfold h := unfold h in *.

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
    | _ _ => destruct t eqn:?
    | _ =>
      tryif is_evar t then
         destruct t eqn:?
      else
        (is_var t; destruct t)
  end.

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
            sintro; try subst
          end)
    | ?F ?X ?U = ?F ?Y ?V =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   sintro; try subst
                 end)
    | ?F ?X ?U ?A = ?F ?Y ?V ?B =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption |
                                           assert (A = B); [ assumption | fail 1 ] ]])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   sintro; try subst
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
             clear H2 || clear H1
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
           clear H2 || clear H1
         | [ H : _ |- _ ] =>
           simp_hyp H
         end.

Ltac exsimpl := (* TODO: move to plugin *)
  match goal with
    | [ H : forall (x : ?T1), exists a, _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2), exists a, _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3), exists a, _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), exists a, _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), exists a, _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H; intro; intro
  end.

Ltac isplit :=
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
    | [ |- context[match ?X with _ => _ end] ] => sdestruct X
    | [ H : context[match ?X with _ => _ end] |- _ ] => sdestruct X
    | [ H : forall (x : ?T1), _ \/ _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2), _ \/ _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3), _ \/ _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), _ \/ _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), _ \/ _ |- _ ] =>
      einst H; clear H; intro H; elim H; clear H
  end.

Ltac trysolve :=
  eauto 2 with shints; try solve [ constructor ]; try subst;
  match goal with
  | [ |- ?t = ?u ] => try solve [ cbn in *; congruence 8 |
                                  match type of t with nat => Psatz.lia | ZArith.BinInt.Z => Psatz.lia end ]
  | [ |- ?t <> ?u ] => try solve [ cbn in *; congruence 8 |
                                   match type of t with nat => Psatz.lia | ZArith.BinInt.Z => Psatz.lia end ]
  | [ |- False ] => try solve [ cbn in *; congruence 8 ]
  | [ |- ?t >= ?u ] => try solve [ Psatz.lia ]
  | [ |- ?t <= ?u ] => try solve [ Psatz.lia ]
  | [ |- ?t > ?u ] => try solve [ Psatz.lia ]
  | [ |- ?t < ?u ] => try solve [ Psatz.lia ]
  | _ => idtac
  end.

Ltac isolve :=
  let simp := intros; simp_hyps; repeat exsimpl
  in
  let rec msolve :=
      simp; repeat (progress isplit; simp);
      lazymatch goal with
        | [ H : False |- _ ] => elim H
        | _ =>
          solve [ trysolve | left; msolve | right; msolve |
                  eexists; msolve ]
      end
  in
  msolve.

Ltac dsolve := auto with shints; try seasy; try solve [ do 10 constructor ].

Ltac ssolve := (intuition (auto with shints)); try solve [ isolve ]; try congruence 32; try seasy;
               try solve [ econstructor; isolve ].

Ltac sintuition := cbn; intros; simp_hyps; ssolve; repeat (progress (intros; simp_hyps); ssolve).

Ltac strivial := solve [ unfold iff in *; unfold not in *; unshelve isolve; dsolve ].

Ltac leaf_solve := solve [ isolve ].
Ltac simpl_solve := solve [ isolve ].

Ltac bnat_reflect :=
  repeat match goal with
         | [ H : (Nat.eqb ?A ?B) = true |- _ ] =>
           notHyp (A = B);
           assert (A = B) by (pose Arith.PeanoNat.Nat.eqb_eq; strivial);
           try subst
         | [ H : (Nat.eqb ?A ?B) = false |- _ ] =>
           notHyp (A = B -> False);
           assert (A = B -> False) by (pose Arith.PeanoNat.Nat.eqb_neq; strivial)
         | [ H : (Nat.leb ?A ?B) = true |- _ ] =>
           notHyp (A <= B);
           assert (A <= B) by (eauto using Arith.Compare_dec.leb_complete)
         | [ H : (Nat.leb ?A ?B) = false |- _ ] =>
           notHyp (B < A);
           assert (B < A) by (eauto using Arith.Compare_dec.leb_complete_conv)
         | [ H : (Nat.ltb ?A ?B) = true |- _ ] =>
           notHyp (A < B);
           assert (A < B) by (pose Arith.PeanoNat.Nat.ltb_lt; strivial)
         | [ H : (Nat.ltb ?A ?B) = false |- _ ] =>
           notHyp (B <= A);
           assert (B <= A) by (pose Arith.PeanoNat.Nat.ltb_ge; strivial)
         end.

Ltac ssubst :=
  try subst;
  repeat match goal with
         | [ H : ?A = ?B |- _ ] => is_var A; rewrite H in *; clear H
         end.

Ltac subst_simpl := ssubst; cbn in *.

Ltac invert_one_subgoal H :=
  let ty := type of H in
  inversion H; [idtac]; clear H; notHyp ty; subst_simpl.

Ltac simple_invert H := solve [ inversion H ] || invert_one_subgoal H.
Ltac simple_inverting :=
  repeat match goal with
         | [ H : ?P |- _ ] => simple_invert H
         end.

Ltac case_split :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => sdestruct X
  | [ H : context[match ?X with _ => _ end] |- _ ] => sdestruct X
  end.

Ltac case_splitting := repeat (case_split; subst_simpl).

Ltac generalizing :=
  repeat match goal with
           | [ H : _ |- _ ] => generalize H; clear H
         end.

Ltac fsolve := solve [ eassumption | symmetry; eassumption | econstructor ].

Ltac full_inst e :=
  let tpe := type of e
  in
  lazymatch tpe with
    | ?T -> ?Q =>
      let H := fresh "H" in
      assert (H : T); [ try fsolve | full_inst (e H); clear H ]
    | forall x : ?T, _ =>
      let v := fresh "v" in
      evar (v : T);
      let v2 := eval unfold v in v in
      clear v;
      full_inst (e v2);
      try match goal with
          | [ y : T |- _ ] => unify y v2
          end
    | _ =>
      generalize e
  end.

Ltac sinvert H :=
  lazymatch type of H with
  | _ -> _ =>
    full_inst H;
    let H1 := fresh "H" in
    intro H1; inversion H1; try subst; try clear H1
  | _ =>
    lazymatch goal with
    | [ |- context[H] ] => destruct H
    | [ |- _ ] => inversion H; try subst; try clear H
    end
  end; cbn.

Ltac einster e tac :=
  let tpe := type of e
  in
  lazymatch tpe with
    | ?T -> ?Q =>
      let H := fresh "H" in
      tryif (assert (H : T) by tac) then
        einster (e H) tac; clear H
      else
        generalize e
    | forall x : ?T, _ =>
      let v := fresh "v" in
      evar (v : T);
      let v2 := eval unfold v in v in
      clear v;
      einster (e v2) tac;
      try match goal with
          | [ y : T |- _ ] => unify y v2
          end
    | _ =>
      generalize e
  end.

Ltac forward e :=
  lazymatch type of e with
  | ?P -> ?Q => fail
  | _ =>
    let rec fwd e :=
        lazymatch type of e with
        | ?P -> ?Q =>
          let H := fresh "H" in
          assert (H : P) by fsolve;
          einster (e H) fsolve;
          clear H
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
    fwd e; cbn;
    match goal with
    | [ |- ?P -> _ ] =>
      noEvars P; notHyp P;
      let H := fresh "H" in intro H; move H at top
    end
  end.

Ltac forwarding :=
  repeat match goal with
         | [ H : forall x : _,_ |- _ ] => forward H
         end.

Definition default := tt.
Definition none := tt.
Definition hints := tt.
Definition nohints := tt.
Definition logic := tt.

Declare ML Module "hammer_tactics".

Tactic Notation "sauto" := unshelve sauto_gen; dsolve.
Tactic Notation "sauto" int_or_var(i) :=
  unshelve (sauto_gen i with shints using default unfolding default inverting default ctrs default opts default); dsolve.
Tactic Notation "sauto" "using" constr(lst) :=
  unshelve (sauto_gen with shints using lst unfolding default inverting default ctrs default opts default); dsolve.
Tactic Notation "sauto" int_or_var(i) "using" constr(lst) :=
  unshelve (sauto_gen i with shints using lst unfolding default inverting default ctrs default opts default); dsolve.
Tactic Notation "sauto" "using" constr(lst) "unfolding" constr(unfolds) :=
  unshelve (sauto_gen with shints using lst unfolding unfolds inverting default ctrs default opts default); dsolve.
Tactic Notation "sauto" int_or_var(i) "using" constr(lst) "unfolding" constr(unfolds) :=
  unshelve (sauto_gen i with shints using lst unfolding unfolds inverting default ctrs default opts default); dsolve.
Tactic Notation "sauto" "unfolding" constr(unfolds) :=
  unshelve (sauto_gen with shints using default unfolding unfolds inverting default ctrs default opts default); dsolve.
Tactic Notation "sauto" int_or_var(i) "unfolding" constr(unfolds) :=
  unshelve (sauto_gen i with shints using default unfolding unfolds inverting default ctrs default opts default); dsolve.
Tactic Notation "sauto" "inverting" constr(inverts) :=
  unshelve (sauto_gen with shints using default unfolding default inverting inverts ctrs default opts default); dsolve.
Tactic Notation "sauto" int_or_var(i) "inverting" constr(inverts) :=
  unshelve (sauto_gen i with shints using default unfolding default inverting inverts ctrs default opts default); dsolve.
Tactic Notation "sauto" "using" constr(lst) "inverting" constr(inverts) :=
  unshelve (sauto_gen with shints using lst unfolding default inverting inverts ctrs default opts default); dsolve.
Tactic Notation "sauto" int_or_var(i) "using" constr(lst) "inverting" constr(inverts) :=
  unshelve (sauto_gen i with shints using lst unfolding default inverting inverts ctrs default opts default); dsolve.
Tactic Notation "sauto" "using" constr(lst) "unfolding" constr(unfolds) "inverting" constr(inverts) :=
  unshelve (sauto_gen with shints using lst unfolding unfolds inverting inverts ctrs default opts default); dsolve.
Tactic Notation "sauto" int_or_var(i) "using" constr(lst) "unfolding" constr(unfolds) "inverting" constr(inverts) :=
  unshelve (sauto_gen i with shints using lst unfolding unfolds inverting inverts ctrs default opts default); dsolve.
Tactic Notation "sauto" "unfolding" constr(unfolds) "inverting" constr(inverts) :=
  unshelve (sauto_gen with shints using default unfolding unfolds inverting inverts ctrs default opts default); dsolve.
Tactic Notation "sauto" int_or_var(i) "unfolding" constr(unfolds) "inverting" constr(inverts) :=
  unshelve (sauto_gen i with shints using default unfolding unfolds inverting inverts ctrs default opts default); dsolve.

Tactic Notation "ssimpl" := unshelve ssimpl_gen; dsolve.
Tactic Notation "ssimpl" "unfolding" constr(unfolds) := unshelve ssimpl_gen unfolding unfolds; dsolve.

Tactic Notation "scrush" := try strivial; ssimpl; sauto.
Tactic Notation "scrush" "using" constr(lst) :=
  pose proof lst; try strivial; ssimpl; sauto.
Tactic Notation "scrush" "using" constr(lst) "unfolding" constr(unfolds) :=
  pose proof lst; try strivial; ssimpl unfolding unfolds; sauto unfolding unfolds.
Tactic Notation "scrush" "unfolding" constr(unfolds) :=
  try strivial; ssimpl unfolding unfolds; sauto unfolding unfolds.

Tactic Notation "hauto" :=
  unshelve (sauto_gen with nohints using default unfolding logic inverting logic ctrs logic opts noinvert); dsolve.
Tactic Notation "hauto" int_or_var(i) :=
  unshelve (sauto_gen i with nohints using default unfolding logic inverting logic ctrs logic opts noinvert); dsolve.
Tactic Notation "hauto" "using" constr(lst1) "unfolding" constr(lst2) :=
  unshelve (sauto_gen with nohints using lst1 unfolding lst2 inverting logic ctrs logic opts noinvert); dsolve.
Tactic Notation "hauto" int_or_var(i) "using" constr(lst1) "unfolding" constr(lst2) :=
  unshelve (sauto_gen i with nohints using lst1 unfolding lst2 inverting logic ctrs logic opts noinvert); dsolve.
Tactic Notation "hauto" "using" constr(lst1) :=
  unshelve (sauto_gen with nohints using lst1 unfolding logic inverting logic ctrs logic opts noinvert); dsolve.
Tactic Notation "hauto" int_or_var(i) "using" constr(lst1) :=
  unshelve (sauto_gen i with nohints using lst1 unfolding logic inverting logic ctrs logic opts noinvert); dsolve.
Tactic Notation "hauto" "unfolding" constr(lst2) :=
  unshelve (sauto_gen with nohints using default unfolding lst2 inverting logic ctrs logic opts noinvert); dsolve.
Tactic Notation "hauto" int_or_var(i) "unfolding" constr(lst2) :=
  unshelve (sauto_gen i with nohints using default unfolding lst2 inverting logic ctrs logic opts noinvert); dsolve.

Ltac rhauto lems unfolds := hauto using lems unfolding unfolds.
Ltac rhauto200 lems unfolds := hauto 200 using lems unfolding unfolds.
Ltac rhauto2000 lems unfolds := hauto 2000 using lems unfolding unfolds.
Ltac rsauto lems unfolds := sauto using lems unfolding unfolds.
Ltac rscrush lems unfolds := scrush using lems unfolding unfolds.

Ltac rcrush := scrush.
