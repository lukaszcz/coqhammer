(* Coq v8.9 required *)
(* author: Lukasz Czajka *)
(* This file contains reconstruction tactics for CoqHammer. *)
(* Copyright (c) 2017-2019, Lukasz Czajka and Cezary Kaliszyk, University of Innsbruck *)
(* This file may be distributed under the terms of the LGPL 2.1 license. *)

Declare ML Module "hammer_lib".

Require List Arith ZArith Bool.

Inductive ReconstrT : Set := Empty : ReconstrT | AllHyps : ReconstrT.

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

Ltac tyexact L := let tp := type of L in exact tp.

Ltac getgoal := match goal with [ |- ?G ] => G end.

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

Ltac all f ls :=
  match ls with
    | Empty => idtac
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

Ltac yeasy :=
  let rec use_hyp H :=
    match type of H with
    | _ /\ _ => exact H || destruct_hyp H
    | _ => try solve [ inversion H ]
    end
  with do_intro := let H := fresh in intro H; use_hyp H
  with destruct_hyp H := case H; clear H; do_intro; do_intro in
  let rec use_hyps :=
    match goal with
    | H : _ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
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

Ltac unfolding defs :=
  repeat (autounfold with shints; unfold iff in *; unfold not in *; all tryunfold defs).

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

Ltac ydestruct t :=
  lazymatch t with
    | _ _ => destruct t eqn:?
    | _ =>
      tryif is_evar t then
         destruct t eqn:?
      else
        (is_var t; destruct t)
  end.

Ltac yinversion H := inversion H; try subst; try clear H.

Ltac xintro x :=
  tryif intro x then
    idtac
  else
    let x1 := fresh x in
    intro x1.

Ltac yintro :=
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
    | (exists x, _) => elim H; clear H; xintro x; yintro
    | { x & _ } => elim H; clear H; xintro x; yintro
    | { x | _ } => elim H; clear H; xintro x; yintro
    | ?A = ?A => clear H
    | ?A -> ?A => clear H
    | ?A -> ?B = ?B => clear H
    | ?A /\ ?A => cut A; [ clear H; yintro | destruct H; assumption ]
    | ?A /\ ?B => elim H; clear H; yintro; yintro
    | ?A /\ ?B -> ?C => cut (A -> B -> C);
                                    [ clear H; yintro
                                    | intro; intro; apply H; split; assumption ]
    | ?A = ?A -> ?B => cut B; [ clear H; yintro | apply H; reflexivity ]
    | ?A -> ?A -> ?B => cut (A -> B); [ clear H; yintro | intro; apply H; assumption ]
    | ?A \/ ?A => cut A; [ clear H; yintro | elim H; intro; assumption ]
    | ?A \/ ?B -> ?C =>
      cut (A -> C); [ cut (B -> C); [ clear H; yintro; yintro |
                                      intro; apply H; right; assumption ] |
                      intro; apply H; left; assumption ]
    | Some _ = Some _ => injection H; try clear H
    | ?F ?X = ?F ?Y =>
      (assert (X = Y); [ assumption | fail 1 ])
      || (injection H; try clear H;
          match goal with
          | [ |- _ = _ -> _ ] =>
            yintro; try subst
          end)
    | ?F ?X ?U = ?F ?Y ?V =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   yintro; try subst
                 end)
    | ?F ?X ?U ?A = ?F ?Y ?V ?B =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption |
                                           assert (A = B); [ assumption | fail 1 ] ]])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   yintro; try subst
                 end)
    | existT _ _ _ = existT _ _ _ => inversion_clear H
    | forall x : ?T1, ?A /\ ?B =>
      cut (forall x : T1, A);
        [ cut (forall x : T1, B);
          [ clear H; yintro; yintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2), A);
        [ cut (forall (x : T1) (y : T2), B);
          [ clear H; yintro; yintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3), A);
        [ cut (forall (x : T1) (y : T2) (z : T3), B);
          [ clear H; yintro; yintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4), B);
          [ clear H; yintro; yintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), B);
          [ clear H; yintro; yintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6), B);
          [ clear H; yintro; yintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6) (w1 : ?T7), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6) (w1 : T7), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6) (w1 : T7), B);
          [ clear H; yintro; yintro | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6)
             (w1 : ?T7) (w2 : ?T8), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6)
                  (w1 : T7) (w2 : T8), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6)
                      (w1 : T7) (w2 : T8), B);
          [ clear H; yintro; yintro | apply H ]
        | apply H ]
    | forall x : ?T1, ?A /\ ?B -> ?C =>
      cut (forall x : T1, A -> B -> C);
        [ clear H; yintro | do 3 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2), A -> B -> C);
        [ clear H; yintro | do 4 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3), A -> B -> C);
        [ clear H; yintro | do 5 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A -> B -> C);
        [ clear H; yintro | do 6 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A -> B -> C);
        [ clear H; yintro | do 7 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1), ?A \/ ?B -> ?C =>
      cut (forall (x : T1), A -> C); [ cut (forall (x : T1), B -> C);
                                       [ clear H; yintro; yintro |
                                         do 2 intro; apply H with (x := x); right; assumption ] |
                                       do 2 intro; apply H with (x := x); left; assumption ]
    | forall (x : ?T1) (y : ?T2), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2), A -> C);
        [ cut (forall (x : T1) (y : T2), B -> C);
          [ clear H; yintro; yintro |
            do 3 intro; apply H with (x := x) (y := y); right; assumption ] |
          do 3 intro; apply H with (x := x) (y := y); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3), B -> C);
          [ clear H; yintro; yintro |
            do 4 intro; apply H with (x := x) (y := y) (z := z); right; assumption ] |
          do 4 intro; apply H with (x := x) (y := y) (z := z); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4), B -> C);
          [ clear H; yintro; yintro |
            do 5 intro; apply H with (x := x) (y := y) (z := z) (u := u); right; assumption ] |
          do 5 intro; apply H with (x := x) (y := y) (z := z) (u := u); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), B -> C);
          [ clear H; yintro; yintro |
            do 6 intro; apply H with (x := x) (y := y) (z := z) (u := u) (v := v);
            right; assumption ] |
          do 6 intro; apply H with (x := x) (y := y) (z := z) (u := u) (v := v);
          left; assumption ]
    | ?A -> ?B =>
      lazymatch goal with
        | [ H1 : A |- _ ] => cut B; [ clear H; yintro | apply H; exact H1 ]
      end
  end.

Ltac yintros :=
  repeat match goal with [ |- ?G ] => isAtom G; fail 1 | [ |- _ ] => yintro end.

Ltac intros_until_atom :=
  repeat match goal with [ |- ?G ] => isAtom G; fail 1 | [ |- _ ] => intro end.

Ltac simp_hyps :=
  unfold iff in *; unfold not in *;
  repeat match goal with
           | [ H2 : ?A -> ?B, H1 : ?A |- _ ] =>
             assert B by (apply H2; exact H1); clear H2
           | [ H : _ |- _ ] =>
             simp_hyp H
         end.

Ltac esimp_hyps :=
  unfold iff in *; unfold not in *;
  repeat match goal with
         | [ H2 : ?A2 -> ?B, H1 : ?A1 |- _ ] =>
           unify A1 A2; notHyp B;
           assert B by (apply H2; exact H1); clear H2
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
    | [ |- context[match ?X with _ => _ end] ] => ydestruct X
    | [ H : context[match ?X with _ => _ end] |- _ ] => ydestruct X
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
    | [ |- ?t = ?u ] => try solve [ cbn in *; congruence 8 ]
    | [ |- ?t <> ?u ] => try solve [ cbn in *; congruence 8 ]
    | [ |- False ] => try solve [ cbn in *; congruence 8 ]
    | _ => idtac
  end.

Ltac msplit splt simp :=
  simp tt;
  repeat (progress splt tt; simp tt).

Ltac isolve :=
  let rec msolve splt simp :=
      msplit splt simp;
      lazymatch goal with
        | [ H : False |- _ ] => exfalso; exact H
        | _ =>
          solve [ trysolve | left; msolve splt simp | right; msolve splt simp |
                  eexists; msolve splt simp ]
      end
  in
  msolve ltac:(fun _ => isplit) ltac:(fun _ => intros; simp_hyps; repeat exsimpl).

Ltac dsolve := auto with shints; try yeasy; try solve [ repeat constructor ].

Ltac ssolve := intuition (auto with yhints); try solve [ isolve ]; try yeasy;
               try congruence 16; try solve [ constructor; isolve ].

Ltac yisolve := try solve [ unfold iff in *; unfold not in *; unshelve isolve; dsolve ].

Ltac bnat_reflect :=
  repeat match goal with
         | [ H : (Nat.eqb ?A ?B) = true |- _ ] =>
           notHyp (A = B);
           assert (A = B) by (pose Arith.PeanoNat.Nat.eqb_eq; yisolve)
         | [ H : (Nat.eqb ?A ?B) = false |- _ ] =>
           notHyp (A <> B);
           assert (A <> B) by (pose Arith.PeanoNat.Nat.eqb_neq; yisolve)
         | [ H : (Nat.leb ?A ?B) = true |- _ ] =>
           notHyp (A <= B);
           assert (A <= B) by (eauto using Arith.Compare_dec.leb_complete)
         | [ H : (Nat.leb ?A ?B) = false |- _ ] =>
           notHyp (B < A);
           assert (B < A) by (eauto using Arith.Compare_dec.leb_complete_conv)
         | [ H : (Nat.ltb ?A ?B) = true |- _ ] =>
           notHyp (A < B);
           assert (A < B) by (pose Arith.PeanoNat.Nat.ltb_lt; yisolve)
         | [ H : (Nat.ltb ?A ?B) = false |- _ ] =>
           notHyp (B <= A);
           assert (B <= A) by (pose Arith.PeanoNat.Nat.ltb_ge; yisolve)
         end.

Ltac subst_simpl := try subst; cbn in *.

Ltac simple_invert H := solve [ inversion H ] || (inversion H; [idtac]; clear H; try subst; cbn).
Ltac simple_inverting :=
  repeat match goal with
         | [ H : ?P |- _ ] => simple_invert H
         end.

Ltac simple_split :=
  match goal with
    | [ |- ?A /\ _ ] =>
      cut A; [ let H := fresh "H" in
               intro H; split; [ exact H | simp_hyp H ] | idtac ]
    | [ |- prod ?A _ ] =>
      cut A; [ let H := fresh "H" in
               intro H; split; [ exact H | simp_hyp H ] | idtac ]
  end.

Ltac simple_splitting := repeat (simple_split; cbn).

Ltac case_split :=
  match goal with
  | [ |- context[match ?X with _ => _ end] ] => ydestruct X
  | [ H : context[match ?X with _ => _ end] |- _ ] => ydestruct X
  end.

Ltac case_splitting := repeat (case_split; subst_simpl).

Ltac generalizing :=
  repeat match goal with
           | [ H : _ |- _ ] => generalize H; clear H
         end.

Ltac fsolve := solve [ eassumption | econstructor | symmetry; eassumption ].

Ltac finst e :=
  let tpe := type of e
  in
  lazymatch tpe with
    | ?T -> ?Q =>
      let H := fresh "H" in
      assert (H : T); [ try fsolve | finst (e H); clear H ]
    | forall x : ?T, _ =>
      let v := fresh "v" in
      evar (v : T);
      let v2 := eval unfold v in v in
      clear v;
      finst (e v2)
    | _ =>
      generalize e
  end.

Ltac einvert H :=
  finst H;
  let H1 := fresh "H" in
  intro H1; inversion_clear H1; cbn.

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
      einster (e v2) tac
    | _ =>
      generalize e
  end.

Ltac forward H :=
  einst H;
  match goal with
  | [ |- (?P -> ?Q) -> _ ] =>
    let H1 := fresh "H" in
    intro H1;
    let H2 := fresh "H" in
    assert (H2 : P) by fsolve;
    generalize (H1 H2);
    clear H1; clear H2;
    intro H1;
    einster H1 fsolve;
    clear H1;
    match goal with
    | [ |- ?P -> _ ] => noteHyp P; lazymatch type of P with Type => fail | _ => yintro end
    end
  end.

Ltac forwarding :=
  repeat match goal with
         | [ H : forall x : _,_ |- _ ] => forward H
         end.

Declare ML Module "hammer_tactics".

Ltac sauto := unshelve sauto_gen; dsolve.
Ltac ssimpl := unshelve ssimpl_gen; dsolve.
