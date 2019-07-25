(* Coq v8.9 required *)
(* author: Lukasz Czajka *)
(* This file contains reconstruction tactics for CoqHammer. *)
(* Copyright (c) 2017-2018, Lukasz Czajka and Cezary Kaliszyk, University of Innsbruck *)
(* This file may be distributed under the terms of the LGPL 2.1 license. *)
(* Fragments of this file are based on the "crush" tactic of Adam Chlipala. *)

Declare ML Module "hammer_lib".

Require List Arith ZArith Bool.

Inductive ReconstrT : Set := Empty : ReconstrT | AllHyps : ReconstrT.

Create HintDb yhints discriminated.

Hint Rewrite -> Arith.PeanoNat.Nat.add_0_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.sub_0_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_0_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_1_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.add_assoc : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_assoc : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_add_distr_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_add_distr_l : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_sub_distr_r : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.mul_sub_distr_l : yhints.
Hint Rewrite -> Arith.PeanoNat.Nat.sub_add_distr : yhints.
Hint Rewrite -> ZArith.BinInt.Z.add_0_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.sub_0_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_0_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_1_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.add_assoc : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_assoc : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_add_distr_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_add_distr_l : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_sub_distr_r : yhints.
Hint Rewrite -> ZArith.BinInt.Z.mul_sub_distr_l : yhints.
Hint Rewrite -> ZArith.BinInt.Z.sub_add_distr : yhints.
Hint Rewrite -> List.in_app_iff : yhints.
Hint Rewrite -> List.in_map_iff : yhints.
Hint Rewrite -> List.in_inv : yhints.
Hint Rewrite <- List.app_assoc : yhints.
Hint Rewrite -> Bool.orb_true_r : yhints.
Hint Rewrite -> Bool.orb_true_l : yhints.
Hint Rewrite -> Bool.orb_false_r : yhints.
Hint Rewrite -> Bool.orb_false_l : yhints.
Hint Rewrite -> Bool.andb_true_r : yhints.
Hint Rewrite -> Bool.andb_true_l : yhints.
Hint Rewrite -> Bool.andb_false_r : yhints.
Hint Rewrite -> Bool.andb_false_l : yhints.

Ltac tyexact L := let tp := type of L in exact tp.

Ltac getgoal := match goal with [ |- ?G ] => G end.

Ltac notHyp P :=
  match goal with
    | [ H : ?P1 |- _ ] => constr_eq P P1; fail 1
    | _ => idtac
  end.

Ltac isProp t :=
  lazymatch type of t with
    | Prop => idtac
  end.

Ltac notProp t :=
  lazymatch type of t with
    | Prop => fail
    | _ => idtac
  end.

Ltac checkListLen lst n :=
  lazymatch n with
    | 0 => constr_eq lst Empty
    | S ?k =>
      lazymatch lst with
        | (?t, ?h) => checkListLen t k
        | _ => idtac
      end
  end.

Ltac noEvars t := tryif has_evar t then fail else idtac.

Ltac natLe m n :=
  let t := constr:(Nat.leb m n) in
  let b := (eval compute in t) in
  match b with
    | true => idtac
  end.

(* TODO: `isAtom c' fails for a constant c *)
Ltac isAtom t :=
  lazymatch t with
    | ?A /\ ?B => fail
    | ?A \/ ?B => fail
    | exists x, _ => fail
    | _ _ => idtac
    | (_ /\ _) -> False => fail
    | (_ \/ _) -> False => fail
    | (exists x, _) -> False => fail
    | _ _ -> False => idtac
    | ?A -> False => is_var A
    | _ => is_var t
  end.

Ltac isPropAtom t := isAtom t; isProp t.

Ltac inList x lst :=
  lazymatch lst with
    | (?t, ?y) => tryif constr_eq x y then idtac else inList x t
    | x => idtac
    | _ => fail
  end.

Ltac notInList x lst := tryif inList x lst then fail else idtac.

Ltac all f ls :=
  match ls with
    | Empty => idtac
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

Ltac lst_rev lst :=
  let rec hlp lst acc :=
      match lst with
        | Empty => acc
        | (?t, ?h) => hlp t (acc, h)
        | ?x => constr:((acc, x))
      end
  in
  hlp lst Empty.

Ltac with_hyps p f :=
  let rec hlp acc :=
      match goal with
        | [ H : ?P |- _ ] =>
          p P; notInList H acc; hlp (acc, H)
        | _ =>
          f ltac:(lst_rev acc)
      end
  in
  hlp Empty.

Ltac with_prop_hyps := with_hyps isProp.
Ltac with_atom_hyps := with_hyps isAtom.
Ltac all_hyps f := with_hyps ltac:(fun _ => idtac) ltac:(all f).
Ltac all_prop_hyps f := with_prop_hyps ltac:(all f).
Ltac all_atom_hyps f := with_atom_hyps ltac:(all f).

Ltac countHyps inb :=
  let rec hlp n :=
      match goal with
        | [ H : _ |- _ ] =>
          revert H; hlp (S n); intro H
        | _ => pose (inb := n)
      end
  in
  hlp 0.

Ltac checkHypsNum n :=
  let m := fresh "m" in
  countHyps m;
  let k := (eval unfold m in m) in
  natLe k n; clear m.

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
  repeat (autounfold with yhints; unfold iff in *; unfold not in *; all tryunfold defs).

Ltac einst e :=
  let tpe := type of e
  in
  match tpe with
    | forall x : ?T, _ =>
      notProp T;
      let v := fresh "v" in
      evar (v : T);
      let v2 := eval unfold v in v in
      clear v;
      einst (e v2)
    | _ =>
      generalize e
  end.

Ltac trysolve :=
  eauto 2 with nocore yhints; try solve [ constructor ]; try subst;
  match goal with
    | [ |- ?t = ?u ] => try solve [ hnf in *; congruence 8 ]
    | [ |- ?t <> ?u ] => try solve [ hnf in *; congruence 8 ]
    | [ |- False ] => try solve [ hnf in *; congruence 8 ]
    | _ => idtac
  end.

Ltac msplit splt simp :=
  simp tt;
  repeat (progress splt tt; simp tt).

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
  | [ |- forall x : ?T, _ ] =>
    tryif isProp T then
      let H := fresh "H" in
      (tryif notHyp T then
          (intro H; try simp_hyp H)
        else
          (intro H; try clear H))
    else
      xintro x
  end

with simp_hyp H :=
  let sintro tt := yintro in
  let tp := type of H in
  lazymatch tp with
    | (exists x, _) => elim H; clear H; xintro x; sintro tt
    | { x & _ } => elim H; clear H; xintro x; sintro tt
    | { x | _ } => elim H; clear H; xintro x; sintro tt
    | ?A = ?A => clear H
    | ?A -> ?A => clear H
    | ?A -> ?B = ?B => clear H
    | ?A /\ ?A => cut A; [ clear H; sintro tt | destruct H; assumption ]
    | ?A /\ ?B => elim H; clear H; sintro tt; sintro tt
    | ?A /\ ?B -> ?C => cut (A -> B -> C);
                                    [ clear H; sintro tt
                                    | intro; intro; apply H; split; assumption ]
    | ?A = ?A -> ?B => cut B; [ clear H; sintro tt | apply H; reflexivity ]
    | ?A -> ?A -> ?B => cut (A -> B); [ clear H; sintro tt | intro; apply H; assumption ]
    | ?A \/ ?A => cut A; [ clear H; sintro tt | elim H; intro; assumption ]
    | ?A \/ ?B -> ?C =>
      cut (A -> C); [ cut (B -> C); [ clear H; sintro tt; sintro tt |
                                      intro; apply H; right; assumption ] |
                      intro; apply H; left; assumption ]
    | Some _ = Some _ => injection H; try clear H
    | ?F ?X = ?F ?Y =>
      (assert (X = Y); [ assumption | fail 1 ])
      || (injection H; try clear H;
          match goal with
          | [ |- _ = _ -> _ ] =>
            sintro tt; try subst
          end)
    | ?F ?X ?U = ?F ?Y ?V =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   sintro tt; try subst
                 end)
    | ?F ?X ?U ?A = ?F ?Y ?V ?B =>
      (assert (X = Y); [ assumption
                       | assert (U = V); [ assumption |
                                           assert (A = B); [ assumption | fail 1 ] ]])
      || (injection H; try clear H;
          repeat match goal with
                 | [ |- _ = _ -> _ ] =>
                   sintro tt; try subst
                 end)
    | existT _ _ _ = existT _ _ _ => inversion_clear H
    | forall x : ?T1, ?A /\ ?B =>
      cut (forall x : T1, A);
        [ cut (forall x : T1, B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2), A);
        [ cut (forall (x : T1) (y : T2), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3), A);
        [ cut (forall (x : T1) (y : T2) (z : T3), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6) (w1 : ?T7), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6) (w1 : T7), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6) (w1 : T7), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5) (w : ?T6)
             (w1 : ?T7) (w2 : ?T8), ?A /\ ?B =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6)
                  (w1 : T7) (w2 : T8), A);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5) (w : T6)
                      (w1 : T7) (w2 : T8), B);
          [ clear H; sintro tt; sintro tt | apply H ]
        | apply H ]
    | forall x : ?T1, ?A /\ ?B -> ?C =>
      cut (forall x : T1, A -> B -> C);
        [ clear H; sintro tt | do 3 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2), A -> B -> C);
        [ clear H; sintro tt | do 4 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3), A -> B -> C);
        [ clear H; sintro tt | do 5 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A -> B -> C);
        [ clear H; sintro tt | do 6 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A /\ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A -> B -> C);
        [ clear H; sintro tt | do 7 intro; apply H; try assumption; split; assumption ]
    | forall (x : ?T1), ?A \/ ?B -> ?C =>
      cut (forall (x : T1), A -> C); [ cut (forall (x : T1), B -> C);
                                       [ clear H; sintro tt; sintro tt |
                                         do 2 intro; apply H with (x := x); right; assumption ] |
                                       do 2 intro; apply H with (x := x); left; assumption ]
    | forall (x : ?T1) (y : ?T2), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2), A -> C);
        [ cut (forall (x : T1) (y : T2), B -> C);
          [ clear H; sintro tt; sintro tt |
            do 3 intro; apply H with (x := x) (y := y); right; assumption ] |
          do 3 intro; apply H with (x := x) (y := y); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3), B -> C);
          [ clear H; sintro tt; sintro tt |
            do 4 intro; apply H with (x := x) (y := y) (z := z); right; assumption ] |
          do 4 intro; apply H with (x := x) (y := y) (z := z); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4), B -> C);
          [ clear H; sintro tt; sintro tt |
            do 5 intro; apply H with (x := x) (y := y) (z := z) (u := u); right; assumption ] |
          do 5 intro; apply H with (x := x) (y := y) (z := z) (u := u); left; assumption ]
    | forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), ?A \/ ?B -> ?C =>
      cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), A -> C);
        [ cut (forall (x : T1) (y : T2) (z : T3) (u : T4) (v : T5), B -> C);
          [ clear H; sintro tt; sintro tt |
            do 6 intro; apply H with (x := x) (y := y) (z := z) (u := u) (v := v);
            right; assumption ] |
          do 6 intro; apply H with (x := x) (y := y) (z := z) (u := u) (v := v);
          left; assumption ]
    | ?A -> ?B =>
      lazymatch goal with
        | [ H1 : A |- _ ] => isProp A; cut B; [ clear H; sintro tt | apply H; exact H1 ]
      end
  end.

Ltac simp_hyps :=
  unfold iff in *; unfold not in *;
  repeat match goal with
           | [ H1 : ?A, H2 : ?A -> ?B |- _ ] =>
             assert B by (apply H2; exact H1); clear H2
           | [ H : True |- _ ] =>
             clear H
           | [ H : _ |- _ ] =>
             simp_hyp H
         end.

Ltac esimp_hyps :=
  unfold iff in *; unfold not in *;
  repeat match goal with
         | [ H1 : ?A1, H2 : ?A2 -> ?B |- _ ] =>
           unify A1 A2; notHyp B;
           assert B by (apply H2; exact H1); clear H2
         | [ H : True |- _ ] =>
           clear H
         | [ H : _ |- _ ] =>
           simp_hyp H
         end.

Ltac exsimpl :=
  match goal with
    | [ H : forall (x : ?T1), exists a, _ |- _ ] =>
      notProp T1;
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2), exists a, _ |- _ ] =>
      notProp T1; notProp T2;
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3), exists a, _ |- _ ] =>
      notProp T1; notProp T2; notProp T3;
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), exists a, _ |- _ ] =>
      notProp T1; notProp T2; notProp T3; notProp T4;
      einst H; clear H; intro H; elim H; clear H; intro; intro
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), exists a, _ |- _ ] =>
      notProp T1; notProp T2; notProp T3; notProp T4; notProp T5;
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
      notProp T1;
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2), _ \/ _ |- _ ] =>
      notProp T1; notProp T2;
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3), _ \/ _ |- _ ] =>
      notProp T1; notProp T2; notProp T3;
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4), _ \/ _ |- _ ] =>
      notProp T1; notProp T2; notProp T3; notProp T4;
      einst H; clear H; intro H; elim H; clear H
    | [ H : forall (x : ?T1) (y : ?T2) (z : ?T3) (u : ?T4) (v : ?T5), _ \/ _ |- _ ] =>
      notProp T1; notProp T2; notProp T3; notProp T4; notProp T5;
      einst H; clear H; intro H; elim H; clear H
  end.

Ltac isolve :=
  let rec msolve splt simp :=
      msplit splt simp;
      lazymatch goal with
        | [ H : False |- _ ] => exfalso; exact H
        | [ |- _ \/ _ ] =>
          trysolve;
            try solve [ left; msolve splt simp | right; msolve splt simp ]
        | [ |- exists x, _ ] =>
          trysolve; try solve [ eexists; msolve splt simp ]
        | _ =>
          trysolve
      end
  in
  msolve ltac:(fun _ => isplit) ltac:(fun _ => intros; simp_hyps; repeat exsimpl).

Ltac dsolve :=
  match goal with
    | [ |- ?G ] => notProp G; auto with yhints; try solve [ repeat constructor ]
    | _ => auto with yhints; try yeasy
  end.

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
         end; try subst; auto.

Ltac simple_invert H := solve [ inversion H ] || (inversion H; [idtac]; clear H; try subst).
Ltac simple_inverting :=
  repeat match goal with
         | [ H : ?P |- _ ] => isPropAtom P; lazymatch P with _ = _ => fail | _ => simple_invert H end
         end.

Ltac eresolve H1 H2 :=
  let H1i := fresh "H" in
  einst H1; intro H1i;
  let H2i := fresh "H" in
  einst H2; intro H2i;
  let T1 := type of H1i in
  let T2 := type of H2i in
  match T2 with
    | ?A -> ?B =>
      unify T1 A;
      let e := fresh "H" in
      pose (e := H2i H1i);
      let tp := type of e in
      generalize e; clear e;
      notHyp tp; clear H1i; clear H2i
    | ?A1 = ?A2 -> ?B =>
      unify T1 (A2 = A1);
      let e := fresh "H" in
      pose (e := H2i (eq_sym H1i));
      let tp := type of e in
      generalize e; clear e;
      notHyp tp; clear H1i; clear H2i
  end.

Ltac generalizing :=
  repeat match goal with
           | [ H : _ |- _ ] => generalize H; clear H
         end.

Ltac ysplit :=
  match goal with
    | [ |- ?A /\ _ ] =>
      cut A; [ let H := fresh "H" in
               intro H; split; [ exact H | simp_hyp H ] | idtac ]
    | [ |- prod ?A _ ] =>
      cut A; [ let H := fresh "H" in
               intro H; split; [ exact H | simp_hyp H ] | idtac ]
    | [ |- context[match ?X with _ => _ end] ] => ydestruct X
    | [ H : context[match ?X with _ => _ end] |- _ ] => ydestruct X
  end.

Ltac ysplitting :=
  repeat ysplit;
  let n := numgoals in
  guard n < 12;
  yisolve;
  let n := numgoals in
  guard n < 6.

Ltac orinst H :=
  let tpH := type of H
  in
  lazymatch tpH with
    | forall x : ?T, _ =>
      tryif isProp T then
        let H0 := fresh "H" in
        assert (H0 : T); [ clear H |
                           let H1 := fresh "H" in
                           generalize (H H0); intro H1; clear H; clear H0;
                           orinst H1 ]
      else
        let v := fresh "v" in
        evar (v : T);
        let v2 := eval unfold v in v in
        clear v;
        let H1 := fresh "H" in
        generalize (H v2); intro H1; clear H;
        orinst H1
    | (_ + { _ }) => elim H; clear H; yintro
    | ({ _ } + { _ }) => elim H; clear H; yintro
    | _ \/ _ => elim H; clear H; yintro
  end.

Ltac yforward H :=
  einst H;
  progress repeat match goal with
                  | [ H0 : ?P |- (?Q -> _) -> _ ] =>
                    unify P Q;
                    let H1 := fresh "H" in
                    intro H1; generalize (H1 H0); clear H1
                  end;
  match goal with
  | [ |- ?P -> _ ] => noEvars P
  end;
  yintro.

Ltac yforwarding :=
  all_prop_hyps ltac:(fun H => try yforward H).

Ltac forward_reasoning n :=
  lazymatch n with
  | 0 => idtac
  | S ?k => yforwarding; forward_reasoning k
  end.

Declare ML Module "hammer_tactics".
