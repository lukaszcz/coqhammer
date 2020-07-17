(* This file contains a definition of a simple imperative programming
   language together with its operational semantics and a definition
   of Hoare logic for it. Most definitions and lemma statements were
   translated into Coq from Isabelle/HOL statements present in the
   book:

   T. Nipkow, G. Klein, Concrete Semantics with Isabelle/HOL.

   This gives a rough idea of how the automation provided by CoqHammer
   compares to the automation available in Isabelle/HOL. *)

From Hammer Require Import Tactics Reflect.
Require Import String.
Require Import Arith.
Require Import Lia.
Open Scope string_scope.

Inductive aexpr :=
| Aval : nat -> aexpr
| Avar : string -> aexpr
| Aplus : aexpr -> aexpr -> aexpr
| Aminus : aexpr -> aexpr -> aexpr.

Coercion Aval : nat >-> aexpr.
Notation "A +! B" := (Aplus A B) (at level 50).
Notation "A -! B" := (Aminus A B) (at level 50).
Notation "^ A" := (Avar A) (at level 40).

Definition state := string -> nat.

Fixpoint aval (s : state) (e : aexpr) :=
  match e with
  | Aval n => n
  | Avar x => s x
  | Aplus x y => aval s x + aval s y
  | Aminus x y => aval s x - aval s y
  end.

Inductive bexpr :=
| Bval : bool -> bexpr
| Bnot : bexpr -> bexpr
| Band : bexpr -> bexpr -> bexpr
| Bless : aexpr -> aexpr -> bexpr.

Coercion Bval : bool >-> bexpr.
Notation "~! A" := (Bnot A) (at level 55).
Notation "A &! B" := (Band A B) (at level 55).
Notation "A <! B" := (Bless A B) (at level 54).

Fixpoint bval (s : state) (e : bexpr) :=
  match e with
  | Bval b => b
  | Bnot e1 => negb (bval s e1)
  | Band e1 e2 => bval s e1 && bval s e2
  | Bless a1 a2 => aval s a1 <? aval s a2
  end.

Inductive cmd :=
| Nop : cmd
| Assign : string -> aexpr -> cmd
| Seq : cmd -> cmd -> cmd
| If : bexpr -> cmd -> cmd -> cmd
| While : bexpr -> cmd -> cmd.

Notation "A <- B" := (Assign A B) (at level 60).
Notation "A ;; B" := (Seq A B) (at level 70).
Notation "'If' A 'Then' B 'Else' C" := (If A B C) (at level 65).
Notation "'While' A 'Do' B" := (While A B) (at level 65).

Definition update (s : state) x v y :=
  if string_dec x y then v else s y.

Definition state_subst (s : state) (x : string) (a : aexpr) : state :=
  (update s x (aval s a)).

Notation "s [ x := a ]" := (state_subst s x a) (at level 5).

Lemma lem_subst_eq : forall s x a, s[x := a] x = aval s a.
Proof.
  sauto unfold: state_subst, update.
Qed.

Lemma lem_subst_neq : forall s x y a, x <> y -> s[x := a] y = s y.
Proof.
  sauto unfold!: state_subst, update.
  (* "unfold:" may unfold or not based on some heuristic criteria;
     "unfold!:" is a primitive version which always unfolds *)
Qed.

(* Big-step operational semantics *)

Inductive BigStep : cmd -> state -> state -> Prop :=
| NopSem : forall s, BigStep Nop s s
| AssignSem : forall s x a, BigStep (x <- a) s s[x := a]
| SeqSem : forall c1 c2 s1 s2 s3, BigStep c1 s1 s2 -> BigStep c2 s2 s3 ->
                                  BigStep (c1 ;; c2) s1 s3
| IfTrue : forall b c1 c2 s s', bval s b -> BigStep c1 s s' ->
                                BigStep (If b Then c1 Else c2) s s'
| IfFalse : forall b c1 c2 s s', negb (bval s b) -> BigStep c2 s s' ->
                                 BigStep (If b Then c1 Else c2) s s'
| WhileFalse : forall b c s, negb (bval s b) -> BigStep (While b Do c) s s
| WhileTrue : forall b c s1 s2 s3,
    bval s1 b -> BigStep c s1 s2 -> BigStep (While b Do c) s2 s3 ->
    BigStep (While b Do c) s1 s3.

Notation "A >> B ==> C" :=
  (BigStep A B C) (at level 80, no associativity).

Lemma lem_seq_assoc : forall c1 c2 c3 s s', c1;; (c2;; c3) >> s ==> s' <->
                                            (c1;; c2);; c3 >> s ==> s'.
Proof.
  sauto.
Qed.

Definition equiv_cmd (c1 c2 : cmd) :=
  forall s s', c1 >> s ==> s' <-> c2 >> s ==> s'.

Notation "A ~~ B" := (equiv_cmd A B) (at level 75, no associativity).

Lemma lem_unfold_loop : forall b c, While b Do c ~~ If b Then c;; While b Do c Else Nop.
Proof.
  sauto unfold: equiv_cmd.
Qed.

Lemma lem_while_cong_aux : forall b c c' s s', While b Do c >> s ==> s' -> c ~~ c' ->
                                               While b Do c' >> s ==> s'.
Proof.
  intros *.
  remember (While b Do c) as w.
  induction 1; sauto unfold: equiv_cmd.
Qed.

Lemma lem_while_cong : forall b c c', c ~~ c' -> While b Do c ~~ While b Do c'.
Proof.
  hauto use: lem_while_cong_aux unfold: equiv_cmd.
Qed.

Lemma lem_big_step_deterministic :
  forall c s s1, c >> s ==> s1 -> forall s2, c >> s ==> s2 -> s1 = s2.
Proof.
  induction 1; sauto brefl: on.
Qed.

Inductive SmallStep : cmd * state -> cmd * state -> Prop :=
| AssignSemS : forall x a s, SmallStep (x <- a, s) (Nop, s[x := a])
| SeqSemS1 : forall c s, SmallStep (Nop ;; c, s) (c, s)
| SeqSemS2 : forall c1 c2 s c1' s', SmallStep (c1, s) (c1', s') ->
                                    SmallStep (c1 ;; c2, s) (c1';; c2, s')
| IfTrueS : forall b c1 c2 s, bval s b ->
                              SmallStep (If b Then c1 Else c2, s) (c1, s)
| IfFalseS : forall b c1 c2 s, negb (bval s b) ->
                               SmallStep (If b Then c1 Else c2, s) (c2, s)
| WhileS : forall b c s, SmallStep (While b Do c, s)
                                   (If b Then c;; While b Do c Else Nop, s).

Notation "A --> B" := (SmallStep A B) (at level 80, no associativity).

Require Import Relations.

Definition SmallStepStar := clos_refl_trans (cmd * state) SmallStep.

Notation "A -->* B" := (SmallStepStar A B) (at level 80, no associativity).

Lemma lem_small_step_deterministic :
  forall p p1, p --> p1 -> forall p2, p --> p2 -> p1 = p2.
Proof.
  induction 1; sauto brefl: on.
Qed.

Lemma lem_star_seq2 : forall c1 c2 s c1' s', (c1, s) -->* (c1', s') ->
                                             (c1;; c2, s) -->* (c1';; c2, s').
Proof.
  enough (forall p1 p2, p1 -->* p2 ->
                        forall c1 c2 s c1' s', p1 = (c1, s) -> p2 = (c1', s') ->
                                               (c1;; c2, s) -->* (c1';; c2, s')).
  { eauto. }
  induction 1; sauto.
Qed.

Lemma lem_seq_comp : forall c1 c2 s1 s2 s3,
    (c1, s1) -->* (Nop, s2) ->
    (c2, s2) -->* (Nop, s3) ->
    (c1;; c2, s1) -->* (Nop, s3).
Proof.
  intros c1 c2 s1 s2 s3 H1 H2.
  assert ((c1;; c2, s1) -->* (Nop;; c2, s2)) by sauto use: lem_star_seq2.
  sauto.
Qed.

Lemma lem_big_to_small : forall c s s', c >> s ==> s' -> (c, s) -->* (Nop, s').
Proof.
  intros c s s' H.
  induction H as [ | | | | | | b c s1 s2 ].
  - sauto.
  - sauto.
  - sauto use: lem_seq_comp.
  - sauto.
  - sauto.
  - sauto.
  - assert ((While b Do c, s1) -->* (c;; While b Do c, s1)) by sauto.
    assert ((c;; While b Do c, s1) -->* (Nop;; While b Do c, s2)) by
        sauto use: lem_star_seq2.
    sauto.
Qed.

Lemma lem_small_to_big_aux : forall p p',
    p --> p' -> forall c1 s1 c2 s2 s,
      p = (c1, s1) -> p' = (c2, s2) -> c2 >> s2 ==> s ->
      c1 >> s1 ==> s.
Proof.
  (* induction 1; sintuition. *)
  (* induction 1; qsimpl. *)
  induction 1; sauto use: lem_unfold_loop.
Qed.

Lemma lem_small_to_big_aux_2 : forall p p',
    p -->* p' -> forall c1 s1 c2 s2 s,
      p = (c1, s1) -> p' = (c2, s2) -> c2 >> s2 ==> s ->
      c1 >> s1 ==> s.
Proof.
  induction 1; sauto use: lem_small_to_big_aux.
Qed.

Lemma lem_small_to_big : forall c s s', (c, s) -->* (Nop, s') -> c >> s ==> s'.
Proof.
  enough (forall p p', p -->* p' ->
                       forall c s s', p = (c, s) -> p' = (Nop, s') ->
                                      c >> s ==> s') by eauto.
  induction 1; sauto use: lem_small_to_big_aux_2.
Qed.

Corollary cor_big_iff_small :
  forall c s s', c >> s ==> s' <-> (c, s) -->* (Nop, s').
Proof.
  sauto use: lem_small_to_big, lem_big_to_small.
Qed.

(* Hoare triples *)

Definition assn := state -> Prop.

Definition HoareValid (P : assn) (c : cmd) (Q : assn): Prop :=
  forall s s', c >> s ==> s' -> P s -> Q s'.

Notation "|= {{ P }} c {{ Q }}" := (HoareValid P c Q).

(* Hoare logic *)

Definition entails (P Q : assn) : Prop := forall s, P s -> Q s.

Inductive Hoare : assn -> cmd -> assn -> Prop :=
| Hoare_Nop : forall P, Hoare P Nop P
| Hoare_Assign : forall P a x,
    Hoare (fun s => P s[x := a]) (x <- a) P
| Hoare_Seq : forall P Q R c1 c2,
    Hoare P c1 Q -> Hoare Q c2 R -> Hoare P (c1 ;; c2) R
| Hoare_If : forall P Q b c1 c2,
    Hoare (fun s => P s /\ bval s b) c1 Q ->
    Hoare (fun s => P s /\ negb (bval s b)) c2 Q ->
    Hoare P (If b Then c1 Else c2) Q
| Hoare_While : forall P b c,
    Hoare (fun s => P s /\ bval s b) c P ->
    Hoare P (While b Do c) (fun s => P s /\ negb (bval s b))
| Hoare_conseq: forall P P' Q Q' c,
    Hoare P c Q -> entails P' P -> entails Q Q' -> Hoare P' c Q'.

Notation "|- {{ s | P }} c {{ s' | Q }}" :=
  (Hoare (fun s => P) c (fun s' => Q)).
Notation "|- {{ s | P }} c {{ Q }}" := (Hoare (fun s => P) c Q).
Notation "|- {{ P }} c {{ s' | Q }}" := (Hoare P c (fun s' => Q)).
Notation "|- {{ P }} c {{ Q }}" := (Hoare P c Q).

Lemma lem_hoare_strengthen_pre : forall P P' Q c,
    entails P' P -> |- {{P}} c {{Q}} -> |- {{P'}} c {{Q}}.
Proof.
  sauto unfold: entails.
Qed.

Lemma lem_hoare_weaken_post : forall P Q Q' c,
    entails Q Q' -> |- {{P}} c {{Q}} -> |- {{P}} c {{Q'}}.
Proof.
  sauto unfold: entails.
Qed.

Lemma hoare_assign : forall (P Q : assn) x a,
    (forall s, P s -> Q s[x := a]) -> |- {{P}} x <- a {{Q}}.
Proof.
  intros P Q x a.
  sauto use: (lem_hoare_strengthen_pre (fun s => Q s[x := a])).
Qed.

Lemma hoare_while : forall b (P Q: assn) c,
    |- {{s | P s /\ bval s b}} c {{P}} ->
       (forall s, P s /\ negb (bval s b) -> Q s) ->
    |- {{P}} (While b Do c) {{Q}}.
Proof.
  intros b P Q c.
  sauto use:
    (lem_hoare_weaken_post P
                           (fun s : state => P s /\ negb (bval s b))
                           Q (While b Do c)).
Qed.

(* Soundness of Hoare logic *)

Theorem thm_hoare_correct : forall P Q c,
    |- {{P}} c {{Q}} -> |= {{P}} c {{Q}}.
Proof.
  unfold HoareValid.
  induction 1.
  - sauto.
  - sauto.
  - sauto inv: BigStep.
  - sauto inv: BigStep.
  - intros *.
    remember (While b Do c).
    induction 1; qauto inv: BigStep.
  - sauto unfold: entails.
Qed.
