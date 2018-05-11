From Hammer Require Import Hammer.









Require Import Notations.
Require Import Logic.
Require Import Specif.





Ltac exfalso := elimtype False.



Ltac contradict H :=
let save tac H := let x:=fresh in intro x; tac H; rename x into H
in
let negpos H := case H; clear H
in
let negneg H := save negpos H
in
let pospos H :=
let A := type of H in (exfalso; revert H; try fold (~A))
in
let posneg H := save pospos H
in
let neg H := match goal with
| |- (~_) => negneg H
| |- (_->False) => negneg H
| |- _ => negpos H
end in
let pos H := match goal with
| |- (~_) => posneg H
| |- (_->False) => posneg H
| |- _ => pospos H
end in
match type of H with
| (~_) => neg H
| (_->False) => neg H
| _ => (elim H;fail) || pos H
end.



Ltac absurd_hyp H :=
idtac "absurd_hyp is OBSOLETE: use contradict instead.";
let T := type of H in
absurd T.



Ltac false_hyp H G :=
let T := type of H in absurd T; [ apply G | assumption ].



Ltac case_eq x := generalize (eq_refl x); pattern x at -1; case x.



Ltac destr_eq H := discriminate H || (try (injection H as H)).



Tactic Notation "destruct_with_eqn" constr(x) :=
destruct x eqn:?.
Tactic Notation "destruct_with_eqn" ident(n) :=
try intros until n; destruct n eqn:?.
Tactic Notation "destruct_with_eqn" ":" ident(H) constr(x) :=
destruct x eqn:H.
Tactic Notation "destruct_with_eqn" ":" ident(H) ident(n) :=
try intros until n; destruct n eqn:H.



Ltac destruct_all t :=
match goal with
| x : t |- _ => destruct x; destruct_all t
| _ => idtac
end.



Tactic Notation "rewrite_all" constr(eq) := repeat rewrite eq in *.
Tactic Notation "rewrite_all" "<-" constr(eq) := repeat rewrite <- eq in *.





Ltac find_equiv H :=
let T := type of H in
lazymatch T with
| ?A -> ?B =>
let H1 := fresh in
let H2 := fresh in
cut A;
[intro H1; pose proof (H H1) as H2; clear H H1;
rename H2 into H; find_equiv H |
clear H]
| forall x : ?t, _ =>
let a := fresh "a" with
H1 := fresh "H" in
evar (a : t); pose proof (H a) as H1; unfold a in H1;
clear a; clear H; rename H1 into H; find_equiv H
| ?A <-> ?B => idtac
| _ => fail "The given statement does not seem to end with an equivalence."
end.

Ltac bapply lemma todo :=
let H := fresh in
pose proof lemma as H;
find_equiv H; [todo H; clear H | .. ].

Tactic Notation "apply" "->" constr(lemma) :=
bapply lemma ltac:(fun H => destruct H as [H _]; apply H).

Tactic Notation "apply" "<-" constr(lemma) :=
bapply lemma ltac:(fun H => destruct H as [_ H]; apply H).

Tactic Notation "apply" "->" constr(lemma) "in" hyp(J) :=
bapply lemma ltac:(fun H => destruct H as [H _]; apply H in J).

Tactic Notation "apply" "<-" constr(lemma) "in" hyp(J) :=
bapply lemma ltac:(fun H => destruct H as [_ H]; apply H in J).



Ltac easy :=
let rec use_hyp H :=
match type of H with
| _ /\ _ => exact H || destruct_hyp H
| _ => try solve [inversion H]
end
with do_intro := let H := fresh in intro H; use_hyp H
with destruct_hyp H := case H; clear H; do_intro; do_intro in
let rec use_hyps :=
match goal with
| H : _ /\ _ |- _  => exact H || (destruct_hyp H; use_hyps)
| H : _ |- _ => solve [inversion H]
| _ => idtac
end in
let do_atom :=
solve [ trivial with eq_true | reflexivity | symmetry; trivial | contradiction ] in
let rec do_ccl :=
try do_atom;
repeat (do_intro; try do_atom);
solve [ split; do_ccl ] in
solve [ do_atom | use_hyps; do_ccl ] ||
fail "Cannot solve this goal".

Tactic Notation "now" tactic(t) := t; easy.



Ltac easy' := repeat split; simpl; easy || now destruct 1.



Ltac now_show c := change c.



Set Implicit Arguments.

Lemma decide_left : forall (C:Prop) (decide:{C}+{~C}),
C -> forall P:{C}+{~C}->Prop, (forall H:C, P (left _ H)) -> P decide.
Proof. try hammer_hook "Tactics" "Tactics.decide_left".  
intros; destruct decide. apply H0. contradiction.
Qed.

Lemma decide_right : forall (C:Prop) (decide:{C}+{~C}),
~C -> forall P:{C}+{~C}->Prop, (forall H:~C, P (right _ H)) -> P decide.
Proof. try hammer_hook "Tactics" "Tactics.decide_right".  
intros; destruct decide. contradiction. apply H0.
Qed.

Tactic Notation "decide" constr(lemma) "with" constr(H) :=
let try_to_merge_hyps H :=
try (clear H; intro H) ||
(let H' := fresh H "bis" in intro H'; try clear H') ||
(let H' := fresh in intro H'; try clear H') in
match type of H with
| ~ ?C => apply (decide_right lemma H); try_to_merge_hyps H
| ?C -> False => apply (decide_right lemma H); try_to_merge_hyps H
| _ => apply (decide_left lemma H); try_to_merge_hyps H
end.



Tactic Notation "clear" "dependent" hyp(h) :=
let rec depclear h :=
clear h ||
match goal with
| H : context [ h ] |- _ => depclear H; depclear h
end ||
fail "hypothesis to clear is used in the conclusion (maybe indirectly)"
in depclear h.



Tactic Notation "revert" "dependent" hyp(h) :=
generalize dependent h.



Tactic Notation "dependent" "induction" ident(H) :=
fail "To use dependent induction, first [Require Import Coq.Program.Equality.]".



Ltac simpl_proj_exist_in H :=
repeat match type of H with
| context G[proj1_sig (exist _ ?x ?p)]
=> let G' := context G[x] in change G' in H
| context G[proj2_sig (exist _ ?x ?p)]
=> let G' := context G[p] in change G' in H
| context G[projT1 (existT _ ?x ?p)]
=> let G' := context G[x] in change G' in H
| context G[projT2 (existT _ ?x ?p)]
=> let G' := context G[p] in change G' in H
| context G[proj3_sig (exist2 _ _ ?x ?p ?q)]
=> let G' := context G[q] in change G' in H
| context G[projT3 (existT2 _ _ ?x ?p ?q)]
=> let G' := context G[q] in change G' in H
| context G[sig_of_sig2 (@exist2 ?A ?P ?Q ?x ?p ?q)]
=> let G' := context G[@exist A P x p] in change G' in H
| context G[sigT_of_sigT2 (@existT2 ?A ?P ?Q ?x ?p ?q)]
=> let G' := context G[@existT A P x p] in change G' in H
end.
Ltac induction_sigma_in_using H rect :=
let H0 := fresh H in
let H1 := fresh H in
induction H as [H0 H1] using (rect _ _ _ _);
simpl_proj_exist_in H0;
simpl_proj_exist_in H1.
Ltac induction_sigma2_in_using H rect :=
let H0 := fresh H in
let H1 := fresh H in
let H2 := fresh H in
induction H as [H0 H1 H2] using (rect _ _ _ _ _);
simpl_proj_exist_in H0;
simpl_proj_exist_in H1;
simpl_proj_exist_in H2.
Ltac inversion_sigma_step :=
match goal with
| [ H : _ = exist _ _ _ |- _ ]
=> induction_sigma_in_using H @eq_sig_rect
| [ H : _ = existT _ _ _ |- _ ]
=> induction_sigma_in_using H @eq_sigT_rect
| [ H : exist _ _ _ = _ |- _ ]
=> induction_sigma_in_using H @eq_sig_rect
| [ H : existT _ _ _ = _ |- _ ]
=> induction_sigma_in_using H @eq_sigT_rect
| [ H : _ = exist2 _ _ _ _ _ |- _ ]
=> induction_sigma2_in_using H @eq_sig2_rect
| [ H : _ = existT2 _ _ _ _ _ |- _ ]
=> induction_sigma2_in_using H @eq_sigT2_rect
| [ H : exist2 _ _ _ _ _ = _ |- _ ]
=> induction_sigma_in_using H @eq_sig2_rect
| [ H : existT2 _ _ _ _ _ = _ |- _ ]
=> induction_sigma_in_using H @eq_sigT2_rect
end.
Ltac inversion_sigma := repeat inversion_sigma_step.
