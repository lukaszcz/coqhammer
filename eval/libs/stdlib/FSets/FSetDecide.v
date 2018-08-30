From Hammer Require Import Hammer.

















Require Import Decidable Setoid DecidableTypeEx FSetFacts.



Module WDecide_fun (E : DecidableType)(Import M : WSfun E).
Module F := FSetFacts.WFacts_fun E M.




Module FSetLogicalFacts.
Export Decidable.
Export Setoid.







Tactic Notation "fold" "any" "not" :=
repeat (
match goal with
| H: context [?P -> False] |- _ =>
fold (~ P) in H
| |- context [?P -> False] =>
fold (~ P)
end).



Ltac or_not_l_iff P Q tac :=
(rewrite (or_not_l_iff_1 P Q) by tac) ||
(rewrite (or_not_l_iff_2 P Q) by tac).

Ltac or_not_r_iff P Q tac :=
(rewrite (or_not_r_iff_1 P Q) by tac) ||
(rewrite (or_not_r_iff_2 P Q) by tac).

Ltac or_not_l_iff_in P Q H tac :=
(rewrite (or_not_l_iff_1 P Q) in H by tac) ||
(rewrite (or_not_l_iff_2 P Q) in H by tac).

Ltac or_not_r_iff_in P Q H tac :=
(rewrite (or_not_r_iff_1 P Q) in H by tac) ||
(rewrite (or_not_r_iff_2 P Q) in H by tac).

Tactic Notation "push" "not" "using" ident(db) :=
let dec := solve_decidable using db in
unfold not, iff;
repeat (
match goal with
| |- context [True -> False] => rewrite not_true_iff
| |- context [False -> False] => rewrite not_false_iff
| |- context [(?P -> False) -> False] => rewrite (not_not_iff P) by dec
| |- context [(?P -> False) -> (?Q -> False)] =>
rewrite (contrapositive P Q) by dec
| |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
| |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
| |- context [(?P -> False) -> ?Q] => rewrite (imp_not_l P Q) by dec
| |- context [?P \/ ?Q -> False] => rewrite (not_or_iff P Q)
| |- context [?P /\ ?Q -> False] => rewrite (not_and_iff P Q)
| |- context [(?P -> ?Q) -> False] => rewrite (not_imp_iff P Q) by dec
end);
fold any not.

Tactic Notation "push" "not" :=
push not using core.

Tactic Notation
"push" "not" "in" "*" "|-" "using" ident(db) :=
let dec := solve_decidable using db in
unfold not, iff in * |-;
repeat (
match goal with
| H: context [True -> False] |- _ => rewrite not_true_iff in H
| H: context [False -> False] |- _ => rewrite not_false_iff in H
| H: context [(?P -> False) -> False] |- _ =>
rewrite (not_not_iff P) in H by dec
| H: context [(?P -> False) -> (?Q -> False)] |- _ =>
rewrite (contrapositive P Q) in H by dec
| H: context [(?P -> False) \/ ?Q] |- _ => or_not_l_iff_in P Q H dec
| H: context [?P \/ (?Q -> False)] |- _ => or_not_r_iff_in P Q H dec
| H: context [(?P -> False) -> ?Q] |- _ =>
rewrite (imp_not_l P Q) in H by dec
| H: context [?P \/ ?Q -> False] |- _ => rewrite (not_or_iff P Q) in H
| H: context [?P /\ ?Q -> False] |- _ => rewrite (not_and_iff P Q) in H
| H: context [(?P -> ?Q) -> False] |- _ =>
rewrite (not_imp_iff P Q) in H by dec
end);
fold any not.

Tactic Notation "push" "not" "in" "*" "|-"  :=
push not in * |- using core.

Tactic Notation "push" "not" "in" "*" "using" ident(db) :=
push not using db; push not in * |- using db.
Tactic Notation "push" "not" "in" "*" :=
push not in * using core.


Lemma test_push : forall P Q R : Prop,
decidable P ->
decidable Q ->
(~ True) ->
(~ False) ->
(~ ~ P) ->
(~ (P /\ Q) -> ~ R) ->
((P /\ Q) \/ ~ R) ->
(~ (P /\ Q) \/ R) ->
(R \/ ~ (P /\ Q)) ->
(~ R \/ (P /\ Q)) ->
(~ P -> R) ->
(~ ((R -> P) \/ (Q -> R))) ->
(~ (P /\ R)) ->
(~ (P -> R)) ->
True.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetLogicalFacts.test_push".  
intros. push not in *.

tauto.
Qed.



Tactic Notation "pull" "not" "using" ident(db) :=
let dec := solve_decidable using db in
unfold not, iff;
repeat (
match goal with
| |- context [True -> False] => rewrite not_true_iff
| |- context [False -> False] => rewrite not_false_iff
| |- context [(?P -> False) -> False] => rewrite (not_not_iff P) by dec
| |- context [(?P -> False) -> (?Q -> False)] =>
rewrite (contrapositive P Q) by dec
| |- context [(?P -> False) \/ ?Q] => or_not_l_iff P Q dec
| |- context [?P \/ (?Q -> False)] => or_not_r_iff P Q dec
| |- context [(?P -> False) -> ?Q] => rewrite (imp_not_l P Q) by dec
| |- context [(?P -> False) /\ (?Q -> False)] =>
rewrite <- (not_or_iff P Q)
| |- context [?P -> ?Q -> False] => rewrite <- (not_and_iff P Q)
| |- context [?P /\ (?Q -> False)] => rewrite <- (not_imp_iff P Q) by dec
| |- context [(?Q -> False) /\ ?P] =>
rewrite <- (not_imp_rev_iff P Q) by dec
end);
fold any not.

Tactic Notation "pull" "not" :=
pull not using core.

Tactic Notation
"pull" "not" "in" "*" "|-" "using" ident(db) :=
let dec := solve_decidable using db in
unfold not, iff in * |-;
repeat (
match goal with
| H: context [True -> False] |- _ => rewrite not_true_iff in H
| H: context [False -> False] |- _ => rewrite not_false_iff in H
| H: context [(?P -> False) -> False] |- _ =>
rewrite (not_not_iff P) in H by dec
| H: context [(?P -> False) -> (?Q -> False)] |- _ =>
rewrite (contrapositive P Q) in H by dec
| H: context [(?P -> False) \/ ?Q] |- _ => or_not_l_iff_in P Q H dec
| H: context [?P \/ (?Q -> False)] |- _ => or_not_r_iff_in P Q H dec
| H: context [(?P -> False) -> ?Q] |- _ =>
rewrite (imp_not_l P Q) in H by dec
| H: context [(?P -> False) /\ (?Q -> False)] |- _ =>
rewrite <- (not_or_iff P Q) in H
| H: context [?P -> ?Q -> False] |- _ =>
rewrite <- (not_and_iff P Q) in H
| H: context [?P /\ (?Q -> False)] |- _ =>
rewrite <- (not_imp_iff P Q) in H by dec
| H: context [(?Q -> False) /\ ?P] |- _ =>
rewrite <- (not_imp_rev_iff P Q) in H by dec
end);
fold any not.

Tactic Notation "pull" "not" "in" "*" "|-"  :=
pull not in * |- using core.

Tactic Notation "pull" "not" "in" "*" "using" ident(db) :=
pull not using db; pull not in * |- using db.
Tactic Notation "pull" "not" "in" "*" :=
pull not in * using core.


Lemma test_pull : forall P Q R : Prop,
decidable P ->
decidable Q ->
(~ True) ->
(~ False) ->
(~ ~ P) ->
(~ (P /\ Q) -> ~ R) ->
((P /\ Q) \/ ~ R) ->
(~ (P /\ Q) \/ R) ->
(R \/ ~ (P /\ Q)) ->
(~ R \/ (P /\ Q)) ->
(~ P -> R) ->
(~ (R -> P) /\ ~ (Q -> R)) ->
(~ P \/ ~ R) ->
(P /\ ~ R) ->
(~ R /\ P) ->
True.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetLogicalFacts.test_pull".  
intros. pull not in *. tauto.
Qed.

End FSetLogicalFacts.
Import FSetLogicalFacts.


Module FSetDecideAuxiliary.





Ltac no_logical_interdep :=
match goal with
| H : ?P |- _ =>
match type of P with
| Prop =>
match goal with H' : context [ H ] |- _ => clear dependent H' end
| _ => fail
end; no_logical_interdep
| _ => idtac
end.

Ltac abstract_term t :=
tryif (is_var t) then fail "no need to abstract a variable"
else (let x := fresh "x" in set (x := t) in *; try clearbody x).

Ltac abstract_elements :=
repeat
(match goal with
| |- context [ singleton ?t ] => abstract_term t
| _ : context [ singleton ?t ] |- _ => abstract_term t
| |- context [ add ?t _ ] => abstract_term t
| _ : context [ add ?t _ ] |- _ => abstract_term t
| |- context [ remove ?t _ ] => abstract_term t
| _ : context [ remove ?t _ ] |- _ => abstract_term t
| |- context [ In ?t _ ] => abstract_term t
| _ : context [ In ?t _ ] |- _ => abstract_term t
end).


Tactic Notation "prop" constr(P) "holds" "by" tactic(t) :=
let H := fresh in
assert P as H by t;
clear H.


Tactic Notation "assert" "new" constr(e) "by" tactic(t) :=
match goal with
| H: e |- _ => fail 1
| _ => assert e by t
end.


Tactic Notation "subst" "++" :=
repeat (
match goal with
| x : _ |- _ => subst x
end);
cbv zeta beta in *.


Tactic Notation "decompose" "records" :=
repeat (
match goal with
| H: _ |- _ => progress (decompose record H); clear H
end).



Inductive FSet_elt_Prop : Prop -> Prop :=
| eq_Prop : forall (S : Type) (x y : S),
FSet_elt_Prop (x = y)
| eq_elt_prop : forall x y,
FSet_elt_Prop (E.eq x y)
| In_elt_prop : forall x s,
FSet_elt_Prop (In x s)
| True_elt_prop :
FSet_elt_Prop True
| False_elt_prop :
FSet_elt_Prop False
| conj_elt_prop : forall P Q,
FSet_elt_Prop P ->
FSet_elt_Prop Q ->
FSet_elt_Prop (P /\ Q)
| disj_elt_prop : forall P Q,
FSet_elt_Prop P ->
FSet_elt_Prop Q ->
FSet_elt_Prop (P \/ Q)
| impl_elt_prop : forall P Q,
FSet_elt_Prop P ->
FSet_elt_Prop Q ->
FSet_elt_Prop (P -> Q)
| not_elt_prop : forall P,
FSet_elt_Prop P ->
FSet_elt_Prop (~ P).

Inductive FSet_Prop : Prop -> Prop :=
| elt_FSet_Prop : forall P,
FSet_elt_Prop P ->
FSet_Prop P
| Empty_FSet_Prop : forall s,
FSet_Prop (Empty s)
| Subset_FSet_Prop : forall s1 s2,
FSet_Prop (Subset s1 s2)
| Equal_FSet_Prop : forall s1 s2,
FSet_Prop (Equal s1 s2).


Hint Constructors FSet_elt_Prop FSet_Prop : FSet_Prop.
Ltac discard_nonFSet :=
repeat (
match goal with
| H : context [ @Logic.eq ?T ?x ?y ] |- _ =>
tryif (change T with E.t in H) then fail
else tryif (change T with t in H) then fail
else clear H
| H : ?P |- _ =>
tryif prop (FSet_Prop P) holds by
(auto 100 with FSet_Prop)
then fail
else clear H
end).



Hint Rewrite
F.empty_iff F.singleton_iff F.add_iff F.remove_iff
F.union_iff F.inter_iff F.diff_iff
: set_simpl.

Lemma eq_refl_iff (x : E.t) : E.eq x x <-> True.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideAuxiliary.eq_refl_iff".  
now split.
Qed.

Hint Rewrite eq_refl_iff : set_eq_simpl.




Lemma dec_In : forall x s,
decidable (In x s).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideAuxiliary.dec_In".  
red; intros; generalize (F.mem_iff s x); case (mem x s); intuition.
Qed.


Lemma dec_eq : forall (x y : E.t),
decidable (E.eq x y).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideAuxiliary.dec_eq".  
red; intros x y; destruct (E.eq_dec x y); auto.
Qed.


Hint Resolve dec_In dec_eq : FSet_decidability.




Ltac change_to_E_t :=
repeat (
match goal with
| H : ?T |- _ =>
progress (change T with E.t in H);
repeat (
match goal with
| J : _ |- _ => progress (change T with E.t in J)
| |- _ => progress (change T with E.t)
end )
| H : forall x : ?T, _ |- _ =>
progress (change T with E.t in H);
repeat (
match goal with
| J : _ |- _ => progress (change T with E.t in J)
| |- _ => progress (change T with E.t)
end )
end).



Ltac Logic_eq_to_E_eq :=
repeat (
match goal with
| H: _ |- _ =>
progress (change (@Logic.eq E.t) with E.eq in H)
| |- _ =>
progress (change (@Logic.eq E.t) with E.eq)
end).

Ltac E_eq_to_Logic_eq :=
repeat (
match goal with
| H: _ |- _ =>
progress (change E.eq with (@Logic.eq E.t) in H)
| |- _ =>
progress (change E.eq with (@Logic.eq E.t))
end).


Ltac substFSet :=
repeat (
match goal with
| H: E.eq ?x ?x |- _ => clear H
| H: E.eq ?x ?y |- _ => rewrite H in *; clear H
end);
autorewrite with set_eq_simpl in *.


Ltac assert_decidability :=

repeat (
match goal with
| H: context [~ E.eq ?x ?y] |- _ =>
assert new (E.eq x y \/ ~ E.eq x y) by (apply dec_eq)
| H: context [~ In ?x ?s] |- _ =>
assert new (In x s \/ ~ In x s) by (apply dec_In)
| |- context [~ E.eq ?x ?y] =>
assert new (E.eq x y \/ ~ E.eq x y) by (apply dec_eq)
| |- context [~ In ?x ?s] =>
assert new (In x s \/ ~ In x s) by (apply dec_In)
end);

repeat (
match goal with
| _: ~ ?P, H : ?P \/ ~ ?P |- _ => clear H
end).


Ltac inst_FSet_hypotheses :=
repeat (
match goal with
| H : forall a : E.t, _,
_ : context [ In ?x _ ] |- _ =>
let P := type of (H x) in
assert new P by (exact (H x))
| H : forall a : E.t, _
|- context [ In ?x _ ] =>
let P := type of (H x) in
assert new P by (exact (H x))
| H : forall a : E.t, _,
_ : context [ E.eq ?x _ ] |- _ =>
let P := type of (H x) in
assert new P by (exact (H x))
| H : forall a : E.t, _
|- context [ E.eq ?x _ ] =>
let P := type of (H x) in
assert new P by (exact (H x))
| H : forall a : E.t, _,
_ : context [ E.eq _ ?x ] |- _ =>
let P := type of (H x) in
assert new P by (exact (H x))
| H : forall a : E.t, _
|- context [ E.eq _ ?x ] =>
let P := type of (H x) in
assert new P by (exact (H x))
end);
repeat (
match goal with
| H : forall a : E.t, _ |- _ =>
clear H
end).




Ltac fsetdec_rec := progress substFSet; intuition fsetdec_rec.


Ltac fsetdec_body :=
autorewrite with set_eq_simpl in *;
inst_FSet_hypotheses;
autorewrite with set_simpl set_eq_simpl in *;
push not in * using FSet_decidability;
substFSet;
assert_decidability;
auto;
(intuition fsetdec_rec) ||
fail 1
"because the goal is beyond the scope of this tactic".

End FSetDecideAuxiliary.
Import FSetDecideAuxiliary.


Ltac fsetdec :=

unfold iff in *;

fold any not; intros;

abstract_elements;

no_logical_interdep;

decompose records;
discard_nonFSet;

unfold Empty, Subset, Equal in *; intros;

change_to_E_t; E_eq_to_Logic_eq; subst++; Logic_eq_to_E_eq;

pull not using FSet_decidability;
unfold not in *;
match goal with
| H: (In ?x ?r) -> False |- (In ?x ?s) -> False =>
contradict H; fsetdec_body
| H: (In ?x ?r) -> False |- (E.eq ?x ?y) -> False =>
contradict H; fsetdec_body
| H: (In ?x ?r) -> False |- (E.eq ?y ?x) -> False =>
contradict H; fsetdec_body
| H: ?P -> False |- ?Q -> False =>
tryif prop (FSet_elt_Prop P) holds by
(auto 100 with FSet_Prop)
then (contradict H; fsetdec_body)
else fsetdec_body
| |- _ =>
fsetdec_body
end.



Module FSetDecideTestCases.

Lemma test_eq_trans_1 : forall x y z s,
E.eq x y ->
~ ~ E.eq z y ->
In x s ->
In z s.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_eq_trans_1".   fsetdec. Qed.

Lemma test_eq_trans_2 : forall x y z r s,
In x (singleton y) ->
~ In z r ->
~ ~ In z (add y r) ->
In x s ->
In z s.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_eq_trans_2".   fsetdec. Qed.

Lemma test_eq_neq_trans_1 : forall w x y z s,
E.eq x w ->
~ ~ E.eq x y ->
~ E.eq y z ->
In w s ->
In w (remove z s).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_eq_neq_trans_1".   fsetdec. Qed.

Lemma test_eq_neq_trans_2 : forall w x y z r1 r2 s,
In x (singleton w) ->
~ In x r1 ->
In x (add y r1) ->
In y r2 ->
In y (remove z r2) ->
In w s ->
In w (remove z s).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_eq_neq_trans_2".   fsetdec. Qed.

Lemma test_In_singleton : forall x,
In x (singleton x).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_In_singleton".   fsetdec. Qed.

Lemma test_add_In : forall x y s,
In x (add y s) ->
~ E.eq x y ->
In x s.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_add_In".   fsetdec. Qed.

Lemma test_Subset_add_remove : forall x s,
s [<=] (add x (remove x s)).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_Subset_add_remove".   fsetdec. Qed.

Lemma test_eq_disjunction : forall w x y z,
In w (add x (add y (singleton z))) ->
E.eq w x \/ E.eq w y \/ E.eq w z.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_eq_disjunction".   fsetdec. Qed.

Lemma test_not_In_disj : forall x y s1 s2 s3 s4,
~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
~ (In x s1 \/ In x s4 \/ E.eq y x).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_not_In_disj".   fsetdec. Qed.

Lemma test_not_In_conj : forall x y s1 s2 s3 s4,
~ In x (union s1 (union s2 (union s3 (add y s4)))) ->
~ In x s1 /\ ~ In x s4 /\ ~ E.eq y x.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_not_In_conj".   fsetdec. Qed.

Lemma test_iff_conj : forall a x s s',
(In a s' <-> E.eq x a \/ In a s) ->
(In a s' <-> In a (add x s)).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_iff_conj".   fsetdec. Qed.

Lemma test_set_ops_1 : forall x q r s,
(singleton x) [<=] s ->
Empty (union q r) ->
Empty (inter (diff s q) (diff s r)) ->
~ In x s.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_set_ops_1".   fsetdec. Qed.

Lemma eq_chain_test : forall x1 x2 x3 x4 s1 s2 s3 s4,
Empty s1 ->
In x2 (add x1 s1) ->
In x3 s2 ->
~ In x3 (remove x2 s2) ->
~ In x4 s3 ->
In x4 (add x3 s3) ->
In x1 s4 ->
Subset (add x4 s4) s4.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.eq_chain_test".   fsetdec. Qed.

Lemma test_too_complex : forall x y z r s,
E.eq x y ->
(In x (singleton y) -> r [<=] s) ->
In z r ->
In z s.
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_too_complex".  

intros until s; intros Heq H Hr; lapply H; fsetdec.
Qed.

Lemma function_test_1 :
forall (f : t -> t),
forall (g : elt -> elt),
forall (s1 s2 : t),
forall (x1 x2 : elt),
Equal s1 (f s2) ->
E.eq x1 (g (g x2)) ->
In x1 s1 ->
In (g (g x2)) (f s2).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.function_test_1".   fsetdec. Qed.

Lemma function_test_2 :
forall (f : t -> t),
forall (g : elt -> elt),
forall (s1 s2 : t),
forall (x1 x2 : elt),
Equal s1 (f s2) ->
E.eq x1 (g x2) ->
In x1 s1 ->
g x2 = g (g x2) ->
In (g (g x2)) (f s2).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.function_test_2".  

intros until 3. intros g_eq. rewrite <- g_eq. fsetdec.
Qed.

Lemma test_baydemir :
forall (f : t -> t),
forall (s : t),
forall (x y : elt),
In x (add y (f s)) ->
~ E.eq x y ->
In x (f s).
Proof. hammer_hook "FSetDecide" "FSetDecide.WDecide_fun.FSetDecideTestCases.test_baydemir".  
fsetdec.
Qed.

End FSetDecideTestCases.

End WDecide_fun.

Require Import FSetInterface.



Module WDecide (M:WS) := !WDecide_fun M.E M.
Module Decide := WDecide.
