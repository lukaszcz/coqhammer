From Hammer Require Import Hammer.










Require Import Coq.Program.Utils.
Require Import Coq.Program.Equality.
Require Export ProofIrrelevance.

Local Open Scope program_scope.



Ltac on_subset_proof_aux tac T :=
match T with
| context [ exist ?P _ ?p ] => try on_subset_proof_aux tac P ; tac p
end.

Ltac on_subset_proof tac :=
match goal with
[ |- ?T ] => on_subset_proof_aux tac T
end.

Ltac abstract_any_hyp H' p :=
match type of p with
?X =>
match goal with
| [ H : X |- _ ] => fail 1
| _ => set (H':=p) ; try (change p with H') ; clearbody H'
end
end.

Ltac abstract_subset_proof :=
on_subset_proof ltac:(fun p => let H := fresh "eqH" in abstract_any_hyp H p ; simpl in H).

Ltac abstract_subset_proofs := repeat abstract_subset_proof.

Ltac pi_subset_proof_hyp p :=
match type of p with
?X =>
match goal with
| [ H : X |- _ ] =>
match p with
| H => fail 2
| _ => rewrite (proof_irrelevance X p H)
end
| _ => fail " No hypothesis with same type "
end
end.

Ltac pi_subset_proof := on_subset_proof pi_subset_proof_hyp.

Ltac pi_subset_proofs := repeat pi_subset_proof.



Ltac clear_subset_proofs :=
abstract_subset_proofs ; simpl in * |- ; pi_subset_proofs ; clear_dups.

Ltac pi := repeat f_equal ; apply proof_irrelevance.

Lemma subset_eq : forall A (P : A -> Prop) (n m : sig P), n = m <-> `n = `m.
Proof. hammer_hook "Subset" "Subset.subset_eq". Restart. 
destruct n as (x,p).
destruct m as (x',p').
simpl.
split ; intros ; subst.

inversion H.
reflexivity.

pi.
Qed.



Definition match_eq (A B : Type) (x : A) (fn : {y : A | y = x} -> B) : B :=
fn (exist _ x eq_refl).



Lemma match_eq_rewrite : forall (A B : Type) (x : A) (fn : {y : A | y = x} -> B)
(y : {y:A | y = x}),
match_eq A B x fn = fn y.
Proof. hammer_hook "Subset" "Subset.match_eq_rewrite". Restart. 
intros.
unfold match_eq.
f_equal.
destruct y.

apply <- subset_eq.
symmetry. assumption.
Qed.



Ltac rewrite_match_eq H :=
match goal with
[ |- ?T ] =>
match T with
context [ match_eq ?A ?B ?t ?f ] =>
rewrite (match_eq_rewrite A B t f (exist _ _ (eq_sym H)))
end
end.



Ltac simpl_match_eq := unfold match_eq ; simpl.
