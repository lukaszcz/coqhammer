From Hammer Require Import Hammer.









Require Import Arith.
Require Import Bool.

Local Open Scope nat_scope.

Definition zerob (n:nat) : bool :=
match n with
| O => true
| S _ => false
end.

Lemma zerob_true_intro : forall n:nat, n = 0 -> zerob n = true.
Proof. hammer_hook "Zerob" "Zerob.zerob_true_intro". Restart. 
destruct n; [ trivial with bool | inversion 1 ].
Qed.
Hint Resolve zerob_true_intro: bool.

Lemma zerob_true_elim : forall n:nat, zerob n = true -> n = 0.
Proof. hammer_hook "Zerob" "Zerob.zerob_true_elim". Restart. 
destruct n; [ trivial with bool | inversion 1 ].
Qed.

Lemma zerob_false_intro : forall n:nat, n <> 0 -> zerob n = false.
Proof. hammer_hook "Zerob" "Zerob.zerob_false_intro". Restart. 
destruct n; [ destruct 1; auto with bool | trivial with bool ].
Qed.
Hint Resolve zerob_false_intro: bool.

Lemma zerob_false_elim : forall n:nat, zerob n = false -> n <> 0.
Proof. hammer_hook "Zerob" "Zerob.zerob_false_elim". Restart. 
destruct n; [ inversion 1 | auto with bool ].
Qed.
