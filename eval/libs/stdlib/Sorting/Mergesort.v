From Hammer Require Import Hammer.













Require Import List Setoid Permutation Sorted Orders.



Local Notation "[ ]" := nil.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..).

Open Scope bool_scope.

Local Coercion is_true : bool >-> Sortclass.



Module Sort (Import X:Orders.TotalLeBool').

Fixpoint merge l1 l2 :=
let fix merge_aux l2 :=
match l1, l2 with
| [], _ => l2
| _, [] => l1
| a1::l1', a2::l2' =>
if a1 <=? a2 then a1 :: merge l1' l2 else a2 :: merge_aux l2'
end
in merge_aux l2.



Fixpoint merge_list_to_stack stack l :=
match stack with
| [] => [Some l]
| None :: stack' => Some l :: stack'
| Some l' :: stack' => None :: merge_list_to_stack stack' (merge l' l)
end.

Fixpoint merge_stack stack :=
match stack with
| [] => []
| None :: stack' => merge_stack stack'
| Some l :: stack' => merge l (merge_stack stack')
end.

Fixpoint iter_merge stack l :=
match l with
| [] => merge_stack stack
| a::l' => iter_merge (merge_list_to_stack stack [a]) l'
end.

Definition sort := iter_merge [].



Local Notation Sorted := (LocallySorted leb) (only parsing).

Fixpoint SortedStack stack :=
match stack with
| [] => True
| None :: stack' => SortedStack stack'
| Some l :: stack' => Sorted l /\ SortedStack stack'
end.

Local Ltac invert H := inversion H; subst; clear H.

Fixpoint flatten_stack (stack : list (option (list t))) :=
match stack with
| [] => []
| None :: stack' => flatten_stack stack'
| Some l :: stack' => l ++ flatten_stack stack'
end.

Theorem Sorted_merge : forall l1 l2,
Sorted l1 -> Sorted l2 -> Sorted (merge l1 l2).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Sorted_merge". Undo.  
induction l1; induction l2; intros; simpl; auto.
destruct (a <=? a0) eqn:Heq1.
invert H.
simpl. constructor; trivial; rewrite Heq1; constructor.
assert (Sorted (merge (b::l) (a0::l2))) by (apply IHl1; auto).
clear H0 H3 IHl1; simpl in *.
destruct (b <=? a0); constructor; auto || rewrite Heq1; constructor.
assert (a0 <=? a) by
(destruct (leb_total a0 a) as [H'|H']; trivial || (rewrite Heq1 in H'; inversion H')).
invert H0.
constructor; trivial.
assert (Sorted (merge (a::l1) (b::l))) by auto using IHl1.
clear IHl2; simpl in *.
destruct (a <=? b); constructor; auto.
Qed.

Theorem Permuted_merge : forall l1 l2, Permutation (l1++l2) (merge l1 l2).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Permuted_merge". Undo.  
induction l1; simpl merge; intro.
assert (forall l, (fix merge_aux (l0 : list t) : list t := l0) l = l)
as -> by (destruct l; trivial).
apply Permutation_refl.
induction l2.
rewrite app_nil_r. apply Permutation_refl.
destruct (a <=? a0).
constructor; apply IHl1.
apply Permutation_sym, Permutation_cons_app, Permutation_sym, IHl2.
Qed.

Theorem Sorted_merge_list_to_stack : forall stack l,
SortedStack stack -> Sorted l -> SortedStack (merge_list_to_stack stack l).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Sorted_merge_list_to_stack". Undo.  
induction stack as [|[|]]; intros; simpl.
auto.
apply IHstack. destruct H as (_,H1). fold SortedStack in H1. auto.
apply Sorted_merge; auto; destruct H; auto.
auto.
Qed.

Theorem Permuted_merge_list_to_stack : forall stack l,
Permutation (l ++ flatten_stack stack) (flatten_stack (merge_list_to_stack stack l)).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Permuted_merge_list_to_stack". Undo.  
induction stack as [|[]]; simpl; intros.
reflexivity.
rewrite app_assoc.
etransitivity.
apply Permutation_app_tail.
etransitivity.
apply Permutation_app_comm.
apply Permuted_merge.
apply IHstack.
reflexivity.
Qed.

Theorem Sorted_merge_stack : forall stack,
SortedStack stack -> Sorted (merge_stack stack).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Sorted_merge_stack". Undo.  
induction stack as [|[|]]; simpl; intros.
constructor; auto.
apply Sorted_merge; tauto.
auto.
Qed.

Theorem Permuted_merge_stack : forall stack,
Permutation (flatten_stack stack) (merge_stack stack).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Permuted_merge_stack". Undo.  
induction stack as [|[]]; simpl.
trivial.
transitivity (l ++ merge_stack stack).
apply Permutation_app_head; trivial.
apply Permuted_merge.
assumption.
Qed.

Theorem Sorted_iter_merge : forall stack l,
SortedStack stack -> Sorted (iter_merge stack l).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Sorted_iter_merge". Undo.  
intros stack l H; induction l in stack, H |- *; simpl.
auto using Sorted_merge_stack.
assert (Sorted [a]) by constructor.
auto using Sorted_merge_list_to_stack.
Qed.

Theorem Permuted_iter_merge : forall l stack,
Permutation (flatten_stack stack ++ l) (iter_merge stack l).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Permuted_iter_merge". Undo.  
induction l; simpl; intros.
rewrite app_nil_r. apply Permuted_merge_stack.
change (a::l) with ([a]++l).
rewrite app_assoc.
etransitivity.
apply Permutation_app_tail.
etransitivity.
apply Permutation_app_comm.
apply Permuted_merge_list_to_stack.
apply IHl.
Qed.

Theorem Sorted_sort : forall l, Sorted (sort l).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Sorted_sort". Undo.  
intro; apply Sorted_iter_merge. constructor.
Qed.

Corollary LocallySorted_sort : forall l, Sorted.Sorted leb (sort l).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.LocallySorted_sort". Undo.   intro; eapply Sorted_LocallySorted_iff, Sorted_sort; auto. Qed.

Theorem Permuted_sort : forall l, Permutation l (sort l).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.Permuted_sort". Undo.  
intro; apply (Permuted_iter_merge l []).
Qed.

Corollary StronglySorted_sort : forall l,
Transitive leb -> StronglySorted leb (sort l).
Proof. try hammer_hook "Mergesort" "Mergesort.Sort.StronglySorted_sort". Undo.   auto using Sorted_StronglySorted, LocallySorted_sort. Qed.

End Sort.



Module NatOrder <: TotalLeBool.
Definition t := nat.
Fixpoint leb x y :=
match x, y with
| 0, _ => true
| _, 0 => false
| S x', S y' => leb x' y'
end.
Infix "<=?" := leb (at level 35).
Theorem leb_total : forall a1 a2, a1 <=? a2 \/ a2 <=? a1.
Proof. try hammer_hook "Mergesort" "Mergesort.NatOrder.leb_total". Undo.  
induction a1; destruct a2; simpl; auto.
Qed.
End NatOrder.

Module Import NatSort := Sort NatOrder.

Example SimpleMergeExample := Eval compute in sort [5;3;6;1;8;6;0].

