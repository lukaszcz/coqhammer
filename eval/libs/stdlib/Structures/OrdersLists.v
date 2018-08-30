From Hammer Require Import Hammer.









Require Export RelationPairs SetoidList Orders EqualitiesFacts.

Set Implicit Arguments.
Unset Strict Implicit.



Module OrderedTypeLists (O:OrderedType).

Local Notation In:=(InA O.eq).
Local Notation Inf:=(lelistA O.lt).
Local Notation Sort:=(sort O.lt).
Local Notation NoDup:=(NoDupA O.eq).

Lemma In_eq : forall l x y, eq x y -> In x l -> In y l.
Proof. hammer_hook "OrdersLists" "OrdersLists.OrderedTypeLists.In_eq".   intros. rewrite <- H; auto. Qed.

Lemma ListIn_In : forall l x, List.In x l -> In x l.
Proof. hammer_hook "OrdersLists" "OrdersLists.OrderedTypeLists.ListIn_In".   exact (In_InA O.eq_equiv). Qed.

Lemma Inf_lt : forall l x y, O.lt x y -> Inf y l -> Inf x l.
Proof. hammer_hook "OrdersLists" "OrdersLists.OrderedTypeLists.Inf_lt".   exact (InfA_ltA O.lt_strorder). Qed.

Lemma Inf_eq : forall l x y, O.eq x y -> Inf y l -> Inf x l.
Proof. hammer_hook "OrdersLists" "OrdersLists.OrderedTypeLists.Inf_eq".   exact (InfA_eqA O.eq_equiv O.lt_compat). Qed.

Lemma Sort_Inf_In : forall l x a, Sort l -> Inf a l -> In x l -> O.lt a x.
Proof. hammer_hook "OrdersLists" "OrdersLists.OrderedTypeLists.Sort_Inf_In".   exact (SortA_InfA_InA O.eq_equiv O.lt_strorder O.lt_compat). Qed.

Lemma ListIn_Inf : forall l x, (forall y, List.In y l -> O.lt x y) -> Inf x l.
Proof. hammer_hook "OrdersLists" "OrdersLists.OrderedTypeLists.ListIn_Inf".   exact (@In_InfA O.t O.lt). Qed.

Lemma In_Inf : forall l x, (forall y, In y l -> O.lt x y) -> Inf x l.
Proof. hammer_hook "OrdersLists" "OrdersLists.OrderedTypeLists.In_Inf".   exact (InA_InfA O.eq_equiv (ltA:=O.lt)). Qed.

Lemma Inf_alt :
forall l x, Sort l -> (Inf x l <-> (forall y, In y l -> O.lt x y)).
Proof. hammer_hook "OrdersLists" "OrdersLists.OrderedTypeLists.Inf_alt".   exact (InfA_alt O.eq_equiv O.lt_strorder O.lt_compat). Qed.

Lemma Sort_NoDup : forall l, Sort l -> NoDup l.
Proof. hammer_hook "OrdersLists" "OrdersLists.OrderedTypeLists.Sort_NoDup".   exact (SortA_NoDupA O.eq_equiv O.lt_strorder O.lt_compat) . Qed.

Hint Resolve ListIn_In Sort_NoDup Inf_lt.
Hint Immediate In_eq Inf_lt.

End OrderedTypeLists.




Module KeyOrderedType(O:OrderedType).
Include KeyDecidableType(O).

Local Notation key:=O.t.
Local Open Scope signature_scope.

Definition ltk {elt} : relation (key*elt) := O.lt @@1.

Hint Unfold ltk.



Instance ltk_strorder {elt} : StrictOrder (@ltk elt) := _.

Instance ltk_compat {elt} : Proper (eqk==>eqk==>iff) (@ltk elt).
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.ltk_compat".   unfold eqk, ltk; auto with *. Qed.

Instance ltk_compat' {elt} : Proper (eqke==>eqke==>iff) (@ltk elt).
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.ltk_compat'".   eapply subrelation_proper; eauto with *. Qed.



Instance pair_compat {elt} : Proper (O.eq==>Logic.eq==>eqke) (@pair key elt).
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.pair_compat".   apply pair_compat. Qed.

Section Elt.
Variable elt : Type.
Implicit Type p q : key*elt.
Implicit Type l m : list (key*elt).

Lemma ltk_not_eqk p q : ltk p q -> ~ eqk p q.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.ltk_not_eqk".  
intros LT EQ; rewrite EQ in LT.
elim (StrictOrder_Irreflexive _ LT).
Qed.

Lemma ltk_not_eqke p q : ltk p q -> ~eqke p q.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.ltk_not_eqke".  
intros LT EQ; rewrite EQ in LT.
elim (StrictOrder_Irreflexive _ LT).
Qed.

Notation Sort := (sort ltk).
Notation Inf := (lelistA ltk).

Lemma Inf_eq l x x' : eqk x x' -> Inf x' l -> Inf x l.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.Inf_eq".   now intros <-. Qed.

Lemma Inf_lt l x x' : ltk x x' -> Inf x' l -> Inf x l.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.Inf_lt".   apply InfA_ltA; auto with *. Qed.

Hint Immediate Inf_eq.
Hint Resolve Inf_lt.

Lemma Sort_Inf_In l p q : Sort l -> Inf q l -> InA eqk p l -> ltk q p.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.Sort_Inf_In".   apply SortA_InfA_InA; auto with *. Qed.

Lemma Sort_Inf_NotIn l k e : Sort l -> Inf (k,e) l ->  ~In k l.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.Sort_Inf_NotIn".  
intros; red; intros.
destruct H1 as [e' H2].
elim (@ltk_not_eqk (k,e) (k,e')).
eapply Sort_Inf_In; eauto.
repeat red; reflexivity.
Qed.

Lemma Sort_NoDupA l : Sort l -> NoDupA eqk l.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.Sort_NoDupA".   apply SortA_NoDupA; auto with *. Qed.

Lemma Sort_In_cons_1 l p q : Sort (p::l) -> InA eqk q l -> ltk p q.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.Sort_In_cons_1".  
intros; invlist sort; eapply Sort_Inf_In; eauto.
Qed.

Lemma Sort_In_cons_2 l p q : Sort (p::l) -> InA eqk q (p::l) ->
ltk p q \/ eqk p q.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.Sort_In_cons_2".  
intros; invlist InA; auto with relations.
left; apply Sort_In_cons_1 with l; auto with relations.
Qed.

Lemma Sort_In_cons_3 x l k e :
Sort ((k,e)::l) -> In x l -> ~O.eq x k.
Proof. hammer_hook "OrdersLists" "OrdersLists.KeyOrderedType.Sort_In_cons_3".  
intros; invlist sort; red; intros.
eapply Sort_Inf_NotIn; eauto using In_eq.
Qed.

End Elt.

Hint Resolve ltk_not_eqk ltk_not_eqke.
Hint Immediate Inf_eq.
Hint Resolve Inf_lt.
Hint Resolve Sort_Inf_NotIn.

End KeyOrderedType.

