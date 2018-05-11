From Hammer Require Import Hammer.













Require Export Bool SetoidList RelationClasses Morphisms
RelationPairs Equalities Orders OrdersFacts.
Set Implicit Arguments.
Unset Strict Implicit.

Module Type TypElt.
Parameters t elt : Type.
End TypElt.

Module Type HasWOps (Import T:TypElt).

Parameter empty : t.


Parameter is_empty : t -> bool.


Parameter mem : elt -> t -> bool.


Parameter add : elt -> t -> t.


Parameter singleton : elt -> t.


Parameter remove : elt -> t -> t.


Parameter union : t -> t -> t.


Parameter inter : t -> t -> t.


Parameter diff : t -> t -> t.


Parameter equal : t -> t -> bool.


Parameter subset : t -> t -> bool.


Parameter fold : forall A : Type, (elt -> A -> A) -> t -> A -> A.


Parameter for_all : (elt -> bool) -> t -> bool.


Parameter exists_ : (elt -> bool) -> t -> bool.


Parameter filter : (elt -> bool) -> t -> t.


Parameter partition : (elt -> bool) -> t -> t * t.


Parameter cardinal : t -> nat.


Parameter elements : t -> list elt.


Parameter choose : t -> option elt.


End HasWOps.

Module Type WOps (E : DecidableType).
Definition elt := E.t.
Parameter t : Type.
Include HasWOps.
End WOps.




Module Type WSetsOn (E : DecidableType).

Include WOps E.


Parameter In : elt -> t -> Prop.
Declare Instance In_compat : Proper (E.eq==>eq==>iff) In.

Definition Equal s s' := forall a : elt, In a s <-> In a s'.
Definition Subset s s' := forall a : elt, In a s -> In a s'.
Definition Empty s := forall a : elt, ~ In a s.
Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

Notation "s  [=]  t" := (Equal s t) (at level 70, no associativity).
Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

Definition eq : t -> t -> Prop := Equal.
Include IsEq.
Include HasEqDec.



Section Spec.
Variable s s': t.
Variable x y : elt.
Variable f : elt -> bool.
Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

Parameter mem_spec : mem x s = true <-> In x s.
Parameter equal_spec : equal s s' = true <-> s[=]s'.
Parameter subset_spec : subset s s' = true <-> s[<=]s'.
Parameter empty_spec : Empty empty.
Parameter is_empty_spec : is_empty s = true <-> Empty s.
Parameter add_spec : In y (add x s) <-> E.eq y x \/ In y s.
Parameter remove_spec : In y (remove x s) <-> In y s /\ ~E.eq y x.
Parameter singleton_spec : In y (singleton x) <-> E.eq y x.
Parameter union_spec : In x (union s s') <-> In x s \/ In x s'.
Parameter inter_spec : In x (inter s s') <-> In x s /\ In x s'.
Parameter diff_spec : In x (diff s s') <-> In x s /\ ~In x s'.
Parameter fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A),
fold f s i = fold_left (flip f) (elements s) i.
Parameter cardinal_spec : cardinal s = length (elements s).
Parameter filter_spec : compatb f ->
(In x (filter f s) <-> In x s /\ f x = true).
Parameter for_all_spec : compatb f ->
(for_all f s = true <-> For_all (fun x => f x = true) s).
Parameter exists_spec : compatb f ->
(exists_ f s = true <-> Exists (fun x => f x = true) s).
Parameter partition_spec1 : compatb f ->
fst (partition f s) [=] filter f s.
Parameter partition_spec2 : compatb f ->
snd (partition f s) [=] filter (fun x => negb (f x)) s.
Parameter elements_spec1 : InA E.eq x (elements s) <-> In x s.

Parameter elements_spec2w : NoDupA E.eq (elements s).
Parameter choose_spec1 : choose s = Some x -> In x s.
Parameter choose_spec2 : choose s = None -> Empty s.

End Spec.

End WSetsOn.



Module Type WSets.
Declare Module E : DecidableType.
Include WSetsOn E.
End WSets.



Module Type HasOrdOps (Import T:TypElt).

Parameter compare : t -> t -> comparison.


Parameter min_elt : t -> option elt.


Parameter max_elt : t -> option elt.


End HasOrdOps.

Module Type Ops (E : OrderedType) := WOps E <+ HasOrdOps.


Module Type SetsOn (E : OrderedType).
Include WSetsOn E <+ HasOrdOps <+ HasLt <+ IsStrOrder.

Section Spec.
Variable s s': t.
Variable x y : elt.

Parameter compare_spec : CompSpec eq lt s s' (compare s s').


Parameter elements_spec2 : sort E.lt (elements s).



Parameter min_elt_spec1 : min_elt s = Some x -> In x s.
Parameter min_elt_spec2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
Parameter min_elt_spec3 : min_elt s = None -> Empty s.

Parameter max_elt_spec1 : max_elt s = Some x -> In x s.
Parameter max_elt_spec2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
Parameter max_elt_spec3 : max_elt s = None -> Empty s.


Parameter choose_spec3 : choose s = Some x -> choose s' = Some y ->
Equal s s' -> E.eq x y.

End Spec.

End SetsOn.




Module Type Sets.
Declare Module E : OrderedType.
Include SetsOn E.
End Sets.

Module Type S := Sets.









Module Type WRawSets (E : DecidableType).

Include WOps E.



Parameter IsOk : t -> Prop.
Class Ok (s:t) : Prop := ok : IsOk s.


Parameter isok : t -> bool.

Declare Instance isok_Ok s `(isok s = true) : Ok s | 10.


Parameter In : elt -> t -> Prop.
Declare Instance In_compat : Proper (E.eq==>eq==>iff) In.

Definition Equal s s' := forall a : elt, In a s <-> In a s'.
Definition Subset s s' := forall a : elt, In a s -> In a s'.
Definition Empty s := forall a : elt, ~ In a s.
Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

Notation "s  [=]  t" := (Equal s t) (at level 70, no associativity).
Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

Definition eq : t -> t -> Prop := Equal.
Declare Instance eq_equiv : Equivalence eq.



Declare Instance empty_ok : Ok empty.
Declare Instance add_ok s x `(Ok s) : Ok (add x s).
Declare Instance remove_ok s x `(Ok s) : Ok (remove x s).
Declare Instance singleton_ok x : Ok (singleton x).
Declare Instance union_ok s s' `(Ok s, Ok s') : Ok (union s s').
Declare Instance inter_ok s s' `(Ok s, Ok s') : Ok (inter s s').
Declare Instance diff_ok s s' `(Ok s, Ok s') : Ok (diff s s').
Declare Instance filter_ok s f `(Ok s) : Ok (filter f s).
Declare Instance partition_ok1 s f `(Ok s) : Ok (fst (partition f s)).
Declare Instance partition_ok2 s f `(Ok s) : Ok (snd (partition f s)).



Section Spec.
Variable s s': t.
Variable x y : elt.
Variable f : elt -> bool.
Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

Parameter mem_spec : forall `{Ok s}, mem x s = true <-> In x s.
Parameter equal_spec : forall `{Ok s, Ok s'},
equal s s' = true <-> s[=]s'.
Parameter subset_spec : forall `{Ok s, Ok s'},
subset s s' = true <-> s[<=]s'.
Parameter empty_spec : Empty empty.
Parameter is_empty_spec : is_empty s = true <-> Empty s.
Parameter add_spec : forall `{Ok s},
In y (add x s) <-> E.eq y x \/ In y s.
Parameter remove_spec : forall `{Ok s},
In y (remove x s) <-> In y s /\ ~E.eq y x.
Parameter singleton_spec : In y (singleton x) <-> E.eq y x.
Parameter union_spec : forall `{Ok s, Ok s'},
In x (union s s') <-> In x s \/ In x s'.
Parameter inter_spec : forall `{Ok s, Ok s'},
In x (inter s s') <-> In x s /\ In x s'.
Parameter diff_spec : forall `{Ok s, Ok s'},
In x (diff s s') <-> In x s /\ ~In x s'.
Parameter fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A),
fold f s i = fold_left (flip f) (elements s) i.
Parameter cardinal_spec : forall `{Ok s},
cardinal s = length (elements s).
Parameter filter_spec : compatb f ->
(In x (filter f s) <-> In x s /\ f x = true).
Parameter for_all_spec : compatb f ->
(for_all f s = true <-> For_all (fun x => f x = true) s).
Parameter exists_spec : compatb f ->
(exists_ f s = true <-> Exists (fun x => f x = true) s).
Parameter partition_spec1 : compatb f ->
fst (partition f s) [=] filter f s.
Parameter partition_spec2 : compatb f ->
snd (partition f s) [=] filter (fun x => negb (f x)) s.
Parameter elements_spec1 : InA E.eq x (elements s) <-> In x s.
Parameter elements_spec2w : forall `{Ok s}, NoDupA E.eq (elements s).
Parameter choose_spec1 : choose s = Some x -> In x s.
Parameter choose_spec2 : choose s = None -> Empty s.

End Spec.

End WRawSets.



Module WRaw2SetsOn (E:DecidableType)(M:WRawSets E) <: WSetsOn E.


Local Unset Elimination Schemes.

Definition elt := E.t.

Record t_ := Mkt {this :> M.t; is_ok : M.Ok this}.
Definition t := t_.
Arguments Mkt this {is_ok}.
Hint Resolve is_ok : typeclass_instances.

Definition In (x : elt)(s : t) := M.In x s.(this).
Definition Equal (s s' : t) := forall a : elt, In a s <-> In a s'.
Definition Subset (s s' : t) := forall a : elt, In a s -> In a s'.
Definition Empty (s : t) := forall a : elt, ~ In a s.
Definition For_all (P : elt -> Prop)(s : t) := forall x, In x s -> P x.
Definition Exists (P : elt -> Prop)(s : t) := exists x, In x s /\ P x.

Definition mem (x : elt)(s : t) := M.mem x s.
Definition add (x : elt)(s : t) : t := Mkt (M.add x s).
Definition remove (x : elt)(s : t) : t := Mkt (M.remove x s).
Definition singleton (x : elt) : t := Mkt (M.singleton x).
Definition union (s s' : t) : t := Mkt (M.union s s').
Definition inter (s s' : t) : t := Mkt (M.inter s s').
Definition diff (s s' : t) : t := Mkt (M.diff s s').
Definition equal (s s' : t) := M.equal s s'.
Definition subset (s s' : t) := M.subset s s'.
Definition empty : t := Mkt M.empty.
Definition is_empty (s : t) := M.is_empty s.
Definition elements (s : t) : list elt := M.elements s.
Definition choose (s : t) : option elt := M.choose s.
Definition fold (A : Type)(f : elt -> A -> A)(s : t) : A -> A := M.fold f s.
Definition cardinal (s : t) := M.cardinal s.
Definition filter (f : elt -> bool)(s : t) : t := Mkt (M.filter f s).
Definition for_all (f : elt -> bool)(s : t) := M.for_all f s.
Definition exists_ (f : elt -> bool)(s : t) := M.exists_ f s.
Definition partition (f : elt -> bool)(s : t) : t * t :=
let p := M.partition f s in (Mkt (fst p), Mkt (snd p)).

Instance In_compat : Proper (E.eq==>eq==>iff) In.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.In_compat".   repeat red. intros; apply M.In_compat; congruence. Qed.

Definition eq : t -> t -> Prop := Equal.

Instance eq_equiv : Equivalence eq.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WRawSets.eq_equiv".   firstorder. Qed.

Definition eq_dec : forall (s s':t), { eq s s' }+{ ~eq s s' }.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WRaw2SetsOn.eq_dec".  
intros (s,Hs) (s',Hs').
change ({M.Equal s s'}+{~M.Equal s s'}).
destruct (M.equal s s') eqn:H; [left|right];
rewrite <- M.equal_spec; congruence.
Defined.


Section Spec.
Variable s s' : t.
Variable x y : elt.
Variable f : elt -> bool.
Notation compatb := (Proper (E.eq==>Logic.eq)) (only parsing).

Lemma mem_spec : mem x s = true <-> In x s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.mem_spec".   exact (@M.mem_spec _ _ _). Qed.
Lemma equal_spec : equal s s' = true <-> Equal s s'.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.equal_spec".   exact (@M.equal_spec _ _ _ _). Qed.
Lemma subset_spec : subset s s' = true <-> Subset s s'.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.subset_spec".   exact (@M.subset_spec _ _ _ _). Qed.
Lemma empty_spec : Empty empty.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.empty_spec".   exact M.empty_spec. Qed.
Lemma is_empty_spec : is_empty s = true <-> Empty s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.is_empty_spec".   exact (@M.is_empty_spec _). Qed.
Lemma add_spec : In y (add x s) <-> E.eq y x \/ In y s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.add_spec".   exact (@M.add_spec _ _ _ _). Qed.
Lemma remove_spec : In y (remove x s) <-> In y s /\ ~E.eq y x.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.remove_spec".   exact (@M.remove_spec _ _ _ _). Qed.
Lemma singleton_spec : In y (singleton x) <-> E.eq y x.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.singleton_spec".   exact (@M.singleton_spec _ _). Qed.
Lemma union_spec : In x (union s s') <-> In x s \/ In x s'.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.union_spec".   exact (@M.union_spec _ _ _ _ _). Qed.
Lemma inter_spec : In x (inter s s') <-> In x s /\ In x s'.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.inter_spec".   exact (@M.inter_spec _ _ _ _ _). Qed.
Lemma diff_spec : In x (diff s s') <-> In x s /\ ~In x s'.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.diff_spec".   exact (@M.diff_spec _ _ _ _ _). Qed.
Lemma fold_spec : forall (A : Type) (i : A) (f : elt -> A -> A),
fold f s i = fold_left (fun a e => f e a) (elements s) i.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.fold_spec".   exact (@M.fold_spec _). Qed.
Lemma cardinal_spec : cardinal s = length (elements s).
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.cardinal_spec".   exact (@M.cardinal_spec s _). Qed.
Lemma filter_spec : compatb f ->
(In x (filter f s) <-> In x s /\ f x = true).
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.filter_spec".   exact (@M.filter_spec _ _ _). Qed.
Lemma for_all_spec : compatb f ->
(for_all f s = true <-> For_all (fun x => f x = true) s).
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.for_all_spec".   exact (@M.for_all_spec _ _). Qed.
Lemma exists_spec : compatb f ->
(exists_ f s = true <-> Exists (fun x => f x = true) s).
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.exists_spec".   exact (@M.exists_spec _ _). Qed.
Lemma partition_spec1 : compatb f -> Equal (fst (partition f s)) (filter f s).
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.partition_spec1".   exact (@M.partition_spec1 _ _). Qed.
Lemma partition_spec2 : compatb f ->
Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.partition_spec2".   exact (@M.partition_spec2 _ _). Qed.
Lemma elements_spec1 : InA E.eq x (elements s) <-> In x s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.elements_spec1".   exact (@M.elements_spec1 _ _). Qed.
Lemma elements_spec2w : NoDupA E.eq (elements s).
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.elements_spec2w".   exact (@M.elements_spec2w _ _). Qed.
Lemma choose_spec1 : choose s = Some x -> In x s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.choose_spec1".   exact (@M.choose_spec1 _ _). Qed.
Lemma choose_spec2 : choose s = None -> Empty s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WSetsOn.choose_spec2".   exact (@M.choose_spec2 _). Qed.

End Spec.

End WRaw2SetsOn.

Module WRaw2Sets (D:DecidableType)(M:WRawSets D) <: WSets with Module E := D.
Module E := D.
Include WRaw2SetsOn D M.
End WRaw2Sets.



Module Type RawSets (E : OrderedType).
Include WRawSets E <+ HasOrdOps <+ HasLt <+ IsStrOrder.

Section Spec.
Variable s s': t.
Variable x y : elt.


Parameter compare_spec : forall `{Ok s, Ok s'}, CompSpec eq lt s s' (compare s s').


Parameter elements_spec2 : forall `{Ok s}, sort E.lt (elements s).


Parameter min_elt_spec1 : min_elt s = Some x -> In x s.
Parameter min_elt_spec2 : forall `{Ok s}, min_elt s = Some x -> In y s -> ~ E.lt y x.
Parameter min_elt_spec3 : min_elt s = None -> Empty s.


Parameter max_elt_spec1 : max_elt s = Some x -> In x s.
Parameter max_elt_spec2 : forall `{Ok s}, max_elt s = Some x -> In y s -> ~ E.lt x y.
Parameter max_elt_spec3 : max_elt s = None -> Empty s.


Parameter choose_spec3 : forall `{Ok s, Ok s'},
choose s = Some x -> choose s' = Some y -> Equal s s' -> E.eq x y.

End Spec.

End RawSets.



Module Raw2SetsOn (O:OrderedType)(M:RawSets O) <: SetsOn O.
Include WRaw2SetsOn O M.

Definition compare (s s':t) := M.compare s s'.
Definition min_elt (s:t) : option elt := M.min_elt s.
Definition max_elt (s:t) : option elt := M.max_elt s.
Definition lt (s s':t) := M.lt s s'.


Instance lt_strorder : StrictOrder lt.
Proof. try hammer_hook "MSetInterface" "MSetInterface.Raw2SetsOn.lt_strorder".   constructor ; unfold lt; red.
unfold complement. red. intros. apply (irreflexivity H).
intros. transitivity y; auto.
Qed.

Instance lt_compat : Proper (eq==>eq==>iff) lt.
Proof. try hammer_hook "MSetInterface" "MSetInterface.Raw2SetsOn.lt_compat".  
repeat red. unfold eq, lt.
intros (s1,p1) (s2,p2) E (s1',p1') (s2',p2') E'; simpl.
change (M.eq s1 s2) in E.
change (M.eq s1' s2') in E'.
rewrite E,E'; intuition.
Qed.

Section Spec.
Variable s s' s'' : t.
Variable x y : elt.

Lemma compare_spec : CompSpec eq lt s s' (compare s s').
Proof. try hammer_hook "MSetInterface" "MSetInterface.SetsOn.compare_spec".   unfold compare; destruct (@M.compare_spec s s' _ _); auto. Qed.


Lemma elements_spec2 : sort O.lt (elements s).
Proof. try hammer_hook "MSetInterface" "MSetInterface.SetsOn.elements_spec2".   exact (@M.elements_spec2 _ _). Qed.


Lemma min_elt_spec1 : min_elt s = Some x -> In x s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.SetsOn.min_elt_spec1".   exact (@M.min_elt_spec1 _ _). Qed.
Lemma min_elt_spec2 : min_elt s = Some x -> In y s -> ~ O.lt y x.
Proof. try hammer_hook "MSetInterface" "MSetInterface.SetsOn.min_elt_spec2".   exact (@M.min_elt_spec2 _ _ _ _). Qed.
Lemma min_elt_spec3 : min_elt s = None -> Empty s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.SetsOn.min_elt_spec3".   exact (@M.min_elt_spec3 _). Qed.


Lemma max_elt_spec1 : max_elt s = Some x -> In x s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.SetsOn.max_elt_spec1".   exact (@M.max_elt_spec1 _ _). Qed.
Lemma max_elt_spec2 : max_elt s = Some x -> In y s -> ~ O.lt x y.
Proof. try hammer_hook "MSetInterface" "MSetInterface.SetsOn.max_elt_spec2".   exact (@M.max_elt_spec2 _ _ _ _). Qed.
Lemma max_elt_spec3 : max_elt s = None -> Empty s.
Proof. try hammer_hook "MSetInterface" "MSetInterface.SetsOn.max_elt_spec3".   exact (@M.max_elt_spec3 _). Qed.


Lemma choose_spec3 :
choose s = Some x -> choose s' = Some y -> Equal s s' -> O.eq x y.
Proof. try hammer_hook "MSetInterface" "MSetInterface.SetsOn.choose_spec3".   exact (@M.choose_spec3 _ _ _ _ _ _). Qed.

End Spec.

End Raw2SetsOn.

Module Raw2Sets (O:OrderedType)(M:RawSets O) <: Sets with Module E := O.
Module E := O.
Include Raw2SetsOn O M.
End Raw2Sets.




Module Type IN (O:OrderedType).
Parameter Inline t : Type.
Parameter Inline In : O.t -> t -> Prop.
Declare Instance In_compat : Proper (O.eq==>eq==>iff) In.
Definition Equal s s' := forall x, In x s <-> In x s'.
Definition Empty s := forall x, ~In x s.
End IN.

Module MakeSetOrdering (O:OrderedType)(Import M:IN O).
Module Import MO := OrderedTypeFacts O.

Definition eq : t -> t -> Prop := Equal.

Instance eq_equiv : Equivalence eq.
Proof. try hammer_hook "MSetInterface" "MSetInterface.WRaw2SetsOn.eq_equiv".   firstorder. Qed.

Instance : Proper (O.eq==>eq==>iff) In.
Proof.
intros x x' Ex s s' Es. rewrite Ex. apply Es.
Qed.

Definition Below x s := forall y, In y s -> O.lt y x.
Definition Above x s := forall y, In y s -> O.lt x y.

Definition EquivBefore x s s' :=
forall y, O.lt y x -> (In y s <-> In y s').

Definition EmptyBetween x y s :=
forall z, In z s -> O.lt z y -> O.lt z x.

Definition lt s s' := exists x, EquivBefore x s s' /\
((In x s' /\ Below x s) \/
(In x s  /\ exists y, In y s' /\ O.lt x y /\ EmptyBetween x y s')).

Instance : Proper (O.eq==>eq==>eq==>iff) EquivBefore.
Proof.
unfold EquivBefore. intros x x' E s1 s1' E1 s2 s2' E2.
setoid_rewrite E; setoid_rewrite E1; setoid_rewrite E2; intuition.
Qed.

Instance : Proper (O.eq==>eq==>iff) Below.
Proof.
unfold Below. intros x x' Ex s s' Es.
setoid_rewrite Ex; setoid_rewrite Es; intuition.
Qed.

Instance : Proper (O.eq==>eq==>iff) Above.
Proof.
unfold Above. intros x x' Ex s s' Es.
setoid_rewrite Ex; setoid_rewrite Es; intuition.
Qed.

Instance : Proper (O.eq==>O.eq==>eq==>iff) EmptyBetween.
Proof.
unfold EmptyBetween. intros x x' Ex y y' Ey s s' Es.
setoid_rewrite Ex; setoid_rewrite Ey; setoid_rewrite Es; intuition.
Qed.

Instance lt_compat : Proper (eq==>eq==>iff) lt.
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeSetOrdering.lt_compat".  
unfold lt. intros s1 s1' E1 s2 s2' E2.
setoid_rewrite E1; setoid_rewrite E2; intuition.
Qed.

Instance lt_strorder : StrictOrder lt.
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeSetOrdering.lt_strorder".  
split.

intros s (x & _ & [(IN,Em)|(IN & y & IN' & LT & Be)]).
specialize (Em x IN); order.
specialize (Be x IN LT); order.

intros s1 s2 s3 (x & EQ & [(IN,Pre)|(IN,Lex)])
(x' & EQ' & [(IN',Pre')|(IN',Lex')]).

assert (O.lt x x') by (specialize (Pre' x IN); auto).
exists x; split.
intros y Hy; rewrite <- (EQ' y); auto; order.
left; split; auto.
rewrite <- (EQ' x); auto.

elim_compare x x'.

destruct Lex' as (y & INy & LT & Be).
exists y; split.
intros z Hz. split; intros INz.
specialize (Pre z INz). rewrite <- (EQ' z), <- (EQ z); auto; order.
specialize (Be z INz Hz). rewrite (EQ z), (EQ' z); auto; order.
left; split; auto.
intros z Hz. transitivity x; auto; order.

exists x; split.
intros z Hz. rewrite <- (EQ' z) by order; auto.
left; split; auto.
rewrite <- (EQ' x); auto.

exists x'; split.
intros z Hz. rewrite (EQ z) by order; auto.
right; split; auto.
rewrite (EQ x'); auto.

destruct Lex as (y & INy & LT & Be).
specialize (Pre' y INy).
exists x; split.
intros z Hz. rewrite <- (EQ' z) by order; auto.
right; split; auto.
exists y; repeat split; auto.
rewrite <- (EQ' y); auto.
intros z Hz LTz; apply Be; auto. rewrite (EQ' z); auto; order.

elim_compare x x'.

destruct Lex as (y & INy & LT & Be).
setoid_replace x with x' in LT; auto.
specialize (Be x' IN' LT); order.

exists x; split.
intros z Hz. rewrite <- (EQ' z) by order; auto.
right; split; auto.
destruct Lex as (y & INy & LT & Be).
elim_compare y x'.

destruct Lex' as (y' & Iny' & LT' & Be').
exists y'; repeat split; auto. order.
intros z Hz LTz. specialize (Be' z Hz LTz).
rewrite <- (EQ' z) in Hz by order.
apply Be; auto. order.

exists y; repeat split; auto.
rewrite <- (EQ' y); auto.
intros z Hz LTz. apply Be; auto. rewrite (EQ' z); auto; order.

assert (O.lt x' x) by auto. order.

exists x'; split.
intros z Hz. rewrite (EQ z) by order; auto.
right; split; auto.
rewrite (EQ x'); auto.
Qed.

Lemma lt_empty_r : forall s s', Empty s' -> ~ lt s s'.
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeSetOrdering.lt_empty_r".  
intros s s' Hs' (x & _ & [(IN,_)|(_ & y & IN & _)]).
elim (Hs' x IN).
elim (Hs' y IN).
Qed.

Definition Add x s s' := forall y, In y s' <-> O.eq x y \/ In y s.

Lemma lt_empty_l : forall x s1 s2 s2',
Empty s1 -> Above x s2 -> Add x s2 s2' -> lt s1 s2'.
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeSetOrdering.lt_empty_l".  
intros x s1 s2 s2' Em Ab Ad.
exists x; split.
intros y Hy; split; intros IN.
elim (Em y IN).
rewrite (Ad y) in IN; destruct IN as [EQ|IN]. order.
specialize (Ab y IN). order.
left; split.
rewrite (Ad x). now left.
intros y Hy. elim (Em y Hy).
Qed.

Lemma lt_add_lt : forall x1 x2 s1 s1' s2 s2',
Above x1 s1 -> Above x2 s2 -> Add x1 s1 s1' -> Add x2 s2 s2' ->
O.lt x1 x2 -> lt s1' s2'.
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeSetOrdering.lt_add_lt".  
intros x1 x2 s1 s1' s2 s2' Ab1 Ab2 Ad1 Ad2 LT.
exists x1; split; [ | right; split]; auto.
intros y Hy. rewrite (Ad1 y), (Ad2 y).
split; intros [U|U]; try order.
specialize (Ab1 y U). order.
specialize (Ab2 y U). order.
rewrite (Ad1 x1); auto with *.
exists x2; repeat split; auto.
rewrite (Ad2 x2); now left.
intros y. rewrite (Ad2 y). intros [U|U]. order.
specialize (Ab2 y U). order.
Qed.

Lemma lt_add_eq : forall x1 x2 s1 s1' s2 s2',
Above x1 s1 -> Above x2 s2 -> Add x1 s1 s1' -> Add x2 s2 s2' ->
O.eq x1 x2 -> lt s1 s2 -> lt s1' s2'.
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeSetOrdering.lt_add_eq".  
intros x1 x2 s1 s1' s2 s2' Ab1 Ab2 Ad1 Ad2 Hx (x & EQ & Disj).
assert (O.lt x1 x).
destruct Disj as [(IN,_)|(IN,_)]; auto. rewrite Hx; auto.
exists x; split.
intros z Hz. rewrite (Ad1 z), (Ad2 z).
split; intros [U|U]; try (left; order); right.
rewrite <- (EQ z); auto.
rewrite (EQ z); auto.
destruct Disj as [(IN,Em)|(IN & y & INy & LTy & Be)].
left; split; auto.
rewrite (Ad2 x); auto.
intros z. rewrite (Ad1 z); intros [U|U]; try specialize (Ab1 z U); auto; order.
right; split; auto.
rewrite (Ad1 x); auto.
exists y; repeat split; auto.
rewrite (Ad2 y); auto.
intros z. rewrite (Ad2 z). intros [U|U]; try specialize (Ab2 z U); auto; order.
Qed.

End MakeSetOrdering.


Module MakeListOrdering (O:OrderedType).
Module MO:=OrderedTypeFacts O.

Local Notation t := (list O.t).
Local Notation In := (InA O.eq).

Definition eq s s' := forall x, In x s <-> In x s'.

Instance eq_equiv : Equivalence eq := _.

Inductive lt_list : t -> t -> Prop :=
| lt_nil : forall x s, lt_list nil (x :: s)
| lt_cons_lt : forall x y s s',
O.lt x y -> lt_list (x :: s) (y :: s')
| lt_cons_eq : forall x y s s',
O.eq x y -> lt_list s s' -> lt_list (x :: s) (y :: s').
Hint Constructors lt_list.

Definition lt := lt_list.
Hint Unfold lt.

Instance lt_strorder : StrictOrder lt.
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeListOrdering.lt_strorder".  
split.

assert (forall s s', s=s' -> ~lt s s').
red; induction 2.
discriminate.
inversion H; subst.
apply (StrictOrder_Irreflexive y); auto.
inversion H; subst; auto.
intros s Hs; exact (H s s (eq_refl s) Hs).

intros s s' s'' H; generalize s''; clear s''; elim H.
intros x l s'' H'; inversion_clear H'; auto.
intros x x' l l' E s'' H'; inversion_clear H'; auto.
constructor 2. transitivity x'; auto.
constructor 2. rewrite <- H0; auto.
intros.
inversion_clear H3.
constructor 2. rewrite H0; auto.
constructor 3; auto. transitivity y; auto. unfold lt in *; auto.
Qed.

Instance lt_compat' :
Proper (eqlistA O.eq==>eqlistA O.eq==>iff) lt.
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeListOrdering.lt_compat'".  
apply proper_sym_impl_iff_2; auto with *.
intros s1 s1' E1 s2 s2' E2 H.
revert s1' E1 s2' E2.
induction H; intros; inversion_clear E1; inversion_clear E2.
constructor 1.
constructor 2. MO.order.
constructor 3. MO.order. unfold lt in *; auto.
Qed.

Lemma eq_cons :
forall l1 l2 x y,
O.eq x y -> eq l1 l2 -> eq (x :: l1) (y :: l2).
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeListOrdering.eq_cons".  
unfold eq; intros l1 l2 x y Exy E12 z.
split; inversion_clear 1.
left; MO.order. right; rewrite <- E12; auto.
left; MO.order. right; rewrite E12; auto.
Qed.
Hint Resolve eq_cons.

Lemma cons_CompSpec : forall c x1 x2 l1 l2, O.eq x1 x2 ->
CompSpec eq lt l1 l2 c -> CompSpec eq lt (x1::l1) (x2::l2) c.
Proof. try hammer_hook "MSetInterface" "MSetInterface.MakeListOrdering.cons_CompSpec".  
destruct c; simpl; inversion_clear 2; auto with relations.
Qed.
Hint Resolve cons_CompSpec.

End MakeListOrdering.
