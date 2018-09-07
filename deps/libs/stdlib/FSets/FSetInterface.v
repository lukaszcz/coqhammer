From Hammer Require Import Hammer.













Require Export Bool OrderedType DecidableType.
Set Implicit Arguments.
Unset Strict Implicit.







Module Type WSfun (E : DecidableType).

Definition elt := E.t.

Parameter t : Type.


Parameter In : elt -> t -> Prop.
Definition Equal s s' := forall a : elt, In a s <-> In a s'.
Definition Subset s s' := forall a : elt, In a s -> In a s'.
Definition Empty s := forall a : elt, ~ In a s.
Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

Notation "s  [=]  t" := (Equal s t) (at level 70, no associativity).
Notation "s  [<=]  t" := (Subset s t) (at level 70, no associativity).

Parameter empty : t.


Parameter is_empty : t -> bool.


Parameter mem : elt -> t -> bool.


Parameter add : elt -> t -> t.


Parameter singleton : elt -> t.


Parameter remove : elt -> t -> t.


Parameter union : t -> t -> t.


Parameter inter : t -> t -> t.


Parameter diff : t -> t -> t.


Definition eq : t -> t -> Prop := Equal.

Parameter eq_dec : forall s s', { eq s s' } + { ~ eq s s' }.

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


Section Spec.

Variable s s' s'': t.
Variable x y : elt.


Parameter In_1 : E.eq x y -> In x s -> In y s.


Parameter eq_refl : eq s s.
Parameter eq_sym : eq s s' -> eq s' s.
Parameter eq_trans : eq s s' -> eq s' s'' -> eq s s''.


Parameter mem_1 : In x s -> mem x s = true.
Parameter mem_2 : mem x s = true -> In x s.


Parameter equal_1 : Equal s s' -> equal s s' = true.
Parameter equal_2 : equal s s' = true -> Equal s s'.


Parameter subset_1 : Subset s s' -> subset s s' = true.
Parameter subset_2 : subset s s' = true -> Subset s s'.


Parameter empty_1 : Empty empty.


Parameter is_empty_1 : Empty s -> is_empty s = true.
Parameter is_empty_2 : is_empty s = true -> Empty s.


Parameter add_1 : E.eq x y -> In y (add x s).
Parameter add_2 : In y s -> In y (add x s).
Parameter add_3 : ~ E.eq x y -> In y (add x s) -> In y s.


Parameter remove_1 : E.eq x y -> ~ In y (remove x s).
Parameter remove_2 : ~ E.eq x y -> In y s -> In y (remove x s).
Parameter remove_3 : In y (remove x s) -> In y s.


Parameter singleton_1 : In y (singleton x) -> E.eq x y.
Parameter singleton_2 : E.eq x y -> In y (singleton x).


Parameter union_1 : In x (union s s') -> In x s \/ In x s'.
Parameter union_2 : In x s -> In x (union s s').
Parameter union_3 : In x s' -> In x (union s s').


Parameter inter_1 : In x (inter s s') -> In x s.
Parameter inter_2 : In x (inter s s') -> In x s'.
Parameter inter_3 : In x s -> In x s' -> In x (inter s s').


Parameter diff_1 : In x (diff s s') -> In x s.
Parameter diff_2 : In x (diff s s') -> ~ In x s'.
Parameter diff_3 : In x s -> ~ In x s' -> In x (diff s s').


Parameter fold_1 : forall (A : Type) (i : A) (f : elt -> A -> A),
fold f s i = fold_left (fun a e => f e a) (elements s) i.


Parameter cardinal_1 : cardinal s = length (elements s).

Section Filter.

Variable f : elt -> bool.


Parameter filter_1 : compat_bool E.eq f -> In x (filter f s) -> In x s.
Parameter filter_2 : compat_bool E.eq f -> In x (filter f s) -> f x = true.
Parameter filter_3 :
compat_bool E.eq f -> In x s -> f x = true -> In x (filter f s).


Parameter for_all_1 :
compat_bool E.eq f ->
For_all (fun x => f x = true) s -> for_all f s = true.
Parameter for_all_2 :
compat_bool E.eq f ->
for_all f s = true -> For_all (fun x => f x = true) s.


Parameter exists_1 :
compat_bool E.eq f ->
Exists (fun x => f x = true) s -> exists_ f s = true.
Parameter exists_2 :
compat_bool E.eq f ->
exists_ f s = true -> Exists (fun x => f x = true) s.


Parameter partition_1 :
compat_bool E.eq f -> Equal (fst (partition f s)) (filter f s).
Parameter partition_2 :
compat_bool E.eq f ->
Equal (snd (partition f s)) (filter (fun x => negb (f x)) s).

End Filter.


Parameter elements_1 : In x s -> InA E.eq x (elements s).
Parameter elements_2 : InA E.eq x (elements s) -> In x s.

Parameter elements_3w : NoDupA E.eq (elements s).


Parameter choose_1 : choose s = Some x -> In x s.
Parameter choose_2 : choose s = None -> Empty s.

End Spec.

Hint Transparent elt.
Hint Resolve mem_1 equal_1 subset_1 empty_1
is_empty_1 choose_1 choose_2 add_1 add_2 remove_1
remove_2 singleton_2 union_1 union_2 union_3
inter_3 diff_3 fold_1 filter_3 for_all_1 exists_1
partition_1 partition_2 elements_1 elements_3w
: set.
Hint Immediate In_1 mem_2 equal_2 subset_2 is_empty_2 add_3
remove_3 singleton_1 inter_1 inter_2 diff_1 diff_2
filter_1 filter_2 for_all_2 exists_2 elements_2
: set.

End WSfun.





Module Type WS.
Declare Module E : DecidableType.
Include WSfun E.
End WS.





Module Type Sfun (E : OrderedType).
Include WSfun E.

Parameter lt : t -> t -> Prop.
Parameter compare : forall s s' : t, Compare lt eq s s'.


Parameter min_elt : t -> option elt.


Parameter max_elt : t -> option elt.


Section Spec.

Variable s s' s'' : t.
Variable x y : elt.


Parameter lt_trans : lt s s' -> lt s' s'' -> lt s s''.
Parameter lt_not_eq : lt s s' -> ~ eq s s'.


Parameter elements_3 : sort E.lt (elements s).




Parameter min_elt_1 : min_elt s = Some x -> In x s.
Parameter min_elt_2 : min_elt s = Some x -> In y s -> ~ E.lt y x.
Parameter min_elt_3 : min_elt s = None -> Empty s.


Parameter max_elt_1 : max_elt s = Some x -> In x s.
Parameter max_elt_2 : max_elt s = Some x -> In y s -> ~ E.lt x y.
Parameter max_elt_3 : max_elt s = None -> Empty s.


Parameter choose_3 : choose s = Some x -> choose s' = Some y ->
Equal s s' -> E.eq x y.

End Spec.

Hint Resolve elements_3 : set.
Hint Immediate
min_elt_1 min_elt_2 min_elt_3 max_elt_1 max_elt_2 max_elt_3 : set.

End Sfun.




Module Type S.
Declare Module E : OrderedType.
Include Sfun E.
End S.






Module Type Sdep.

Declare Module E : OrderedType.
Definition elt := E.t.

Parameter t : Type.

Parameter In : elt -> t -> Prop.
Definition Equal s s' := forall a : elt, In a s <-> In a s'.
Definition Subset s s' := forall a : elt, In a s -> In a s'.
Definition Add x s s' := forall y, In y s' <-> E.eq x y \/ In y s.
Definition Empty s := forall a : elt, ~ In a s.
Definition For_all (P : elt -> Prop) s := forall x, In x s -> P x.
Definition Exists (P : elt -> Prop) s := exists x, In x s /\ P x.

Notation "s [=] t" := (Equal s t) (at level 70, no associativity).

Definition eq : t -> t -> Prop := Equal.
Parameter lt : t -> t -> Prop.
Parameter compare : forall s s' : t, Compare lt eq s s'.

Parameter eq_refl : forall s : t, eq s s.
Parameter eq_sym : forall s s' : t, eq s s' -> eq s' s.
Parameter eq_trans : forall s s' s'' : t, eq s s' -> eq s' s'' -> eq s s''.
Parameter lt_trans : forall s s' s'' : t, lt s s' -> lt s' s'' -> lt s s''.
Parameter lt_not_eq : forall s s' : t, lt s s' -> ~ eq s s'.

Parameter eq_In : forall (s : t) (x y : elt), E.eq x y -> In x s -> In y s.

Parameter empty : {s : t | Empty s}.

Parameter is_empty : forall s : t, {Empty s} + {~ Empty s}.

Parameter mem : forall (x : elt) (s : t), {In x s} + {~ In x s}.

Parameter add : forall (x : elt) (s : t), {s' : t | Add x s s'}.

Parameter
singleton : forall x : elt, {s : t | forall y : elt, In y s <-> E.eq x y}.

Parameter
remove :
forall (x : elt) (s : t),
{s' : t | forall y : elt, In y s' <-> ~ E.eq x y /\ In y s}.

Parameter
union :
forall s s' : t,
{s'' : t | forall x : elt, In x s'' <-> In x s \/ In x s'}.

Parameter
inter :
forall s s' : t,
{s'' : t | forall x : elt, In x s'' <-> In x s /\ In x s'}.

Parameter
diff :
forall s s' : t,
{s'' : t | forall x : elt, In x s'' <-> In x s /\ ~ In x s'}.

Parameter equal : forall s s' : t, {s[=]s'} + {~ s[=]s'}.

Parameter subset : forall s s' : t, {Subset s s'} + {~ Subset s s'}.

Parameter
filter :
forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
(s : t),
{s' : t | compat_P E.eq P -> forall x : elt, In x s' <-> In x s /\ P x}.

Parameter
for_all :
forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
(s : t),
{compat_P E.eq P -> For_all P s} + {compat_P E.eq P -> ~ For_all P s}.

Parameter
exists_ :
forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
(s : t),
{compat_P E.eq P -> Exists P s} + {compat_P E.eq P -> ~ Exists P s}.

Parameter
partition :
forall (P : elt -> Prop) (Pdec : forall x : elt, {P x} + {~ P x})
(s : t),
{partition : t * t |
let (s1, s2) := partition in
compat_P E.eq P ->
For_all P s1 /\
For_all (fun x => ~ P x) s2 /\
(forall x : elt, In x s <-> In x s1 \/ In x s2)}.

Parameter
elements :
forall s : t,
{l : list elt |
sort E.lt l /\ (forall x : elt, In x s <-> InA E.eq x l)}.

Parameter
fold :
forall (A : Type) (f : elt -> A -> A) (s : t) (i : A),
{r : A | let (l,_) := elements s in
r = fold_left (fun a e => f e a) l i}.

Parameter
cardinal :
forall s : t,
{r : nat | let (l,_) := elements s in r = length l }.

Parameter
min_elt :
forall s : t,
{x : elt | In x s /\ For_all (fun y => ~ E.lt y x) s} + {Empty s}.

Parameter
max_elt :
forall s : t,
{x : elt | In x s /\ For_all (fun y => ~ E.lt x y) s} + {Empty s}.

Parameter choose : forall s : t, {x : elt | In x s} + {Empty s}.


Parameter choose_equal : forall s s', Equal s s' ->
match choose s, choose s' with
| inleft (exist _ x _), inleft (exist _ x' _) => E.eq x x'
| inright _, inright _  => True
| _, _  => False
end.

End Sdep.

