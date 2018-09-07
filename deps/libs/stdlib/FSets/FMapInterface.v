From Hammer Require Import Hammer.













Require Export Bool DecidableType OrderedType.
Set Implicit Arguments.
Unset Strict Implicit.




Definition Cmp (elt:Type)(cmp:elt->elt->bool) e1 e2 := cmp e1 e2 = true.



Module Type WSfun (E : DecidableType).

Definition key := E.t.
Hint Transparent key.

Parameter t : Type -> Type.


Section Types.

Variable elt:Type.

Parameter empty : t elt.


Parameter is_empty : t elt -> bool.


Parameter add : key -> elt -> t elt -> t elt.


Parameter find : key -> t elt -> option elt.


Parameter remove : key -> t elt -> t elt.


Parameter mem : key -> t elt -> bool.


Variable elt' elt'' : Type.

Parameter map : (elt -> elt') -> t elt -> t elt'.


Parameter mapi : (key -> elt -> elt') -> t elt -> t elt'.


Parameter map2 :
(option elt -> option elt' -> option elt'') -> t elt -> t elt' ->  t elt''.


Parameter elements : t elt -> list (key*elt).


Parameter cardinal : t elt -> nat.


Parameter fold : forall A: Type, (key -> elt -> A -> A) -> t elt -> A -> A.


Parameter equal : (elt -> elt -> bool) -> t elt -> t elt -> bool.


Section Spec.

Variable m m' m'' : t elt.
Variable x y z : key.
Variable e e' : elt.

Parameter MapsTo : key -> elt -> t elt -> Prop.

Definition In (k:key)(m: t elt) : Prop := exists e:elt, MapsTo k e m.

Definition Empty m := forall (a : key)(e:elt) , ~ MapsTo a e m.

Definition eq_key (p p':key*elt) := E.eq (fst p) (fst p').

Definition eq_key_elt (p p':key*elt) :=
E.eq (fst p) (fst p') /\ (snd p) = (snd p').


Parameter MapsTo_1 : E.eq x y -> MapsTo x e m -> MapsTo y e m.


Parameter mem_1 : In x m -> mem x m = true.
Parameter mem_2 : mem x m = true -> In x m.


Parameter empty_1 : Empty empty.


Parameter is_empty_1 : Empty m -> is_empty m = true.
Parameter is_empty_2 : is_empty m = true -> Empty m.


Parameter add_1 : E.eq x y -> MapsTo y e (add x e m).
Parameter add_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (add x e' m).
Parameter add_3 : ~ E.eq x y -> MapsTo y e (add x e' m) -> MapsTo y e m.


Parameter remove_1 : E.eq x y -> ~ In y (remove x m).
Parameter remove_2 : ~ E.eq x y -> MapsTo y e m -> MapsTo y e (remove x m).
Parameter remove_3 : MapsTo y e (remove x m) -> MapsTo y e m.


Parameter find_1 : MapsTo x e m -> find x m = Some e.
Parameter find_2 : find x m = Some e -> MapsTo x e m.


Parameter elements_1 :
MapsTo x e m -> InA eq_key_elt (x,e) (elements m).
Parameter elements_2 :
InA eq_key_elt (x,e) (elements m) -> MapsTo x e m.

Parameter elements_3w : NoDupA eq_key (elements m).


Parameter cardinal_1 : cardinal m = length (elements m).


Parameter fold_1 :
forall (A : Type) (i : A) (f : key -> elt -> A -> A),
fold f m i = fold_left (fun a p => f (fst p) (snd p) a) (elements m) i.





Definition Equal m m' := forall y, find y m = find y m'.
Definition Equiv (eq_elt:elt->elt->Prop) m m' :=
(forall k, In k m <-> In k m') /\
(forall k e e', MapsTo k e m -> MapsTo k e' m' -> eq_elt e e').
Definition Equivb (cmp: elt->elt->bool) := Equiv (Cmp cmp).



Variable cmp : elt -> elt -> bool.

Parameter equal_1 : Equivb cmp m m' -> equal cmp m m' = true.
Parameter equal_2 : equal cmp m m' = true -> Equivb cmp m m'.

End Spec.
End Types.


Parameter map_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)(f:elt->elt'),
MapsTo x e m -> MapsTo x (f e) (map f m).
Parameter map_2 : forall (elt elt':Type)(m: t elt)(x:key)(f:elt->elt'),
In x (map f m) -> In x m.


Parameter mapi_1 : forall (elt elt':Type)(m: t elt)(x:key)(e:elt)
(f:key->elt->elt'), MapsTo x e m ->
exists y, E.eq y x /\ MapsTo x (f y e) (mapi f m).
Parameter mapi_2 : forall (elt elt':Type)(m: t elt)(x:key)
(f:key->elt->elt'), In x (mapi f m) -> In x m.


Parameter map2_1 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
(x:key)(f:option elt->option elt'->option elt''),
In x m \/ In x m' ->
find x (map2 f m m') = f (find x m) (find x m').

Parameter map2_2 : forall (elt elt' elt'':Type)(m: t elt)(m': t elt')
(x:key)(f:option elt->option elt'->option elt''),
In x (map2 f m m') -> In x m \/ In x m'.

Hint Immediate MapsTo_1 mem_2 is_empty_2
map_2 mapi_2 add_3 remove_3 find_2
: map.
Hint Resolve mem_1 is_empty_1 is_empty_2 add_1 add_2 remove_1
remove_2 find_1 fold_1 map_1 mapi_1 mapi_2
: map.

End WSfun.




Module Type WS.
Declare Module E : DecidableType.
Include WSfun E.
End WS.





Module Type Sfun (E : OrderedType).
Include WSfun E.
Section elt.
Variable elt:Type.
Definition lt_key (p p':key*elt) := E.lt (fst p) (fst p').

Parameter elements_3 : forall m, sort lt_key (elements m).

End elt.
End Sfun.





Module Type S.
Declare Module E : OrderedType.
Include Sfun E.
End S.





Module Type Sord.

Declare Module Data : OrderedType.
Declare Module MapS : S.
Import MapS.

Definition t := MapS.t Data.t.

Parameter eq : t -> t -> Prop.
Parameter lt : t -> t -> Prop.

Axiom eq_refl : forall m : t, eq m m.
Axiom eq_sym : forall m1 m2 : t, eq m1 m2 -> eq m2 m1.
Axiom eq_trans : forall m1 m2 m3 : t, eq m1 m2 -> eq m2 m3 -> eq m1 m3.
Axiom lt_trans : forall m1 m2 m3 : t, lt m1 m2 -> lt m2 m3 -> lt m1 m3.
Axiom lt_not_eq : forall m1 m2 : t, lt m1 m2 -> ~ eq m1 m2.

Definition cmp e e' := match Data.compare e e' with EQ _ => true | _ => false end.

Parameter eq_1 : forall m m', Equivb cmp m m' -> eq m m'.
Parameter eq_2 : forall m m', eq m m' -> Equivb cmp m m'.

Parameter compare : forall m1 m2, Compare lt eq m1 m2.


End Sord.
