From Hammer Require Import Hammer.













Require Import Arith_base.
Require Vectors.Fin.
Import EqNotations.
Local Open Scope nat_scope.





Inductive t A : nat -> Type :=
|nil : t A 0
|cons : forall (h:A) (n:nat), t A n -> t A (S n).

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

Section SCHEMES.



Definition rectS {A} (P:forall {n}, t A (S n) -> Type)
(bas: forall a: A, P (a :: []))
(rect: forall a {n} (v: t A (S n)), P v -> P (a :: v)) :=
fix rectS_fix {n} (v: t A (S n)) : P v :=
match v with
|@cons _ a 0 v =>
match v with
|nil _ => bas a
|_ => fun devil => False_ind (@IDProp) devil
end
|@cons _ a (S nn') v => rect a v (rectS_fix v)
|_ => fun devil => False_ind (@IDProp) devil
end.


Definition case0 {A} (P:t A 0 -> Type) (H:P (nil A)) v:P v :=
match v with
|[] => H
|_ => fun devil => False_ind (@IDProp) devil
end.


Definition caseS {A} (P : forall {n}, t A (S n) -> Type)
(H : forall h {n} t, @P n (h :: t)) {n} (v: t A (S n)) : P v :=
match v with
|h :: t => H h t
|_ => fun devil => False_ind (@IDProp) devil
end.

Definition caseS' {A} {n : nat} (v : t A (S n)) : forall (P : t A (S n) -> Type)
(H : forall h t, P (h :: t)), P v :=
match v with
| h :: t => fun P H => H h t
| _ => fun devil => False_rect (@IDProp) devil
end.


Definition rect2 {A B} (P:forall {n}, t A n -> t B n -> Type)
(bas : P [] []) (rect : forall {n v1 v2}, P v1 v2 ->
forall a b, P (a :: v1) (b :: v2)) :=
fix rect2_fix {n} (v1 : t A n) : forall v2 : t B n, P v1 v2 :=
match v1 with
| [] => fun v2 => case0 _ bas v2
| @cons _ h1 n' t1 => fun v2 =>
caseS' v2 (fun v2' => P (h1::t1) v2') (fun h2 t2 => rect (rect2_fix t1 t2) h1 h2)
end.

End SCHEMES.

Section BASES.

Definition hd {A} := @caseS _ (fun n v => A) (fun h n t => h).
Global Arguments hd {A} {n} v.


Definition last {A} := @rectS _ (fun _ _ => A) (fun a => a) (fun _ _ _ H => H).
Global Arguments last {A} {n} v.


Definition const {A} (a:A) := nat_rect _ [] (fun n x => cons _ a n x).


Definition nth {A} :=
fix nth_fix {m} (v' : t A m) (p : Fin.t m) {struct v'} : A :=
match p in Fin.t m' return t A m' -> A with
|Fin.F1 => caseS (fun n v' => A) (fun h n t => h)
|Fin.FS p' => fun v => (caseS (fun n v' => Fin.t n -> A)
(fun h n t p0 => nth_fix t p0) v) p'
end v'.


Definition nth_order {A} {n} (v: t A n) {p} (H: p < n) :=
(nth v (Fin.of_nat_lt H)).


Fixpoint replace {A n} (v : t A n) (p: Fin.t n) (a : A) {struct p}: t A n :=
match p with
| @Fin.F1 k => fun v': t A (S k) => caseS' v' _ (fun h t => a :: t)
| @Fin.FS k p' => fun v' : t A (S k) =>
(caseS' v' (fun _ => t A (S k)) (fun h t => h :: (replace t p' a)))
end v.


Definition replace_order {A n} (v: t A n) {p} (H: p < n) :=
replace v (Fin.of_nat_lt H).


Definition tl {A} := @caseS _ (fun n v => t A n) (fun h n t => t).
Global Arguments tl {A} {n} v.


Definition shiftout {A} := @rectS _ (fun n _ => t A n) (fun a => [])
(fun h _ _ H => h :: H).
Global Arguments shiftout {A} {n} v.


Fixpoint shiftin {A} {n:nat} (a : A) (v:t A n) : t A (S n) :=
match v with
|[] => a :: []
|h :: t => h :: (shiftin a t)
end.


Definition shiftrepeat {A} := @rectS _ (fun n _ => t A (S (S n)))
(fun h =>  h :: h :: []) (fun h _ _ H => h :: H).
Global Arguments shiftrepeat {A} {n} v.


Fixpoint take {A} {n} (p:nat) (le:p <= n) (v:t A n) : t A p :=
match p as p return p <= n -> t A p with
| 0 => fun _ => []
| S p' => match v in t _ n return S p' <= n -> t A (S p') with
| []=> fun le => False_rect _ (Nat.nle_succ_0 p' le)
| x::xs => fun le => x::take p' (le_S_n p' _ le) xs
end
end le.


Lemma trunc : forall {A} {n} (p:nat), n > p -> t A n
-> t A (n - p).
Proof. try hammer_hook "VectorDef" "VectorDef.trunc". Undo.  
induction p as [| p f]; intros H v.
rewrite <- minus_n_O.
exact v.

apply shiftout.

rewrite minus_Sn_m.
apply f.
auto with *.
exact v.
auto with *.
Defined.


Fixpoint append {A}{n}{p} (v:t A n) (w:t A p):t A (n+p) :=
match v with
| [] => w
| a :: v' => a :: (append v' w)
end.

Infix "++" := append.




Fixpoint rev_append_tail {A n p} (v : t A n) (w: t A p)
: t A (tail_plus n p) :=
match v with
| [] => w
| a :: v' => rev_append_tail v' (a :: w)
end.

Import EqdepFacts.


Definition rev_append {A n p} (v: t A n) (w: t A p)
:t A (n + p) :=
rew <- (plus_tail_plus n p) in (rev_append_tail v w).


Definition rev {A n} (v : t A n) : t A n :=
rew <- (plus_n_O _) in (rev_append v []).

End BASES.
Local Notation "v [@ p ]" := (nth v p) (at level 1).

Section ITERATORS.



Definition map {A} {B} (f : A -> B) : forall {n} (v:t A n), t B n :=
fix map_fix {n} (v : t A n) : t B n := match v with
| [] => []
| a :: v' => (f a) :: (map_fix v')
end.


Definition map2 {A B C} (g:A -> B -> C) :
forall (n : nat), t A n -> t B n -> t C n :=
@rect2 _ _ (fun n _ _ => t C n) (nil C) (fun _ _ _ H a b => (g a b) :: H).
Global Arguments map2 {A B C} g {n} v1 v2.


Definition fold_left {A B:Type} (f:B->A->B): forall (b:B) {n} (v:t A n), B :=
fix fold_left_fix (b:B) {n} (v : t A n) : B := match v with
| [] => b
| a :: w => (fold_left_fix (f b a) w)
end.


Definition fold_right {A B : Type} (f : A->B->B) :=
fix fold_right_fix {n} (v : t A n) (b:B)
{struct v} : B :=
match v with
| [] => b
| a :: w => f a (fold_right_fix w b)
end.


Definition fold_right2 {A B C} (g:A -> B -> C -> C) (c: C) :=
@rect2 _ _ (fun _ _ _ => C) c (fun _ _ _ H a b => g a b H).



Definition fold_left2 {A B C: Type} (f : A -> B -> C -> A) :=
fix fold_left2_fix (a : A) {n} (v : t B n) : t C n -> A :=
match v in t _ n0 return t C n0 -> A with
|[] => fun w => case0 (fun _ => A) a w
|@cons _ vh vn vt => fun w =>
caseS' w (fun _ => A) (fun wh wt => fold_left2_fix (f a vh wh) vt wt)
end.

End ITERATORS.

Section SCANNING.
Inductive Forall {A} (P: A -> Prop): forall {n} (v: t A n), Prop :=
|Forall_nil: Forall P []
|Forall_cons {n} x (v: t A n): P x -> Forall P v -> Forall P (x::v).
Hint Constructors Forall.

Inductive Exists {A} (P:A->Prop): forall {n}, t A n -> Prop :=
|Exists_cons_hd {m} x (v: t A m): P x -> Exists P (x::v)
|Exists_cons_tl {m} x (v: t A m): Exists P v -> Exists P (x::v).
Hint Constructors Exists.

Inductive In {A} (a:A): forall {n}, t A n -> Prop :=
|In_cons_hd {m} (v: t A m): In a (a::v)
|In_cons_tl {m} x (v: t A m): In a v -> In a (x::v).
Hint Constructors In.

Inductive Forall2 {A B} (P:A->B->Prop): forall {n}, t A n -> t B n -> Prop :=
|Forall2_nil: Forall2 P [] []
|Forall2_cons {m} x1 x2 (v1:t A m) v2: P x1 x2 -> Forall2 P v1 v2 ->
Forall2 P (x1::v1) (x2::v2).
Hint Constructors Forall2.

Inductive Exists2 {A B} (P:A->B->Prop): forall {n}, t A n -> t B n -> Prop :=
|Exists2_cons_hd {m} x1 x2 (v1: t A m) (v2: t B m): P x1 x2 -> Exists2 P (x1::v1) (x2::v2)
|Exists2_cons_tl {m} x1 x2 (v1:t A m) v2: Exists2 P v1 v2 -> Exists2 P (x1::v1) (x2::v2).
Hint Constructors Exists2.

End SCANNING.

Section VECTORLIST.


Fixpoint of_list {A} (l : list A) : t A (length l) :=
match l as l' return t A (length l') with
|Datatypes.nil => []
|(h :: tail)%list => (h :: (of_list tail))
end.

Definition to_list {A}{n} (v : t A n) : list A :=
Eval cbv delta beta in fold_right (fun h H => Datatypes.cons h H) v Datatypes.nil.
End VECTORLIST.

Module VectorNotations.
Delimit Scope vector_scope with vector.
Notation "[ ]" := [] (format "[ ]") : vector_scope.
Notation "[]" := [] (compat "8.5") : vector_scope.
Notation "h :: t" := (h :: t) (at level 60, right associativity)
: vector_scope.
Notation "[ x ]" := (x :: []) : vector_scope.
Notation "[ x ; y ; .. ; z ]" := (cons _ x _ (cons _ y _ .. (cons _ z _ (nil _)) ..)) : vector_scope.
Notation "[ x ; .. ; y ]" := (cons _ x _ .. (cons _ y _ (nil _)) ..) (compat "8.4") : vector_scope.
Notation "v [@ p ]" := (nth v p) (at level 1, format "v [@ p ]") : vector_scope.
Open Scope vector_scope.
End VectorNotations.
