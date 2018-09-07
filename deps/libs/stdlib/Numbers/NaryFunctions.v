From Hammer Require Import Hammer.











Local Open Scope type_scope.

Require Import List.





Fixpoint nfun A n B :=
match n with
| O => B
| S n => A -> (nfun A n B)
end.

Notation " A ^^ n --> B " := (nfun A n B)
(at level 50, n at next level) : type_scope.



Fixpoint napply_cst (A B:Type)(a:A) n : (A^^n-->B) -> B :=
match n return (A^^n-->B) -> B with
| O => fun x => x
| S n => fun x => napply_cst _ _ a n (x a)
end.




Fixpoint nfun_to_nfun (A B C:Type)(f:B -> C) n :
(A^^n-->B) -> (A^^n-->C) :=
match n return (A^^n-->B) -> (A^^n-->C) with
| O => f
| S n => fun g a => nfun_to_nfun _ _ _ f n (g a)
end.



Definition napply_except_last (A B:Type) :=
nfun_to_nfun A B (A->B) (fun b a => b).



Definition napply_then_last (A B:Type)(a:A) :=
nfun_to_nfun A (A->B) B (fun fab => fab a).



Fixpoint napply_discard (A B:Type)(b:B) n : A^^n-->B :=
match n return A^^n-->B with
| O => b
| S n => fun _ => napply_discard _ _ b n
end.



Fixpoint nfold A B (f:A->B->B)(b:B) n : (A^^n-->B) :=
match n return (A^^n-->B) with
| O => b
| S n => fun a => (nfold _ _ f (f a b) n)
end.




Fixpoint nprod A n : Type := match n with
| O => unit
| S n => (A * nprod A n)%type
end.

Notation "A ^ n" := (nprod A n) : type_scope.



Fixpoint ncurry (A B:Type) n : (A^n -> B) -> (A^^n-->B) :=
match n return (A^n -> B) -> (A^^n-->B) with
| O => fun x => x tt
| S n => fun f a => ncurry _ _ n (fun p => f (a,p))
end.

Fixpoint nuncurry (A B:Type) n : (A^^n-->B) -> (A^n -> B) :=
match n return (A^^n-->B) -> (A^n -> B) with
| O => fun x _ => x
| S n => fun f p => let (x,p) := p in nuncurry _ _ n (f x) p
end.



Definition nfun_to_nfun_bis A B C (f:B->C) n :
(A^^n-->B) -> (A^^n-->C) :=
fun anb => ncurry _ _ n (fun an => f ((nuncurry _ _ n anb) an)).



Fixpoint nfold_bis A B (f:A->B->B)(b:B) n : (A^^n-->B) :=
match n return (A^^n-->B) with
| O => b
| S n => fun a =>
nfun_to_nfun_bis _ _ _ (f a) n (nfold_bis _ _ f b n)
end.



Fixpoint nprod_to_list (A:Type) n : A^n -> list A :=
match n with
| O => fun _ => nil
| S n => fun p => let (x,p) := p in x::(nprod_to_list _ n p)
end.



Fixpoint nprod_of_list (A:Type)(l:list A) : A^(length l) :=
match l return A^(length l) with
| nil => tt
| x::l => (x, nprod_of_list _ l)
end.



Definition nfold_list (A B:Type)(f:A->B->B)(b:B) n : (A^^n-->B) :=
ncurry _ _ n (fun p => fold_right f b (nprod_to_list _ _ p)).

