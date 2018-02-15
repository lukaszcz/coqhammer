From Hammer Require Import Hammer.









Require Export BinNums.
Require Import BinPos.

Local Open Scope N_scope.





Module N.

Definition t := N.



Notation pos := Npos.



Definition zero := 0.
Definition one := 1.
Definition two := 2.



Definition succ_double x :=
match x with
| 0 => 1
| pos p => pos p~1
end.



Definition double n :=
match n with
| 0 => 0
| pos p => pos p~0
end.



Definition succ n :=
match n with
| 0 => 1
| pos p => pos (Pos.succ p)
end.



Definition pred n :=
match n with
| 0 => 0
| pos p => Pos.pred_N p
end.



Definition succ_pos (n : N) : positive :=
match n with
| 0 => 1%positive
| pos p => Pos.succ p
end.



Definition add n m :=
match n, m with
| 0, _ => m
| _, 0 => n
| pos p, pos q => pos (p + q)
end.

Infix "+" := add : N_scope.



Definition sub n m :=
match n, m with
| 0, _ => 0
| n, 0 => n
| pos n', pos m' =>
match Pos.sub_mask n' m' with
| IsPos p => pos p
| _ => 0
end
end.

Infix "-" := sub : N_scope.



Definition mul n m :=
match n, m with
| 0, _ => 0
| _, 0 => 0
| pos p, pos q => pos (p * q)
end.

Infix "*" := mul : N_scope.



Definition compare n m :=
match n, m with
| 0, 0 => Eq
| 0, pos m' => Lt
| pos n', 0 => Gt
| pos n', pos m' => (n' ?= m')%positive
end.

Infix "?=" := compare (at level 70, no associativity) : N_scope.



Fixpoint eqb n m :=
match n, m with
| 0, 0 => true
| pos p, pos q => Pos.eqb p q
| _, _ => false
end.

Definition leb x y :=
match x ?= y with Gt => false | _ => true end.

Definition ltb x y :=
match x ?= y with Lt => true | _ => false end.

Infix "=?" := eqb (at level 70, no associativity) : N_scope.
Infix "<=?" := leb (at level 70, no associativity) : N_scope.
Infix "<?" := ltb (at level 70, no associativity) : N_scope.



Definition min n n' := match n ?= n' with
| Lt | Eq => n
| Gt => n'
end.

Definition max n n' := match n ?= n' with
| Lt | Eq => n'
| Gt => n
end.



Definition div2 n :=
match n with
| 0 => 0
| 1 => 0
| pos (p~0) => pos p
| pos (p~1) => pos p
end.



Definition even n :=
match n with
| 0 => true
| pos (xO _) => true
| _ => false
end.

Definition odd n := negb (even n).



Definition pow n p :=
match p, n with
| 0, _ => 1
| _, 0 => 0
| pos p, pos q => pos (q^p)
end.

Infix "^" := pow : N_scope.



Definition square n :=
match n with
| 0 => 0
| pos p => pos (Pos.square p)
end.



Definition log2 n :=
match n with
| 0 => 0
| 1 => 0
| pos (p~0) => pos (Pos.size p)
| pos (p~1) => pos (Pos.size p)
end.



Definition size n :=
match n with
| 0 => 0
| pos p => pos (Pos.size p)
end.

Definition size_nat n :=
match n with
| 0 => O
| pos p => Pos.size_nat p
end.



Fixpoint pos_div_eucl (a:positive)(b:N) : N * N :=
match a with
| xH =>
match b with 1 => (1,0) | _ => (0,1) end
| xO a' =>
let (q, r) := pos_div_eucl a' b in
let r' := double r in
if b <=? r' then (succ_double q, r' - b)
else (double q, r')
| xI a' =>
let (q, r) := pos_div_eucl a' b in
let r' := succ_double r in
if b <=? r' then (succ_double q, r' - b)
else  (double q, r')
end.

Definition div_eucl (a b:N) : N * N :=
match a, b with
| 0,  _ => (0, 0)
| _, 0  => (0, a)
| pos na, _ => pos_div_eucl na b
end.

Definition div a b := fst (div_eucl a b).
Definition modulo a b := snd (div_eucl a b).

Infix "/" := div : N_scope.
Infix "mod" := modulo (at level 40, no associativity) : N_scope.



Definition gcd a b :=
match a, b with
| 0, _ => b
| _, 0 => a
| pos p, pos q => pos (Pos.gcd p q)
end.



Definition ggcd a b :=
match a, b with
| 0, _ => (b,(0,1))
| _, 0 => (a,(1,0))
| pos p, pos q =>
let '(g,(aa,bb)) := Pos.ggcd p q in
(pos g, (pos aa, pos bb))
end.



Definition sqrtrem n :=
match n with
| 0 => (0, 0)
| pos p =>
match Pos.sqrtrem p with
| (s, IsPos r) => (pos s, pos r)
| (s, _) => (pos s, 0)
end
end.

Definition sqrt n :=
match n with
| 0 => 0
| pos p => pos (Pos.sqrt p)
end.





Definition lor n m :=
match n, m with
| 0, _ => m
| _, 0 => n
| pos p, pos q => pos (Pos.lor p q)
end.



Definition land n m :=
match n, m with
| 0, _ => 0
| _, 0 => 0
| pos p, pos q => Pos.land p q
end.



Fixpoint ldiff n m :=
match n, m with
| 0, _ => 0
| _, 0 => n
| pos p, pos q => Pos.ldiff p q
end.



Definition lxor n m :=
match n, m with
| 0, _ => m
| _, 0 => n
| pos p, pos q => Pos.lxor p q
end.



Definition shiftl_nat (a:N) := nat_rect _ a (fun _ => double).
Definition shiftr_nat (a:N) := nat_rect _ a (fun _ => div2).

Definition shiftl a n :=
match a with
| 0 => 0
| pos a => pos (Pos.shiftl a n)
end.

Definition shiftr a n :=
match n with
| 0 => a
| pos p => Pos.iter div2 a p
end.



Definition testbit_nat (a:N) :=
match a with
| 0 => fun _ => false
| pos p => Pos.testbit_nat p
end.



Definition testbit a n :=
match a with
| 0 => false
| pos p => Pos.testbit p n
end.



Definition to_nat (a:N) :=
match a with
| 0 => O
| pos p => Pos.to_nat p
end.

Definition of_nat (n:nat) :=
match n with
| O => 0
| S n' => pos (Pos.of_succ_nat n')
end.



Definition iter (n:N) {A} (f:A->A) (x:A) : A :=
match n with
| 0 => x
| pos p => Pos.iter f x p
end.

End N.
