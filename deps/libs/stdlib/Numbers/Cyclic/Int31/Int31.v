From Hammer Require Import Hammer.











Require Import NaryFunctions.
Require Import Wf_nat.
Require Export ZArith.
Require Export DoubleType.





Definition size := 31%nat.



Inductive digits : Type := D0 | D1.





Definition digits31 t := Eval compute in nfun digits size t.

Inductive int31 : Type := I31 : digits31 int31.


Register digits as int31 bits in "coq_int31" by True.
Register int31 as int31 type in "coq_int31" by True.

Delimit Scope int31_scope with int31.
Bind Scope int31_scope with int31.
Local Open Scope int31_scope.




Definition On : int31 := Eval compute in napply_cst _ _ D0 size I31.


Definition In : int31 := Eval compute in (napply_cst _ _ D0 (size-1) I31) D1.


Definition Tn : int31 := Eval compute in napply_cst _ _ D1 size I31.


Definition Twon : int31 := Eval compute in (napply_cst _ _ D0 (size-2) I31) D1 D0.






Definition sneakr : digits -> int31 -> int31 := Eval compute in
fun b => int31_rect _ (napply_except_last _ _ (size-1) (I31 b)).



Definition sneakl : digits -> int31 -> int31 := Eval compute in
fun b => int31_rect _ (fun _ => napply_then_last _ _ b (size-1) I31).




Definition shiftl := sneakl D0.
Definition shiftr := sneakr D0.
Definition twice := sneakl D0.
Definition twice_plus_one := sneakl D1.



Definition firstl : int31 -> digits := Eval compute in
int31_rect _ (fun d => napply_discard _ _ d (size-1)).



Definition firstr : int31 -> digits := Eval compute in
int31_rect _ (napply_discard _ _ (fun d=>d) (size-1)).



Definition iszero : int31 -> bool := Eval compute in
let f d b := match d with D0 => b | D1 => false end
in int31_rect _ (nfold_bis _ _ f true size).






Definition base := Eval compute in
iter_nat size Z Z.double 1%Z.



Fixpoint recl_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int31->A->A)
(i:int31) : A :=
match n with
| O => case0
| S next =>
if iszero i then
case0
else
let si := shiftl i in
caserec (firstl i) si (recl_aux next A case0 caserec si)
end.

Fixpoint recr_aux (n:nat)(A:Type)(case0:A)(caserec:digits->int31->A->A)
(i:int31) : A :=
match n with
| O => case0
| S next =>
if iszero i then
case0
else
let si := shiftr i in
caserec (firstr i) si (recr_aux next A case0 caserec si)
end.

Definition recl := recl_aux size.
Definition recr := recr_aux size.





Definition phi : int31 -> Z :=
recr Z (0%Z)
(fun b _ => match b with D0 => Z.double | D1 => Z.succ_double end).



Fixpoint phi_inv_positive p :=
match p with
| xI q => twice_plus_one (phi_inv_positive q)
| xO q => twice (phi_inv_positive q)
| xH => In
end.



Fixpoint complement_negative p :=
match p with
| xI q => twice (complement_negative q)
| xO q => twice_plus_one (complement_negative q)
| xH => twice Tn
end.



Definition incr : int31 -> int31 :=
recr int31 In
(fun b si rec => match b with
| D0 => sneakl D1 si
| D1 => sneakl D0 rec end).



Definition phi_inv : Z -> int31 := fun n =>
match n with
| Z0 => On
| Zpos p => phi_inv_positive p
| Zneg p => incr (complement_negative p)
end.



Definition phi_inv2 n :=
match n with
| Z0 => W0
| _ => WW (phi_inv (n/base)%Z) (phi_inv n)
end.



Definition phi2 nh nl :=
((phi nh)*base+(phi nl))%Z.





Definition add31 (n m : int31) := phi_inv ((phi n)+(phi m)).
Notation "n + m" := (add31 n m) : int31_scope.







Definition add31c (n m : int31) :=
let npm := n+m in
match (phi npm ?= (phi n)+(phi m))%Z with
| Eq => C0 npm
| _ => C1 npm
end.
Notation "n '+c' m" := (add31c n m) (at level 50, no associativity) : int31_scope.



Definition add31carryc (n m : int31) :=
let npmpone_exact := ((phi n)+(phi m)+1)%Z in
let npmpone := phi_inv npmpone_exact in
match (phi npmpone ?= npmpone_exact)%Z with
| Eq => C0 npmpone
| _ => C1 npmpone
end.





Definition sub31 (n m : int31) := phi_inv ((phi n)-(phi m)).
Notation "n - m" := (sub31 n m) : int31_scope.



Definition sub31c (n m : int31) :=
let nmm := n-m in
match (phi nmm ?= (phi n)-(phi m))%Z with
| Eq => C0 nmm
| _ => C1 nmm
end.
Notation "n '-c' m" := (sub31c n m) (at level 50, no associativity) : int31_scope.



Definition sub31carryc (n m : int31) :=
let nmmmone_exact := ((phi n)-(phi m)-1)%Z in
let nmmmone := phi_inv nmmmone_exact in
match (phi nmmmone ?= nmmmone_exact)%Z with
| Eq => C0 nmmmone
| _ => C1 nmmmone
end.



Definition opp31 x := On - x.
Notation "- x" := (opp31 x) : int31_scope.





Definition mul31 (n m : int31) := phi_inv ((phi n)*(phi m)).
Notation "n * m" := (mul31 n m) : int31_scope.



Definition mul31c (n m : int31) := phi_inv2 ((phi n)*(phi m)).
Notation "n '*c' m" := (mul31c n m) (at level 40, no associativity) : int31_scope.






Definition div3121 (nh nl m : int31) :=
let (q,r) := Z.div_eucl (phi2 nh nl) (phi m) in
(phi_inv q, phi_inv r).



Definition div31 (n m : int31) :=
let (q,r) := Z.div_eucl (phi n) (phi m) in
(phi_inv q, phi_inv r).
Notation "n / m" := (div31 n m) : int31_scope.




Definition compare31 (n m : int31) := ((phi n)?=(phi m))%Z.
Notation "n ?= m" := (compare31 n m) (at level 70, no associativity) : int31_scope.

Definition eqb31 (n m : int31) :=
match n ?= m with Eq => true | _ => false end.




Definition iter_int31 i A f :=
recr (A->A) (fun x => x)
(fun b si rec => match b with
| D0 => fun x => rec (rec x)
| D1 => fun x => f (rec (rec x))
end)
i.



Definition addmuldiv31 p i j :=
let (res, _ ) :=
iter_int31 p (int31*int31)
(fun ij => let (i,j) := ij in (sneakl (firstl j) i, shiftl j))
(i,j)
in
res.



Definition lor31 n m := phi_inv (Z.lor (phi n) (phi m)).
Definition land31 n m := phi_inv (Z.land (phi n) (phi m)).
Definition lxor31 n m := phi_inv (Z.lxor (phi n) (phi m)).

Register add31 as int31 plus in "coq_int31" by True.
Register add31c as int31 plusc in "coq_int31" by True.
Register add31carryc as int31 pluscarryc in "coq_int31" by True.
Register sub31 as int31 minus in "coq_int31" by True.
Register sub31c as int31 minusc in "coq_int31" by True.
Register sub31carryc as int31 minuscarryc in "coq_int31" by True.
Register mul31 as int31 times in "coq_int31" by True.
Register mul31c as int31 timesc in "coq_int31" by True.
Register div3121 as int31 div21 in "coq_int31" by True.
Register div31 as int31 diveucl in "coq_int31" by True.
Register compare31 as int31 compare in "coq_int31" by True.
Register addmuldiv31 as int31 addmuldiv in "coq_int31" by True.
Register lor31 as int31 lor in "coq_int31" by True.
Register land31 as int31 land in "coq_int31" by True.
Register lxor31 as int31 lxor in "coq_int31" by True.

Definition lnot31 n := lxor31 Tn n.
Definition ldiff31 n m := land31 n (lnot31 m).

Fixpoint euler (guard:nat) (i j:int31) {struct guard} :=
match guard with
| O => In
| S p => match j ?= On with
| Eq => i
| _ => euler p j (let (_, r ) := i/j in r)
end
end.

Definition gcd31 (i j:int31) := euler (2*size)%nat i j.





Definition sqrt31_step (rec: int31 -> int31 -> int31) (i j: int31)  :=
Eval lazy delta [Twon] in
let (quo,_) := i/j in
match quo ?= j with
Lt => rec i (fst ((j + quo)/Twon))
| _ =>  j
end.

Fixpoint iter31_sqrt (n: nat) (rec: int31 -> int31 -> int31)
(i j: int31) {struct n} : int31 :=
sqrt31_step
(match n with
O =>  rec
| S n => (iter31_sqrt n (iter31_sqrt n rec))
end) i j.

Definition sqrt31 i :=
Eval lazy delta [On In Twon] in
match compare31 In i with
Gt => On
| Eq => In
| Lt => iter31_sqrt 31 (fun i j => j) i (fst (i/Twon))
end.

Definition v30 := Eval compute in (addmuldiv31 (phi_inv (Z.of_nat size - 1)) In On).

Definition sqrt312_step (rec: int31 -> int31 -> int31 -> int31)
(ih il j: int31)  :=
Eval lazy delta [Twon v30] in
match ih ?= j with Eq => j | Gt => j | _ =>
let (quo,_) := div3121 ih il j in
match quo ?= j with
Lt => let m := match j +c quo with
C0 m1 => fst (m1/Twon)
| C1 m1 => fst (m1/Twon) + v30
end in rec ih il m
| _ =>  j
end end.

Fixpoint iter312_sqrt (n: nat)
(rec: int31  -> int31 -> int31 -> int31)
(ih il j: int31) {struct n} : int31 :=
sqrt312_step
(match n with
O =>  rec
| S n => (iter312_sqrt n (iter312_sqrt n rec))
end) ih il j.

Definition sqrt312 ih il :=
Eval lazy delta [On In] in
let s := iter312_sqrt 31 (fun ih il j => j) ih il Tn in
match s *c s with
W0 => (On, C0 On)
| WW ih1 il1 =>
match il -c il1 with
C0 il2 =>
match ih ?= ih1 with
Gt => (s, C1 il2)
| _  => (s, C0 il2)
end
| C1 il2 =>
match (ih - In) ?= ih1 with
Gt => (s, C1 il2)
| _  => (s, C0 il2)
end
end
end.


Fixpoint p2i n p : (N*int31)%type :=
match n with
| O => (Npos p, On)
| S n => match p with
| xO p => let (r,i) := p2i n p in (r, Twon*i)
| xI p => let (r,i) := p2i n p in (r, Twon*i+In)
| xH => (N0, In)
end
end.

Definition positive_to_int31 (p:positive) := p2i size p.



Definition T31 : int31 := Eval compute in phi_inv (Z.of_nat size).

Definition head031 (i:int31) :=
recl _ (fun _ => T31)
(fun b si rec n => match b with
| D0 => rec (add31 n In)
| D1 => n
end)
i On.

Definition tail031 (i:int31) :=
recr _ (fun _ => T31)
(fun b si rec n => match b with
| D0 => rec (add31 n In)
| D1 => n
end)
i On.

Register head031 as int31 head0 in "coq_int31" by True.
Register tail031 as int31 tail0 in "coq_int31" by True.
