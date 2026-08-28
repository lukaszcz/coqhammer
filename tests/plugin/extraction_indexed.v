(* Indexed-family translation fixtures.  extraction_transl.v replays these
   translations so check-extraction-transl.sh can assert their forded shapes. *)

From Hammer Require Import Hammer.

From Stdlib Require Import Arith.PeanoNat Bool.Bool Logic.JMeq.

Require Import extraction_deptypes.

Inductive breflect (P : Prop) : bool -> Set :=
| BReflectT : P -> breflect P true
| BReflectF : ~ P -> breflect P false.

Inductive tagged : nat -> Set :=
| tg : forall n, tagged n.

Definition untag n (t : tagged n) : nat :=
  match t with
  | tg n' => n'
  end.

Inductive ibounded : nat -> Set :=
| IBounded : forall n k, k < n -> ibounded n.

Definition ibval n (b : ibounded n) : nat :=
  match b with
  | IBounded _ k _ => k
  end.

(* The body reads the solved index rather than the carrier.  Fording must tie
   that index to the scrutinee's own index: left universally quantified it
   would occur only on the right-hand side of the branch equation, and the
   collapse of the constructor to its carrier would then equate every two
   indices. *)
Definition ibidx n (b : ibounded n) : nat :=
  match b with
  | IBounded n' _ _ => n'
  end.

(* An under-applied constructor of an indexed subset.  Its remaining fields are
   typed through the argument the result index fords, so eta-expanding the
   partial application must see that argument and not the index formal the
   classification substituted for it. *)
Definition ibpart := IBounded 5.

(* A parameter-dependent indexed subset cannot be collapsed occurrence by
   occurrence while its declaration keeps constructor injectivity: equal
   carriers at different indices would make those indices equal. *)
Inductive indexed_poly_subset (A : Type) : nat -> Type :=
| IndexedPolySubset : forall n (x : A), True -> indexed_poly_subset A n.

Definition indexed_poly_value A n (v : indexed_poly_subset A n) : A :=
  match v with
  | IndexedPolySubset _ _ x _ => x
  end.

Inductive okp (n : nat) : nat -> Prop :=
| ok_intro : okp n (S n).

Definition fromok n m (p : okp n m) : nat :=
  match p with
  | ok_intro _ => S n
  end.

Inductive isT : Type -> Prop :=
| is_nat : isT nat.

Definition fromisT (T : Type) (p : isT T) : T :=
  match p in isT U return U with
  | is_nat => 0
  end.

Inductive istrue : bool -> Prop :=
| istrue_intro : istrue true.

Definition fromtrue b (p : istrue b) : bool :=
  match p with
  | istrue_intro => true
  end.

Definition cast (A B : Type) (e : A = B) (x : A) : B :=
  match e in (_ = T) return T with
  | eq_refl => x
  end.

Inductive vec (A : Type) : nat -> Type :=
| vnil : vec A 0
| vcons : forall n, A -> vec A n -> vec A (S n).

Definition vhead (A : Type) (n : nat) (v : vec A (S n)) : A :=
  match v in vec _ m return (match m with 0 => unit | S _ => A end) with
  | vnil _ => tt
  | vcons _ _ a _ => a
  end.

(* [dswap]'s declared argument order differs from [dbox]'s.  Reading the
   scrutinee indices positionally from the declared type would therefore prune
   the live successor branch in the later rigid-clash pass. *)
Definition dheight2 {n} (b : dswap (S n) dred) : nat :=
  match b with
  | dbox_zero _ => 0
  | dbox_succ _ m _ => S m
  end.

Definition jmeq_match
    (A B : Type) (x : A) (y : B) (e : JMeq x y) : A :=
  match e with
  | JMeq_refl => x
  end.

Hammer_transl "breflect".
Hammer_transl "tagged".
Hammer_transl "untag".
Hammer_transl "ibounded".
Hammer_transl "ibval".
Hammer_transl "ibidx".
Hammer_transl "ibpart".
Hammer_transl "indexed_poly_subset".
Hammer_transl "indexed_poly_value".
Hammer_transl "okp".
Hammer_transl "fromok".
Hammer_transl "isT".
Hammer_transl "fromisT".
Hammer_transl "istrue".
Hammer_transl "fromtrue".
Hammer_transl "cast".
Hammer_transl "vec".
Hammer_transl "vhead".
Hammer_transl "dheight2".
Hammer_transl "jmeq_match".
