From Hammer Require Import Hammer.











Require Export Bool Sumbool.
Require Vector.
Export Vector.VectorNotations.
Require Import Minus.

Local Open Scope nat_scope.



Section BOOLEAN_VECTORS.



Definition Bvector := Vector.t bool.

Definition Bnil := @Vector.nil bool.

Definition Bcons := @Vector.cons bool.

Definition Bvect_true := Vector.const true.

Definition Bvect_false := Vector.const false.

Definition Blow := @Vector.hd bool.

Definition Bhigh := @Vector.tl bool.

Definition Bsign := @Vector.last bool.

Definition Bneg := @Vector.map _ _ negb.

Definition BVand := @Vector.map2 _ _ _ andb.

Definition BVor := @Vector.map2 _ _ _ orb.

Definition BVxor := @Vector.map2 _ _ _ xorb.

Definition BshiftL (n:nat) (bv:Bvector (S n)) (carry:bool) :=
Bcons carry n (Vector.shiftout bv).

Definition BshiftRl (n:nat) (bv:Bvector (S n)) (carry:bool) :=
Bhigh (S n) (Vector.shiftin carry bv).

Definition BshiftRa (n:nat) (bv:Bvector (S n)) :=
Bhigh (S n) (Vector.shiftrepeat bv).

Fixpoint BshiftL_iter (n:nat) (bv:Bvector (S n)) (p:nat) : Bvector (S n) :=
match p with
| O => bv
| S p' => BshiftL n (BshiftL_iter n bv p') false
end.

Fixpoint BshiftRl_iter (n:nat) (bv:Bvector (S n)) (p:nat) : Bvector (S n) :=
match p with
| O => bv
| S p' => BshiftRl n (BshiftRl_iter n bv p') false
end.

Fixpoint BshiftRa_iter (n:nat) (bv:Bvector (S n)) (p:nat) : Bvector (S n) :=
match p with
| O => bv
| S p' => BshiftRa n (BshiftRa_iter n bv p')
end.

End BOOLEAN_VECTORS.

