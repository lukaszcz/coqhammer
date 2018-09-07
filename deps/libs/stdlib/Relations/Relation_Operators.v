From Hammer Require Import Hammer.





















Require Import Relation_Definitions.



Section Transitive_Closure.
Variable A : Type.
Variable R : relation A.



Inductive clos_trans (x: A) : A -> Prop :=
| t_step (y:A) : R x y -> clos_trans x y
| t_trans (y z:A) : clos_trans x y -> clos_trans y z -> clos_trans x z.



Inductive clos_trans_1n (x: A) : A -> Prop :=
| t1n_step (y:A) : R x y -> clos_trans_1n x y
| t1n_trans (y z:A) : R x y -> clos_trans_1n y z -> clos_trans_1n x z.



Inductive clos_trans_n1 (x: A) : A -> Prop :=
| tn1_step (y:A) : R x y -> clos_trans_n1 x y
| tn1_trans (y z:A) : R y z -> clos_trans_n1 x y -> clos_trans_n1 x z.

End Transitive_Closure.



Section Reflexive_Closure.
Variable A : Type.
Variable R : relation A.



Inductive clos_refl (x: A) : A -> Prop :=
| r_step (y:A) : R x y -> clos_refl x y
| r_refl : clos_refl x x.

End Reflexive_Closure.



Section Reflexive_Transitive_Closure.
Variable A : Type.
Variable R : relation A.



Inductive clos_refl_trans (x:A) : A -> Prop :=
| rt_step (y:A) : R x y -> clos_refl_trans x y
| rt_refl : clos_refl_trans x x
| rt_trans (y z:A) :
clos_refl_trans x y -> clos_refl_trans y z -> clos_refl_trans x z.



Inductive clos_refl_trans_1n (x: A) : A -> Prop :=
| rt1n_refl : clos_refl_trans_1n x x
| rt1n_trans (y z:A) :
R x y -> clos_refl_trans_1n y z -> clos_refl_trans_1n x z.



Inductive clos_refl_trans_n1 (x: A) : A -> Prop :=
| rtn1_refl : clos_refl_trans_n1 x x
| rtn1_trans (y z:A) :
R y z -> clos_refl_trans_n1 x y -> clos_refl_trans_n1 x z.

End Reflexive_Transitive_Closure.



Section Reflexive_Symmetric_Transitive_Closure.
Variable A : Type.
Variable R : relation A.



Inductive clos_refl_sym_trans : relation A :=
| rst_step (x y:A) : R x y -> clos_refl_sym_trans x y
| rst_refl (x:A) : clos_refl_sym_trans x x
| rst_sym (x y:A) : clos_refl_sym_trans x y -> clos_refl_sym_trans y x
| rst_trans (x y z:A) :
clos_refl_sym_trans x y ->
clos_refl_sym_trans y z -> clos_refl_sym_trans x z.



Inductive clos_refl_sym_trans_1n (x: A) : A -> Prop :=
| rst1n_refl : clos_refl_sym_trans_1n x x
| rst1n_trans (y z:A) : R x y \/ R y x ->
clos_refl_sym_trans_1n y z -> clos_refl_sym_trans_1n x z.



Inductive clos_refl_sym_trans_n1 (x: A) : A -> Prop :=
| rstn1_refl : clos_refl_sym_trans_n1 x x
| rstn1_trans (y z:A) : R y z \/ R z y ->
clos_refl_sym_trans_n1 x y -> clos_refl_sym_trans_n1 x z.

End Reflexive_Symmetric_Transitive_Closure.



Section Converse.
Variable A : Type.
Variable R : relation A.

Definition transp (x y:A) := R y x.
End Converse.



Section Union.
Variable A : Type.
Variables R1 R2 : relation A.

Definition union (x y:A) := R1 x y \/ R2 x y.
End Union.



Section Disjoint_Union.
Variables A B : Type.
Variable leA : A -> A -> Prop.
Variable leB : B -> B -> Prop.

Inductive le_AsB : A + B -> A + B -> Prop :=
| le_aa (x y:A) : leA x y -> le_AsB (inl _ x) (inl _ y)
| le_ab (x:A) (y:B) : le_AsB (inl _ x) (inr _ y)
| le_bb (x y:B) : leB x y -> le_AsB (inr _ x) (inr _ y).

End Disjoint_Union.



Section Lexicographic_Product.

Variable A : Type.
Variable B : A -> Type.
Variable leA : A -> A -> Prop.
Variable leB : forall x:A, B x -> B x -> Prop.

Inductive lexprod : sigT B -> sigT B -> Prop :=
| left_lex :
forall (x x':A) (y:B x) (y':B x'),
leA x x' -> lexprod (existT B x y) (existT B x' y')
| right_lex :
forall (x:A) (y y':B x),
leB x y y' -> lexprod (existT B x y) (existT B x y').

End Lexicographic_Product.



Section Symmetric_Product.
Variable A : Type.
Variable B : Type.
Variable leA : A -> A -> Prop.
Variable leB : B -> B -> Prop.

Inductive symprod : A * B -> A * B -> Prop :=
| left_sym :
forall x x':A, leA x x' -> forall y:B, symprod (x, y) (x', y)
| right_sym :
forall y y':B, leB y y' -> forall x:A, symprod (x, y) (x, y').

End Symmetric_Product.



Section Swap.
Variable A : Type.
Variable R : A -> A -> Prop.

Inductive swapprod : A * A -> A * A -> Prop :=
| sp_noswap x y (p:A * A) : symprod A A R R (x, y) p -> swapprod (x, y) p
| sp_swap x y (p:A * A) : symprod A A R R (x, y) p -> swapprod (y, x) p.
End Swap.

Local Open Scope list_scope.

Section Lexicographic_Exponentiation.

Variable A : Set.
Variable leA : A -> A -> Prop.
Let Nil := nil (A:=A).
Let List := list A.

Inductive Ltl : List -> List -> Prop :=
| Lt_nil (a:A) (x:List) : Ltl Nil (a :: x)
| Lt_hd (a b:A) : leA a b -> forall x y:list A, Ltl (a :: x) (b :: y)
| Lt_tl (a:A) (x y:List) : Ltl x y -> Ltl (a :: x) (a :: y).

Inductive Desc : List -> Prop :=
| d_nil : Desc Nil
| d_one (x:A) : Desc (x :: Nil)
| d_conc (x y:A) (l:List) :
clos_refl A leA x y -> Desc (l ++ y :: Nil) -> Desc ((l ++ y :: Nil) ++ x :: Nil).

Definition Pow : Set := sig Desc.

Definition lex_exp (a b:Pow) : Prop := Ltl (proj1_sig a) (proj1_sig b).

End Lexicographic_Exponentiation.

Hint Unfold transp union: sets.
Hint Resolve t_step rt_step rt_refl rst_step rst_refl: sets.
Hint Immediate rst_sym: sets.



Notation rts1n_refl := rst1n_refl (only parsing).
Notation rts1n_trans := rst1n_trans (only parsing).
Notation rtsn1_refl := rstn1_refl (only parsing).
Notation rtsn1_trans := rstn1_trans (only parsing).

