From Hammer Require Import Hammer.











Set Implicit Arguments.

Require Import ZArith.
Local Open Scope Z_scope.

Definition base digits := Z.pow 2 (Zpos digits).
Arguments base digits: simpl never.

Section Carry.

Variable A : Type.

Inductive carry :=
| C0 : A -> carry
| C1 : A -> carry.

Definition interp_carry (sign:Z)(B:Z)(interp:A -> Z) c :=
match c with
| C0 x => interp x
| C1 x => sign*B + interp x
end.

End Carry.

Section Zn2Z.

Variable znz : Type.



Inductive zn2z :=
| W0 : zn2z
| WW : znz -> znz -> zn2z.

Definition zn2z_to_Z (wB:Z) (w_to_Z:znz->Z) (x:zn2z) :=
match x with
| W0 => 0
| WW xh xl => w_to_Z xh * wB + w_to_Z xl
end.

End Zn2Z.

Arguments W0 {znz}.



Fixpoint word (w:Type) (n:nat) : Type :=
match n with
| O => w
| S n => zn2z (word w n)
end.
