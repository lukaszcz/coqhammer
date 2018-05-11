From Hammer Require Import Hammer.












Require Import Bool BinPos BinNat PeanoNat Nnat.
Declare ML Module "ascii_syntax_plugin".





Inductive ascii : Set := Ascii (_ _ _ _ _ _ _ _ : bool).

Delimit Scope char_scope with char.
Bind Scope char_scope with ascii.

Definition zero := Ascii false false false false false false false false.

Definition one := Ascii true false false false false false false false.

Definition shift (c : bool) (a : ascii) :=
match a with
| Ascii a1 a2 a3 a4 a5 a6 a7 a8 => Ascii c a1 a2 a3 a4 a5 a6 a7
end.



Definition ascii_dec : forall a b : ascii, {a = b} + {a <> b}.
Proof. try hammer_hook "Ascii" "Ascii.ascii_dec".  
decide equality; apply bool_dec.
Defined.





Definition ascii_of_pos : positive -> ascii :=
let loop := fix loop n p :=
match n with
| O => zero
| S n' =>
match p with
| xH => one
| xI p' => shift true (loop n' p')
| xO p' => shift false (loop n' p')
end
end
in loop 8.



Definition ascii_of_N (n : N) :=
match n with
| N0 => zero
| Npos p => ascii_of_pos p
end.



Definition ascii_of_nat (a : nat) := ascii_of_N (N.of_nat a).



Local Open Scope list_scope.

Fixpoint N_of_digits (l:list bool) : N :=
match l with
| nil => 0
| b :: l' => (if b then 1 else 0) + 2*(N_of_digits l')
end%N.

Definition N_of_ascii (a : ascii) : N :=
let (a0,a1,a2,a3,a4,a5,a6,a7) := a in
N_of_digits (a0::a1::a2::a3::a4::a5::a6::a7::nil).

Definition nat_of_ascii (a : ascii) : nat := N.to_nat (N_of_ascii a).



Theorem ascii_N_embedding :
forall a : ascii, ascii_of_N (N_of_ascii a) = a.
Proof. try hammer_hook "Ascii" "Ascii.ascii_N_embedding".  
destruct a as [[|][|][|][|][|][|][|][|]]; vm_compute; reflexivity.
Qed.

Theorem N_ascii_embedding :
forall n:N, (n < 256)%N -> N_of_ascii (ascii_of_N n) = n.
Proof. try hammer_hook "Ascii" "Ascii.N_ascii_embedding".  
destruct n.
reflexivity.
do 8 (destruct p; [ | | intros; vm_compute; reflexivity ]);
intro H; vm_compute in H; destruct p; discriminate.
Qed.

Theorem ascii_nat_embedding :
forall a : ascii, ascii_of_nat (nat_of_ascii a) = a.
Proof. try hammer_hook "Ascii" "Ascii.ascii_nat_embedding".  
destruct a as [[|][|][|][|][|][|][|][|]]; compute; reflexivity.
Qed.

Theorem nat_ascii_embedding :
forall n : nat, n < 256 -> nat_of_ascii (ascii_of_nat n) = n.
Proof. try hammer_hook "Ascii" "Ascii.nat_ascii_embedding".  
intros. unfold nat_of_ascii, ascii_of_nat.
rewrite N_ascii_embedding.
apply Nat2N.id.
unfold N.lt.
change 256%N with (N.of_nat 256).
rewrite <- Nat2N.inj_compare.
now apply Nat.compare_lt_iff.
Qed.






