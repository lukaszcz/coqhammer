From Hammer Require Import Hammer.









Require Import NAxioms NSub NZDiv.



Module Type NDivProp (Import N : NAxiomsSig')(Import NP : NSubProp N).


Module Import Private_NZDiv := Nop <+ NZDivProp N N NP.

Ltac auto' := try rewrite <- neq_0_lt_0; auto using le_0_l.



Lemma mod_upper_bound : forall a b, b ~= 0 -> a mod b < b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_upper_bound".   intros. apply mod_bound_pos; auto'. Qed.



Lemma mod_eq :
forall a b, b~=0 -> a mod b == a - b*(a/b).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_eq".  
intros.
symmetry. apply add_sub_eq_l. symmetry.
now apply div_mod.
Qed.



Theorem div_mod_unique :
forall b q1 q2 r1 r2, r1<b -> r2<b ->
b*q1+r1 == b*q2+r2 -> q1 == q2 /\ r1 == r2.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_mod_unique".   intros. apply div_mod_unique with b; auto'. Qed.

Theorem div_unique:
forall a b q r, r<b -> a == b*q + r -> q == a/b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_unique".   intros; apply div_unique with r; auto'. Qed.

Theorem mod_unique:
forall a b q r, r<b -> a == b*q + r -> r == a mod b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_unique".   intros. apply mod_unique with q; auto'. Qed.

Theorem div_unique_exact: forall a b q, b~=0 -> a == b*q -> q == a/b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_unique_exact".   intros. apply div_unique_exact; auto'. Qed.



Lemma div_same : forall a, a~=0 -> a/a == 1.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_same".   intros. apply div_same; auto'. Qed.

Lemma mod_same : forall a, a~=0 -> a mod a == 0.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_same".   intros. apply mod_same; auto'. Qed.



Theorem div_small: forall a b, a<b -> a/b == 0.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_small".   intros. apply div_small; auto'. Qed.



Theorem mod_small: forall a b, a<b -> a mod b == a.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_small".   intros. apply mod_small; auto'. Qed.



Lemma div_0_l: forall a, a~=0 -> 0/a == 0.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_0_l".   intros. apply div_0_l; auto'. Qed.

Lemma mod_0_l: forall a, a~=0 -> 0 mod a == 0.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_0_l".   intros. apply mod_0_l; auto'. Qed.

Lemma div_1_r: forall a, a/1 == a.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_1_r".   intros. apply div_1_r; auto'. Qed.

Lemma mod_1_r: forall a, a mod 1 == 0.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_1_r".   intros. apply mod_1_r; auto'. Qed.

Lemma div_1_l: forall a, 1<a -> 1/a == 0.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_1_l".   exact div_1_l. Qed.

Lemma mod_1_l: forall a, 1<a -> 1 mod a == 1.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_1_l".   exact mod_1_l. Qed.

Lemma div_mul : forall a b, b~=0 -> (a*b)/b == a.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_mul".   intros. apply div_mul; auto'. Qed.

Lemma mod_mul : forall a b, b~=0 -> (a*b) mod b == 0.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_mul".   intros. apply mod_mul; auto'. Qed.






Theorem mod_le: forall a b, b~=0 -> a mod b <= a.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_le".   intros. apply mod_le; auto'. Qed.

Lemma div_str_pos : forall a b, 0<b<=a -> 0 < a/b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_str_pos".   exact div_str_pos. Qed.

Lemma div_small_iff : forall a b, b~=0 -> (a/b==0 <-> a<b).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_small_iff".   intros. apply div_small_iff; auto'. Qed.

Lemma mod_small_iff : forall a b, b~=0 -> (a mod b == a <-> a<b).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_small_iff".   intros. apply mod_small_iff; auto'. Qed.

Lemma div_str_pos_iff : forall a b, b~=0 -> (0<a/b <-> b<=a).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_str_pos_iff".   intros. apply div_str_pos_iff; auto'. Qed.




Lemma div_lt : forall a b, 0<a -> 1<b -> a/b < a.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_lt".   exact div_lt. Qed.



Lemma div_le_mono : forall a b c, c~=0 -> a<=b -> a/c <= b/c.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_le_mono".   intros. apply div_le_mono; auto'. Qed.

Lemma mul_div_le : forall a b, b~=0 -> b*(a/b) <= a.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mul_div_le".   intros. apply mul_div_le; auto'. Qed.

Lemma mul_succ_div_gt: forall a b, b~=0 -> a < b*(S (a/b)).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mul_succ_div_gt".   intros; apply mul_succ_div_gt; auto'. Qed.



Lemma div_exact : forall a b, b~=0 -> (a == b*(a/b) <-> a mod b == 0).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_exact".   intros. apply div_exact; auto'. Qed.



Theorem div_lt_upper_bound:
forall a b q, b~=0 -> a < b*q -> a/b < q.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_lt_upper_bound".   intros. apply div_lt_upper_bound; auto'. Qed.

Theorem div_le_upper_bound:
forall a b q, b~=0 -> a <= b*q -> a/b <= q.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_le_upper_bound".   intros; apply div_le_upper_bound; auto'. Qed.

Theorem div_le_lower_bound:
forall a b q, b~=0 -> b*q <= a -> q <= a/b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_le_lower_bound".   intros; apply div_le_lower_bound; auto'. Qed.



Lemma div_le_compat_l: forall p q r, 0<q<=r -> p/r <= p/q.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_le_compat_l".   intros. apply div_le_compat_l. auto'. auto. Qed.



Lemma mod_add : forall a b c, c~=0 ->
(a + b * c) mod c == a mod c.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_add".   intros. apply mod_add; auto'. Qed.

Lemma div_add : forall a b c, c~=0 ->
(a + b * c) / c == a / c + b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_add".   intros. apply div_add; auto'. Qed.

Lemma div_add_l: forall a b c, b~=0 ->
(a * b + c) / b == a + c / b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_add_l".   intros. apply div_add_l; auto'. Qed.



Lemma div_mul_cancel_r : forall a b c, b~=0 -> c~=0 ->
(a*c)/(b*c) == a/b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_mul_cancel_r".   intros. apply div_mul_cancel_r; auto'. Qed.

Lemma div_mul_cancel_l : forall a b c, b~=0 -> c~=0 ->
(c*a)/(c*b) == a/b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_mul_cancel_l".   intros. apply div_mul_cancel_l; auto'. Qed.

Lemma mul_mod_distr_r: forall a b c, b~=0 -> c~=0 ->
(a*c) mod (b*c) == (a mod b) * c.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mul_mod_distr_r".   intros. apply mul_mod_distr_r; auto'. Qed.

Lemma mul_mod_distr_l: forall a b c, b~=0 -> c~=0 ->
(c*a) mod (c*b) == c * (a mod b).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mul_mod_distr_l".   intros. apply mul_mod_distr_l; auto'. Qed.



Theorem mod_mod: forall a n, n~=0 ->
(a mod n) mod n == a mod n.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_mod".   intros. apply mod_mod; auto'. Qed.

Lemma mul_mod_idemp_l : forall a b n, n~=0 ->
((a mod n)*b) mod n == (a*b) mod n.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mul_mod_idemp_l".   intros. apply mul_mod_idemp_l; auto'. Qed.

Lemma mul_mod_idemp_r : forall a b n, n~=0 ->
(a*(b mod n)) mod n == (a*b) mod n.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mul_mod_idemp_r".   intros. apply mul_mod_idemp_r; auto'. Qed.

Theorem mul_mod: forall a b n, n~=0 ->
(a * b) mod n == ((a mod n) * (b mod n)) mod n.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mul_mod".   intros. apply mul_mod; auto'. Qed.

Lemma add_mod_idemp_l : forall a b n, n~=0 ->
((a mod n)+b) mod n == (a+b) mod n.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.add_mod_idemp_l".   intros. apply add_mod_idemp_l; auto'. Qed.

Lemma add_mod_idemp_r : forall a b n, n~=0 ->
(a+(b mod n)) mod n == (a+b) mod n.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.add_mod_idemp_r".   intros. apply add_mod_idemp_r; auto'. Qed.

Theorem add_mod: forall a b n, n~=0 ->
(a+b) mod n == (a mod n + b mod n) mod n.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.add_mod".   intros. apply add_mod; auto'. Qed.

Lemma div_div : forall a b c, b~=0 -> c~=0 ->
(a/b)/c == a/(b*c).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_div".   intros. apply div_div; auto'. Qed.

Lemma mod_mul_r : forall a b c, b~=0 -> c~=0 ->
a mod (b*c) == a mod b + b*((a/b) mod c).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_mul_r".   intros. apply mod_mul_r; auto'. Qed.



Theorem div_mul_le:
forall a b c, b~=0 -> c*(a/b) <= (c*a)/b.
Proof. hammer_hook "NDiv" "NDiv.NDivProp.div_mul_le".   intros. apply div_mul_le; auto'. Qed.



Lemma mod_divides : forall a b, b~=0 ->
(a mod b == 0 <-> exists c, a == b*c).
Proof. hammer_hook "NDiv" "NDiv.NDivProp.mod_divides".   intros. apply mod_divides; auto'. Qed.

End NDivProp.
