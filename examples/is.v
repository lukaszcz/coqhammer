From Hammer Require Import Hammer Reconstr.


Require Import ZArith Bool.

(* Require Import Coq.micromega.Lia.*)

Infix "-->" := implb (at level 60, right associativity) : bool_scope.
Infix "<-->" := Bool.eqb (at level 60, right associativity) : bool_scope.

Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Coercion is_true : bool >-> Sortclass.

Fixpoint insert (x:Z) (l:list Z) : list Z :=
  match l with
    | nil => x::nil
    | y::ys => if (x <=? y)%Z then x::y::ys else y::(insert x ys)
  end.

Fixpoint sort (l:list Z) : list Z :=
  match l with
    | nil => nil
    | x::xs => insert x (sort xs)
  end.

Fixpoint is_sorted (l:list Z) : bool :=
  match l with
    | nil => true
    | x::xs =>
    match xs with
      | nil => true
      | y::_ => (x <=? y)%Z && (is_sorted xs)
    end
  end.

Fixpoint smaller (x:Z) (l:list Z) : bool :=
  match l with
    | nil => true
    | y::ys => (x <=? y)%Z && (smaller x ys)
  end.

Lemma is_sorted_smaller x y ys: (((x <=? y) && is_sorted (y :: ys)) --> is_sorted (x :: ys)).
Proof. destruct ys as [ |z zs].
       - simpl. Reconstr.reasy Reconstr.Empty Reconstr.Empty.
       - change (is_sorted (y :: z :: zs)) with ((y <=? z)%Z && (is_sorted (z::zs))).
         change (is_sorted (x :: z :: zs)) with ((x <=? z)%Z && (is_sorted (z::zs))).
	       Reconstr.rcrush (@Coq.ZArith.Zbool.Zle_bool_trans) Reconstr.Empty.
Qed.

Lemma is_sorted_cons x xs: (is_sorted (x::xs)) <--> (is_sorted xs && smaller x xs).
Proof.
      induction xs as [ |y ys IHys].
      - easy.
      - simpl.
        generalize (is_sorted_smaller x y ys). 
        revert IHys.
        Reconstr.reasy Reconstr.Empty (@is_sorted).
Qed.

Lemma insert_keeps_smaller x y ys :
  smaller y ys --> (y <=? x) --> smaller y (insert x ys).
Proof.
  induction ys as [ |z zs IHzs].
  - simpl. Reconstr.reasy (@Coq.Init.Datatypes.true) Reconstr.Empty.
  - simpl. case (x <=? z).
    + cbn. Reconstr.reasy Reconstr.Empty Reconstr.Empty.
    + simpl. revert IHzs.
	    Reconstr.reasy Reconstr.Empty Reconstr.Empty.
Qed.

Lemma eq_false b : b = false <-> negb b.
Proof. 	Reconstr.reasy Reconstr.Empty Reconstr.Empty. Qed.

Lemma insert_keeps_sorted x l : is_sorted l -> is_sorted (insert x l).
Proof.
  induction l as [ |y ys IHys].
  - reflexivity.
  - intro H. cbn. case_eq (x <=? y); intro Heq.
    + revert IHys H Heq. cbn.
      Reconstr.reasy Reconstr.Empty Reconstr.Empty.
    + rewrite eq_false in Heq.
      revert IHys H Heq.
      generalize (insert_keeps_smaller x y ys).
      unfold negb.
      rewrite !(eqb_prop _ _ (is_sorted_cons _ _)).
	    Reconstr.reasy (@Coq.ZArith.BinInt.Z.leb_gt, 
       @Coq.ZArith.BinInt.Z.lt_le_incl, 
       @Coq.ZArith.Zbool.Zle_imp_le_bool) Reconstr.Empty.
Qed.

Theorem sort_sorts l : is_sorted (sort l).
Proof.
  induction l as [ |x xs IHxs].
  - reflexivity.
  - simpl. 
   	Reconstr.reasy (@insert_keeps_sorted) Reconstr.Empty.
Qed.

