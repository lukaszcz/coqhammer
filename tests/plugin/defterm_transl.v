(* Focused translation regression for the term half of a definitional equation.

   A transparent Prop-valued definition names a proposition, and the
   translation says what it names with a propositional equivalence: the
   constant applied to its arguments holds exactly when its unfolding does.
   That is the whole story only for as long as the constant stands where a
   formula is expected.  It does not always stand there.  A proposition also
   occurs in *term* position -- as the type argument an erased proof leaves
   behind, the [Prop] index carried by a sumbool or a subset being the common
   case -- and there the two spellings of one delta-convertible proposition are
   simply two distinct terms.  A case equation that writes an erased proof's
   type as [lt a b] and a typing guard that writes the same type as
   [le (S b) a] can then never meet: the only axiom relating them equates their
   truth values, and in term position there is no formula to apply it to.  The
   eval watch point [dep_idiv_zero] was CounterSatisfiable for exactly this
   reason.

   The remedy is the extra [$_def_<name>$term] equation, which states that the
   two sides are the same object.  It is justified by conversion -- the same
   argument that justifies a [$_link_] equation between two lifts of one term
   -- and it is emitted *alongside* the equivalence, never instead of it: the
   equivalence remains what lets the proposition be used as a formula.

   Pinned here: [ltx], whose body is an atomic proposition, gets both axioms.
   The negatives get the equivalence alone.  [conj2]'s body is headed by a
   connective and [allpos]'s is quantified, so their translations are formulae
   built from connectives and binders, with no term for an equation to be
   stated over.  [wfle] is well-founded recursive, and its equation is a Coq
   theorem only under the erased premises of [Fix_eq] rather than a conversion,
   so reading it as an identity of terms would not be sound. *)

From Hammer Require Import Hammer.
From Stdlib Require Import Program.Wf.

(* Positive: the body is an application of a constant, so it denotes a term. *)
Definition ltx (n m : nat) : Prop := le (S n) m.

(* Negative: the body is headed by a logical connective. *)
Definition conj2 (P Q : Prop) : Prop := P /\ Q.

(* Negative: the body is quantified. *)
Definition allpos (P : nat -> Prop) : Prop := forall n, P n.

(* Negative: well-founded recursion.  No recursive call is needed to exercise
   the guard -- the [measure] annotation alone routes the body through
   [Fix_sub], which is what marks the equation as a theorem under erased
   premises instead of a conversion.  The body is otherwise exactly as atomic
   as [ltx]'s, so this is the guard and nothing else. *)
Program Fixpoint wfle (n m : nat) {measure n} : Prop := le n m.

Hammer_transl "ltx".
Hammer_transl "conj2".
Hammer_transl "allpos".
Hammer_transl "wfle".
