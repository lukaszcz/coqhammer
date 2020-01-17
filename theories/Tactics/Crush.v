(* Copyright (c) 2008-2012, Adam Chlipala
 *
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

Require Import Coq.Logic.Eqdep Coq.Lists.List.

Require Import Omega.

Set Implicit Arguments.
Generalizable All Variables.

(** A version of [injection] that does some standard simplifications afterward: clear the hypothesis in question, bring the new facts above the double line, and attempt substitution for known variables. *)
Ltac inject H := injection H; clear H; intros; try subst.

(** Devious marker predicate to use for encoding state within proof goals *)
Definition done (T : Type) (x : T) := True.

(** Try calling tactic function [f] on all hypotheses, keeping the first application that doesn't fail. *)
Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

(** Run [f] on every element of [ls], not just the first that doesn't fail. *)
Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

(** Workhorse tactic to simplify hypotheses for a variety of proofs. *)
Ltac simplHyp :=
  (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
  let invert H F :=
      lazymatch F with
      | @done => fail
      | @done _ => fail
      | _ =>
        (** This case covers an inversion that succeeds immediately, meaning no constructors of [F] applied. *)
        (inversion H; fail)
        (** Otherwise, we only proceed if inversion eliminates all but one constructor case. *)
        || (inversion H; [idtac]; clear H; try subst)
      end
  in
  match goal with
    (** Eliminate all existential hypotheses. *)
    | [ H : ex _ |- _ ] => destruct H

    (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)

    (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
    | [ H : ?F _ |- _ ] => invert H F
    | [ H : ?F _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ _ |- _ ] => invert H F

    (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H

    (** If we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H

    (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.

(** Find some hypothesis to rewrite with, ensuring that [auto] proves all of the extra subgoals added by [rewrite]. *)
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

(** Combine [autorewrite] with automatic hypothesis rewrites. *)
Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
Ltac rewriter := autorewrite with core in *; rewriterP.

(** This one is just so darned useful, let's add it as a hint here. *)
Hint Rewrite app_ass.

(** Try a new instantiation of a universally quantified fact, proved by [e].
   * [trace] is an accumulator recording which instantiations we choose. *)
Ltac inster e trace :=
  (** Does [e] have any quantifiers left? *)
  match type of e with
    | forall x : _, _ =>
      (** Yes, so let's pick the first context variable of the right type. *)
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      (** No more quantifiers, so now we check if the trace we computed was already used. *)
      match trace with
        | (_, _) =>
          (** We only reach this case if the trace is nonempty, ensuring that [inster] fails if no progress can be made. *)
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              (** Uh oh, found a record of this trace in the context!  Backtrack to try another trace. *)
              fail 1
            | _ =>
              (** What is the type of the proof [e] now? *)
              let T := type of e in
                match type of T with
                  | Prop =>
                    (** [e] should be thought of as a proof, so let's add it to the context, and also add a new marker hypothesis recording our choice of trace. *)
                    generalize e; intro;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    (** [e] is something beside a proof.  Better make sure no element of our current trace was generated by a previous call to [inster], or we might get stuck in an infinite loop!  (We store previous [inster] terms in second positions of tuples used as arguments to [done] in hypotheses.  Proofs instantiated by [inster] merely use [tt] in such positions.) *)
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    (** Pick a new name for our new instantiation. *)
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.

(** After a round of application with the above, we will have a lot of junk [done] markers to clean up; hence this tactic. *)
Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

Require Import JMeq.

Ltac crush :=
  (** A useful combination of standard automation *)
  let sintuition := simpl in *; intuition; try subst;
                             repeat (simplHyp; intuition; try subst); try congruence in

  (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] =>
                match P with
                  | context[JMeq] => fail 1 (** JMeq is too fancy to deal with here. *)
                  | _ => rewrite H by crush
                end
            end; autorewrite with core in *) in

  (** Now the main sequence of heuristics: *)
    (sintuition; rewriter;
     repeat (appHyps ltac:(fun L => inster L L);
             repeat (simplHyp; intuition)); un_done;
     sintuition; rewriter; sintuition;
     (** End with a last attempt to prove an arithmetic fact with [omega], or prove any sort of fact in a context that is contradictory by reasoning that [omega] can do. *)
     try omega; try (elimtype False; omega)).

Ltac simplHyp0 :=
  match goal with
    (** Eliminate all existential hypotheses. *)
    | [ H : ex _ |- _ ] => destruct H

    (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)

    (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H

    (** If we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H

    (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.

Ltac crush0 :=
  (** A useful combination of standard automation *)
  let sintuition := simpl in *; intuition; try subst;
                             repeat (simplHyp0; intuition; try subst); try congruence in

  (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] =>
                match P with
                  | context[JMeq] => fail 1 (** JMeq is too fancy to deal with here. *)
                  | _ => rewrite H by crush0
                end
            end; autorewrite with core in *) in

  (** Now the main sequence of heuristics: *)
    (sintuition; rewriter;
     sintuition; rewriter; sintuition;
     (** End with a last attempt to prove an arithmetic fact with [omega], or prove any sort of fact in a context that is contradictory by reasoning that [omega] can do. *)
     try omega; try (elimtype False; omega)).
