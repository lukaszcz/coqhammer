Research problems
-----------------

1. Make boolean reflection work. Make CoqHammer usable with MathComp:
   this will probably require much more than just making boolean
   reflection work, probably including most of the points below.

2. Omit (some) type arguments (inductive type parameters? implicit
   type arguments?) to polymorphic functions/constructors
   (e.g. cons). Is it possible to determine which arguments are
   implicit at the Coq kernel level? Yes:
   `Impargs.implicits_of_global`.

    The easy thing to do first is to just omit the arguments declared
    as implicit. Then try inductive type parameters? Think about other
    possibilities.

3. Omit (some) type guards when the type may be inferred. For example,

   * forall x : nat, Even(x) -> phi

   probably may be translated to

   * forall x, Even(x) -> phi',

   because Even(x) implies nat(x).

   A non-trivial problem is to precisely formulate a general
   criterion, and prove it correct for a reasonable subset of CIC.

4. (partly done) For reconstruction: look at the inversion (also
   discrimination, injection -- less useful?) axioms used in the ATP
   proofs and add them to the context before invoking a reconstruction
   tactic. Or use the inversion axioms to specify the "inverting"
   option of the reconstruction tactics. Make some intelligent use of
   other information contained in the atp_info data structure
   (src/plugin/provers.mli). Also look at the axioms for matches,
   which may sometimes be used by the ATPs to do inversion (see point
   7).

   Try to use even more information from ATP runs. Dig deeper into ATP
   proofs.

5. Heuristic monomorphisation (instantiation of polymorphic
   definitions with types). It is important to do this on the
   translation level and not leave it to the ATPs, because then the
   translation output may be further optimised. For example,

   * forall (A : Type) (x : A), phi

   is translated to

   * forall A, T(A, Type) -> forall x, T(x, A) -> phi',

   but in an instantiated version the type guards may be optimised,
   e.g. for instantiation with nat to:

   * forall x, nat(x) -> phi'.

   The monomorphisation is especially important for higher-order
   statements, whose translations are now not very usable by the
   ATPs. See e.g. the inversion axiom for List.Forall (Hammer_transl
   "List.Forall").

6. Optimise type guards for parameterised types. For instance,
   forall x : list nat, phi is translated to

   * forall x, T(x, list nat) -> phi',

   but should be to

   * forall x, list_nat(x) -> phi'.

   This will work well in combination with heuristic monomorphisation.

   The above example of list with nat parameter is simple, but types
   in Coq can be complicated. Can we do something when some of the
   type parameters contain occurrences of variables bound externally?
   For example:

   * forall x y, T(x, A) -> T(y, list (Q x)) -> phi.

   We can, e.g., have an optimised type guard list(Q x, y) or
   list\_Q(x,y). What are other possibilities? What if T(y, list (Q
   nat)), maybe then list\_Q\_nat(y)? This problem probably involves
   much experimentation trying to figure out the right way of doing
   this.

7. Try breaking up the axiom for matches (on variables?) into one
   axiom for each constructor. E.g. instead of translating

   * match x with 0 => t1 | S y => t2 end

   to:

   * forall x, nat(x) -> (x = 0 /\ F x = t1') \\/
                         (exists y, nat(y) /\ x = S y /\ F x = t2')

   use two axioms:

   1. F 0 = t1'[0/x]
   2. forall y, nat(y) -> F (S(y)) = t2'[S(y)/x]

   Note that in point 2 the guard nat(y) should be omitted if
   `opt_closure_guards` is true (this is analogous to omitting type
   guards for free variables of lambda-lifted expressions).

   This is related to program extraction. See Pierre Letouzey’s
   Ph.D. thesis.

8. Try giving symbol ordering hints to ATPs. There is a natural order
   on constants: c1 > c2 if transitive-closure(c2 occurs in the
   definition of c1). This ordering, lifted to lexicographic path
   order, seems to work well in the reconstruction tactics. See
   src/lib/lpo.ml and the implementation of rewriting actions in
   src/tactics/sauto.ml. Extend this idea, try to make the ordering
   total, try different orderings.

9. Properly handle functions which use dependent types in a
   non-trivial way. Properly handle case analysis for small
   propositional inductive types. Properly handle sig, sigT, etc., and
   prod, sum, etc. with propositional arguments. For example, given

   ```coq
   Definition h (x y z : nat) (p : x = y /\ y = z) : {u : nat | x = u} :=
     match p with
     | conj p1 p2 =>
       exist (fun u => x = u) z (eq_trans p1 p2)
     end.
   ```

   the function `h` has type

   ```coq
   forall x y z : nat, x = y /\ y = z -> {u : nat | x = u}
   ```

   It should be translated to a definition of a function `h`

   * forall x y z, h(x, y, z) = z

   and a specification axiom derived from the type

   * forall x y z, x = y /\ y = z -> x = h(x, y, z)

   Currently, no function definition for h is generated. Neither is
   the specification axiom. Only an unusable typing axiom for h is
   generated.

   A similar problem is considered in Pierre Letouzey’s Ph.D. thesis,
   but there the goal is only code extraction, so there is no need to
   generate the specification axioms derived from types. In addition
   to program extraction, we need to do *specification extraction*.

10. Explicitly state the types of non-trivial terms. E.g. if
    f:nat->nat and 0:nat and (f 0) occurs (in the goal or hypothesis?)
    then state (f 0):nat as an axiom. More general: consider
    non-trivial terms as possible premises. This ties in with
    monomorphisation. What types to choose for instantiating
    e.g. list? Do machine-learning premise selection with (list nat),
    (list Z), etc. among premises.

11. Improvements in premise selection: better features, other
    algorithms? Special status for head constants?

12. Translation to HOL. Factor the translation, including a HOL
    intermediate stage: Coq -> CIC_0 -> HOL -> applicative FOL ->
    FOL. Try using higher-order ATPs.

13. Write a custom version of the `eapply` tactic which does
    unification modulo "simple" (equational?) reasoning. See the smart
    matching of Matita.

14. Optional use of classical logic.

Technical improvements
----------------------

1. Remove dependence on "grep".
2. Properly handle argument parsing in the tactics.
3. Make the plugin work on Windows.
