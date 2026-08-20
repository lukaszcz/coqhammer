(* Focused translation regression for lift sharing across instantiation.

   Lifting mints one symbol per occurrence shape, so one Coq type reached at
   two shapes -- a schema occurrence under quantifiers and an instance
   occurrence over constants -- gets two unrelated [$_type_N] names.  Nothing
   related them: the unfolding axiom is only an implication (commit 951862d),
   and the [$_arrow] former covers non-dependent non-Prop-domain products
   only.  A lifted symbol names a Coq term, so when one lift's term is a
   syntactic instance of another's the translator emits the equation

     $_type_instance(vars) = $_type_schema(sigma)

   under the name [$_link_N].  It is true by construction -- both sides are
   images of one Coq term -- and being an equality it bridges both ways.

   The same holds for lifted lambdas.  Their definition equations relate the
   lifted symbol to the body only when both are applied to the lambda-bound
   arguments, so the unapplied symbols stay unrelated, and identifying two
   pointwise equal functions in general needs functional extensionality.  A
   link equation is not that: it says the two lifts' canonical terms are
   related by syntactic instantiation, so the two symbols name one and the same
   Coq lambda term.

   Being images of one Coq term is not on its own enough, though.  Matching is
   syntactic on the unerased term while a lift's arity is settled after
   erasure, so a schema whose binder type is a canonical variable can match an
   instance whose binder is a proof; the two symbols are then applied at
   different arities and the equation relates a value to a function.  What
   keeps such a pair apart is the binder-erasure check in [add_link_axiom], and
   [link_erasure_transl.v] is what pins it.

   Pinned here: the shapes lifting still splits, namely dependent products,
   Prop-domain products and lambdas, are linked; a dependent-product link and
   a lambda link are minted inside a dumped ATP problem, from a schema and an
   instance the dumped goal carries itself; and no unfolding axiom became an
   equivalence in the process.  That last check is about the axiom's own
   connective and nothing else: a guard may legitimately contain a translated
   Coq [iff] -- a subset payload or a Prop-domain antecedent is an ordinary
   proposition -- so the first connective is what is compared, not the
   presence of [<=>] anywhere in the axiom. *)

From Hammer Require Import Hammer.

Parameter A : Type.
Parameter X : Type.
Parameter Pi : X -> Type.
Parameter Fam : forall W : Type, W -> Type.

(* Dependent product, schema occurrence: the lifted type [forall z : Z, Q z]
   has both its domain and its codomain family as canonical variables. *)
Parameter dep_schema : forall (Z : Type) (Q : Z -> Type), (forall z : Z, Q z) -> nat.

(* The same product, ground instance occurrence: [Z := X], [Q := Pi]. *)
Parameter dep_inst : forall x : X, Pi x.

(* An instance which is still open, so both sides of the link are applied
   lifted constants: [Z := W], [Q := Fam W]. *)
Parameter dep_inst_open : forall W : Type, (forall w : W, Fam W w) -> nat.

Parameter R : Prop.

(* Prop-domain product, schema and ground instance.  [type_to_guard] prunes
   proof binders from the term spine, so [R -> W] is not an [$_arrow]. *)
Parameter prop_schema : forall W : Type, (R -> W) -> nat.
Parameter prop_inst : R -> A.

Parameter idp : forall Z : Type, Z -> Z.
Parameter apply2 : forall Z : Type, (Z -> Z) -> Z -> Z.
Parameter gg : X -> X.

(* Lambda, schema occurrence: the lifted [fun z : Z => f (idp Z z)] has its
   domain and the applied function as canonical variables.  The constant [idp]
   keeps the schema out of the registry's capped constant-free bucket. *)
Definition lam_schema (Z : Type) (f : Z -> Z) (u : Z) : Z :=
  apply2 Z (fun z : Z => f (idp Z z)) u.

(* The same lambda over constants: [Z := X], [f := gg]. *)
Definition lam_inst (u : X) : X := apply2 X (fun x : X => gg (idp X x)) u.

(* Each schema is translated before its instances, so the link equation is
   emitted in the instance's own axiom set. *)
Hammer_transl "dep_schema".
Hammer_transl "dep_inst".
Hammer_transl "dep_inst_open".

Hammer_transl "prop_schema".
Hammer_transl "prop_inst".

Hammer_transl "lam_schema".
Hammer_transl "lam_inst".

Section DumpGoal.

(* The dumped problem has to exercise linking on its own.  Problem generation
   resets translation state, so no lift the [Hammer_transl] queries above
   minted survives into it and no link of theirs can be reused; and premise
   selection decides on its own what a problem gets, so the schemata are not
   left to it either.  Instead both halves of each pair sit in the goal's own
   local context, which [Hammer_dump] always translates along with the
   conclusion: [ks] is a dependent-product instance of the schema in
   [dep_schema_h], and the lambda in [lam_inst_h] is an instance of the one in
   [lam_schema_h].

   Hypotheses are translated in reverse declaration order, so the schemata are
   declared last, after the instances which must find them.  That order is
   what the registry needs for the dependent-product schema [forall z : Z, Q z]:
   it mentions no constant, an instance is indexed under the constants it does
   mention, and a constant-free lookup probes the constant-free bucket only --
   so a schema registered after its instance would not find it.  The lambda
   schema mentions [idp] and is found either way. *)

Variable Qs : X -> Type.
Variable ks : forall x : X, Qs x.

Variable gs : X -> X.
Variable lam_inst_h : forall u : X, apply2 X (fun x : X => gs (idp X x)) u = u.

Variable dep_schema_h :
  forall (Z : Type) (Q : Z -> Type), (forall z : Z, Q z) -> nat.
Variable lam_schema_h :
  forall (Z : Type) (f : Z -> Z) (u : Z),
    apply2 Z (fun z : Z => f (idp Z z)) u = u.

Goal ks = ks.
  Hammer_dump "type_sharing_transl.p".
Abort.

End DumpGoal.
