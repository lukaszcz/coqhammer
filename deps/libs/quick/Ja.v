Require Import Omega.
Require Import String.
Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.

From Hammer Require Import Hammer Reconstr.

Module JaSyntax.

(** Syntactical category of reference annotations. It contains
    _rwr_, _rd_ and _atm_ annotations.

    Defined in Figure {fig:syntax} as the set \mmod. *)
Inductive JFAMod : Set :=
| JFrwr
| JFrd
| JFatm.

(** Partial order on annotations.

    Defined in Section {sec:syntax-semantics}. *)
Inductive leqAnn : JFAMod -> JFAMod -> Prop  :=
| refl:  forall x, leqAnn x x
| rwrrd: leqAnn JFrwr JFrd
| rdatm: leqAnn JFrd JFatm
| rwratm: leqAnn JFrwr JFatm.

Hint Constructors leqAnn : myhints.

(** Upper bound for annotations.

    Defined in Section {sec:syntax-semantics}. *)
Definition supAnn (an1 an2:JFAMod) : JFAMod :=
  match an1 with
  | JFrwr => an2
  | JFrd => match an2 with
            | JFrwr => JFrd
            | JFrd => JFrd
            | JFatm => JFatm
            end
  | JFatm => JFatm
  end.

(** Lower bound for annotations.

    Defined in Section {sec:syntax-semantics}. *)
Definition infAnn (an1 an2:JFAMod) : JFAMod :=
  match an1 with
  | JFrwr => JFrwr
  | JFrd => match an2 with
            | JFrwr => JFrwr
            | JFrd => JFrd
            | JFatm => JFrd
            end
  | JFatm => an2
  end.


Lemma rwr_bottom:
  forall x, leqAnn JFrwr x.
Proof.
  scrush.
Qed.

Lemma rwr_eq:
  forall x, leqAnn x JFrwr -> x = JFrwr.
Proof.
  scrush.
Qed.


Lemma atm_top:
  forall x, leqAnn x JFatm.
Proof.
  scrush.
Qed.


Lemma atm_eq:
  forall x, leqAnn JFatm x -> x = JFatm.
Proof.
  scrush.
Qed.


Lemma leqAnn_trans:
  forall (mu1 mu2 mu3:JFAMod),
    leqAnn mu1 mu2 -> leqAnn mu2 mu3 -> leqAnn mu1 mu3.
Proof.
  scrush.
Qed.

Hint Resolve atm_top rwr_bottom leqAnn_trans : myhints.

(**
   Effective version of the partial order on annotations that
   returns booleans instead predicting the property.
*)
Fixpoint leqAnn_bool (m1 m2:JFAMod) : bool  :=
  match m1 with
    | JFrwr => true
    | JFrd => match m2 with
                | JFrwr => false
                | _ => true
              end
    | JFatm => match m2 with
                 | JFatm => true
                 | _ => false
               end
  end.

(**
   The reverse of the effective version of the partial order on
   annotations. It returns booleans instead predicting the property.
*)
Definition geqAnn_bool m1 m2 := leqAnn_bool m2 m1.


(** Alias name for class names. We represet them as
    Coq strings. *)
Definition JFClassName := string.

Hint Resolve string_dec : dec.

(** Decidable equality on [JFClassName]. *)
Definition JFClassName_dec : forall v v' : JFClassName, {v=v'}+{~v=v'}.
  exact string_dec.
Defined.
Hint Resolve JFClassName_dec : dec.

Lemma jfclassname_commutative:
  forall x y,
    (if JFClassName_dec x y then true else false) =
    if JFClassName_dec y x then true else false.
Proof.
  scrush.
Qed.

(** Syntactical category of class identifiers. The
  identifier JFBotClass does not occur in the source
  code.

  Defined in Figure {fig:syntax} as the set \Cname. *)
Inductive JFCId : Set :=
| JFClass (name:JFClassName)
| JFBotClass.

(** Decidable equality on [JFCId]. *)
Definition JFCId_dec : forall v v' : JFCId, {v=v'}+{~v=v'}.
  decide equality.
  auto with dec.
Defined.
Hint Resolve JFCId_dec : dec.

(** The class name of the _Object_ class.

    Defined in Figure {fig:auxiliary-notation} in
    the second row as \objecttype. *)
Definition JFObjectName := "Object"%string.

(** The class name of the _NullPointerException_ class.

    Defined in Figure {fig:auxiliary-notation} in
    the second row as \npetype. *)
Definition JFNPEName := "NullPointerException"%string.

(** The class identifier of _Object_. *)
Definition JFObject := JFClass (JFObjectName).

(** The class identifier of _NullPointerException_. *)
Definition JFNPE := JFClass (JFNPEName).

(** Syntactical category of method identifiers.

  Defined in Figure {fig:syntax} as the set _m_. *)
Definition JFMId := string.

(** Decidable equality on [JFMId]. *)
Definition JFMId_dec : forall v v' : JFMId, {v=v'}+{~v=v'}.
  exact string_dec.
Defined.
Hint Resolve JFMId_dec : dec.

(** Syntactical category of variable identifiers.

  Defined in Figure {fig:syntax} as the set _x_. *)
Definition JFXId := string.

(** Decidable equality on [JFCId]. *)
Definition JFXId_dec : forall v v' : JFXId, {v=v'}+{~v=v'}.
  exact string_dec.
Defined.
Hint Resolve JFXId_dec : dec.

(** Semantical category of locations. It is defined in the
    syntax part since the small step reduction of Jafun
    semantics uses locations in expressions being reduced.
    Locations are either the _null_ location or an address.

    Defined in Section {sec:syntax-semantics} as the set \Loc. *)
Inductive Loc : Set :=
| null
| JFLoc (n:nat).

Hint Resolve Nat.eq_dec : dec.

(** Decidable equality on locations [Loc]. *)
Definition Loc_dec : forall l l' : Loc, {l=l'}+{~l=l'}.
  decide equality.
  auto with dec.
Defined.
Hint Resolve Loc_dec : dec.

(** Syntactic reference: variable or _this_. *)
Inductive JFRef :=
| JFVar (x:JFXId)
| JFThis.

(** Decidable equality on references [JFRef]. *)
Definition JFRef_dec : forall v v' : JFRef, {v=v'}+{~v=v'}.
  decide equality.
  auto with dec.
Defined.
Hint Resolve JFRef_dec : dec.

(** Values: locations or syntactic references *)
Inductive JFVal :=
| JFVLoc (l:Loc)
| JFSyn (x:JFRef).

(* now substitutions substitute locations for syntactic references *)

(** "Syntactic" _null_ is directly represented by the "semantic" one. *)
Notation JFnull := (JFVLoc null).


(** Decidable equality on primitive values [JFVal]. *)
Definition JFVal_dec : forall v v' : JFVal, {v=v'}+{~v=v'}.
  decide equality; auto with dec.
Defined.
Hint Resolve JFVal_dec : dec.


(**
   The representation of subexpression in which an object refers to
   its field. This is a type of subexpressions that helps to define
   the main syntactic category.
 *)
Definition JFFieldref :Set :=  (JFVal * JFXId)%type.

(** The representation of Jafun expressions.

    Defined in Figure {fig:syntax} as the syntactic
    category _E_. *)
Inductive JFExpr : Set :=
| JFNew (mu:JFAMod) (C:JFClassName) (vs : list JFVal)
| JFLet (C:JFClassName) (x:JFXId) (E1:JFExpr) (E2:JFExpr)
| JFIf (v1 v2:JFVal) (E1:JFExpr) (E2:JFExpr)
| JFInvoke (v:JFVal) (m:JFMId) (vs:list JFVal)
| JFAssign (vx:JFFieldref) (v:JFVal)
| JFVal1 (v:JFVal)
| JFVal2 (vx:JFFieldref)
| JFThrow (v:JFVal)
| JFTry (E1:JFExpr) (mu:JFAMod) (C:JFClassName) (x:JFXId) (E2:JFExpr).

(* make an alpha equivalent of [x.E] not using [vv]; TODO: maybe this should return a pair *)
Parameter alphaExpr : forall (x:JFXId) (vv:list JFXId) (E:JFExpr), JFExpr.
Parameter alphaVal : forall (x:JFXId) (vv:list JFXId) (E:JFVal), JFVal.

(** Substitute the value [l] for [v] in [x] (i.e. _"x{l/v}"_). *)
Definition substVal (v : JFRef) (l:Loc) (x : JFVal) :=
  match x with
  | JFVLoc _ => x
  | JFSyn y => if JFRef_dec v y then JFVLoc l else x
  end.



(** Substitute the location [l] for the occurrences of the reference [v]
    in the expression [E] (i.e. _"E{l/v}"_).
 *)
Fixpoint substExpr (v:JFRef) (l:Loc) (E:JFExpr) {struct E} : JFExpr :=
  match E with
  | JFNew mu C vs => JFNew mu C (List.map (substVal v l) vs)
  | JFLet C x E1 E2 =>
    if JFRef_dec (JFVar x) v then
      JFLet C x (substExpr v l E1) E2
    else
      JFLet C x (substExpr v l E1) (substExpr v l E2)
  | JFIf v1 v2 E1 E2 =>
    JFIf (substVal v l v1) (substVal v l v2)
         (substExpr v l E1) (substExpr v l E2)
  | JFInvoke v1 m vs =>
    JFInvoke (substVal v l v1) m (List.map (substVal v l) vs)
  | JFAssign (v1,fld) v2 =>
    JFAssign (substVal v l v1, fld) (substVal v l v2)
  | JFVal1 v1 =>
    JFVal1 (substVal v l v1)
  | JFVal2 (v1, fld) =>
    JFVal2 (substVal v l v1, fld)
  | JFThrow v1 =>
    JFThrow  (substVal v l v1)
  | JFTry E1 mu C x E2 =>
    if JFRef_dec (JFVar x) v then
      JFTry (substExpr v l E1) mu C x E2
    else
      JFTry (substExpr v l E1) mu C x (substExpr v l E2)
  end.

(** Substitute the variables from the list [vs] by respective values
    in the list [fs] in [E] (i.e. _"E{fs/vs}"_).
 *)
Fixpoint substList fs vs E {struct fs} :=
  match fs with
    | [] => Some E
    | v1 :: tl =>
      match vs with
        | [] => None
        | v2 :: tl' =>
          match v2 with
            | JFVLoc l => substList tl tl' (substExpr v1 l E)
            | _ => None
          end
      end
  end.

(** A class type combinded with an annotation.

    The type system uses the pairs in the
    sequence: class first, annotation second. *)
Definition JFACId : Set := (JFCId * JFAMod)%type.

(** The representation of method declarations. There are two kinds
    of declarations: with access mode annotations (local state ones)
    [JFMDecl] and without [JFMDecl0].

    Defined in Figure {fig:syntax} as the syntactic
    category \mathbf{M}.
 *)
Inductive JFMethodDeclaration : Set :=
| JFMDecl (C:JFACId) (mu:JFAMod) (m:JFMId) (vs:list (JFXId * JFACId)) (thrws:list JFACId) (E:JFExpr)
| JFMDecl0 (C:JFCId) (m:JFMId) (vs:list (JFXId * JFCId)) (thrws:list JFCId) (E:JFExpr).

(** Decidable equality on method declarations [JFMethodDeclaration]. *)
Definition JFMethodDeclaration_dec : forall v v' : JFMethodDeclaration, {v=v'}+{~v=v'}.
  repeat (decide equality; auto with dec).
Defined.
Hint Resolve JFMethodDeclaration_dec : dec.

Section methodProjections.

(** Retrives the type of the value returned from the given
    method declared as [md]. *)
Definition rettyp_of_md (md: JFMethodDeclaration) : JFACId :=
  match md with
  | JFMDecl D mu mn vs excs E => D
  | JFMDecl0 D mn vs excs E => (D, JFrwr)
  end.

(** Retrives the annotation of _this_ for the given
    method declared as [md]. It returns [Some] value in case
    the method is local-sensitive and [None] otherwise. *)
Definition mode_of_md (md: JFMethodDeclaration) : option JFAMod :=
  match md with
  | JFMDecl D mu mn vs excs E => Some mu
  | JFMDecl0 D mn vs excs E => None
  end.

(** Retrives the name of the method from the given
    method declaration [md]. *)
Definition name_of_md (md: JFMethodDeclaration) : JFMId :=
  match md with
  | JFMDecl _ _ mn _ _ _ => mn
  | JFMDecl0 _ mn _ _ _ => mn
  end.

(** Retrives the formal parameters of the method from the given
    method declaration [md]. *)
Definition params_of_md md :=
  match md with
    | JFMDecl _ _ _ vs _ _ => map fst vs
    | JFMDecl0 _ _ vs _ _ => map fst vs
  end.

(** Retrives the list of types of exceptions being thrown by
    the method [md]. The function returns an annotated type, i.e.
    [JFACid]. In case of non-local sensitive methods it returns
    _rwr_ annotations. *)
Definition thrs_of_md (md: JFMethodDeclaration) : list JFACId :=
  match md with
  | JFMDecl D mu mn vs excs E => excs
  | JFMDecl0 D mn vs excs E => map (fun D => (D, JFrwr)) excs
  end.

(** Retrives the expression which is the body of the given
    method declaration [md]. *)
Definition body_of_md (md:JFMethodDeclaration) : JFExpr :=
  match md with
    | JFMDecl _ _ _ _ _ E => E
    | JFMDecl0 _ _ _ _ E => E
  end.

(** Checks if the given method [md] is a declaration of a local-sensitive
    method. The method checks the way the declaration [md] is constructed. *)
Definition isLS (md:JFMethodDeclaration) : Prop :=
  match md with
  | JFMDecl _ _ _ _ _ _ => True
  | JFMDecl0 _ _ _ _ _ => False
  end.

End methodProjections.

(** Finds a declaration of a method with the given name [m] in
    the list of method declarations [mthds]. It returns [None] in
    case there is no method declaration of the given name and
    [Some] value in case the method declaration is found. *)
Fixpoint find_method mthds m {struct mthds} :=
  match mthds with
    | [] => None
    | (JFMDecl D mu mn vs excs E) :: tl =>
      if JFMId_dec m mn
      then Some (JFMDecl D mu mn vs excs E)
      else find_method tl m
    | (JFMDecl0 D mn vs excs E) :: tl =>
      if JFMId_dec m mn
      then Some (JFMDecl0 D mn vs excs E)
      else find_method tl m
  end.

(** Syntactical category of field declarations.
    The _phi_ argument is [true] when there is a _rep_
    modifier attached to the field. It is [false] otherwise.

  Defined in Figure {fig:syntax} as the set \mathbf{F}.
 *)
Inductive JFFieldDeclaration : Set :=
| JFFDecl (phi:bool) (C:JFCId) (x:JFXId).

(** Decidable equality on field declarations [JFFieldDeclaration]. *)
Definition JFFieldDeclaration_dec : forall v v' : JFFieldDeclaration, {v=v'}+{~v=v'}.
  repeat decide equality.
Defined.

Section fieldProjections.

(** Retrives the name of the given field [fd]. *)
Definition name_of_fd (fd: bool * JFCId * JFXId) :=
  match fd with
    | (x, y, z ) => z
  end.

(** Retrives the class of the given field [fd]. *)
Definition class_of_fd (fd: bool * JFCId * JFXId) :=
  match fd with
    | (x, y, z ) => y
  end.

(** Retrives the annotation of the given field [fd]. *)
Definition ann_of_fd (fd: bool * JFCId * JFXId) :=
  match fd with
    | (x, y, z ) => x
  end.

End fieldProjections.


(** Finds a declaration of a field with the given name [x] in
    the list of field declarations [flds]. It returns [None] in
    case there is no field declaration of the given name and
    [Some] value in case the field declaration is found. *)
Fixpoint find_field flds x {struct flds} :=
  match flds with
    | [] => None
    | (phi, C, xn) :: tl =>
      if JFXId_dec x xn
      then Some (JFFDecl phi C xn)
      else find_field tl x
  end.

Lemma in_find_field:
  forall x fs,
    In x (map name_of_fd fs) -> exists fd, find_field fs x = Some fd.
Proof.
  induction fs; sauto.
Qed.

(** Syntactical category of class declarations.

    Defined in Figure {fig:syntax} as the set \mathbf{C}.

    As written in Java Language Specification Section 8.1.4,
    the extends clause is optional. This is modelled by the
    *option* type in the argument [ex].
 *)
Inductive JFClassDeclaration : Set :=
| JFCDecl (D:JFClassName) (ex:option JFClassName)
          (fields:list JFFieldDeclaration) (methods:list JFMethodDeclaration).

(** Decidable equality on class declarations [JFClassDeclaration]. *)
Definition JFClassDeclaration_dec : forall v v' : JFClassDeclaration, {v=v'}+{~v=v'}.
  repeat decide equality.
Defined.


Section classProjections.

(** Retrives the name of the given class [cd]. *)
Definition name_of_cd (cd: JFClassDeclaration) :=
  match cd with
  | JFCDecl D _ _ _ => D
  end.

(** Retrives the field declarations in the given class [cd].
    This method does not traverse the inheritance hierarchy. *)
Definition flds_of_cd (cd: JFClassDeclaration) :=
  match cd with
  | JFCDecl D _ _ _ => D
  end.

(** Retrieves the list of triples that represent data in field
    declarations of the class declaration [cd].
 *)
Definition get_fields_raw (cd:JFClassDeclaration) :=
  let gfxid := fun field =>
                 match field with
                 | JFFDecl phi C x => (phi, C, x)
                 end
  in match cd with
     | JFCDecl _ _ fields _ => List.map gfxid fields
     end.

(** Retrives the method declarations in the given class [cd].
    This method does not traverse the inheritance hierarchy. *)
Definition mthds_of_cd (cd: JFClassDeclaration) :=
  match cd with
  | JFCDecl _ _ _ mthds => mthds
  end.

(** Retrives the extends clause in the given class [cd].
    It returns [None] in case the current class is not extended.
    This should happen only in the case of the [Object] class. *)
Definition extds_of_cd (cd:JFClassDeclaration) :=
  match cd with
  | JFCDecl _ extds _ _ => extds
  end.


End classProjections.

(** The general structure of Jafun programs. It is a list of classes. *)
(* TODO: dlaczego to jest lista, Featherweight definiuje to jako
   funkcja częściowa. *)
Definition JFProgram : Set := list JFClassDeclaration.

(** Finds a declaration of a class with the given name [cname] in
    the program [CC]. It returns [None] in case there is no class
    declaration of the given name and [Some] value in case the class
    declaration is found. *)
Fixpoint find_class (CC:JFProgram) (cname:JFClassName) :=
  match CC with
  | [] => None
  | (JFCDecl D ex fields methods) :: tl =>
    if (JFClassName_dec D cname)
    then Some (JFCDecl D ex fields methods)
    else find_class tl cname
  end.

Lemma find_class_eq:
  forall P C ex fields methods,
    find_class (JFCDecl C ex fields methods :: P) C =
    Some (JFCDecl C ex fields methods).
Proof.
  sauto.
Qed.

Lemma find_class_further_neq:
  forall P D C ex fields methods CC,
  C<>D ->
  find_class (JFCDecl C ex fields methods :: P) D = Some CC ->
  find_class P D = Some CC.
Proof.
  sauto.
Qed.


Lemma find_class_in:
  forall CC cname ex fields methods,
    find_class CC cname = Some (JFCDecl cname ex fields methods) ->
    In (JFCDecl cname ex fields methods) CC.
Proof.
  induction CC; sauto.
Qed.


Lemma find_class_same:
  forall P D C ex fields methods CC,
  C<>D ->
  find_class P D = Some CC ->
  find_class (JFCDecl C ex fields methods :: P) D = Some CC.
Proof.
  sauto.
Qed.

Lemma find_class_eq_name:
  forall P C D ex fields methods,
  find_class P C = Some (JFCDecl D ex fields methods) ->
  C = D.
Proof.
  induction P; sauto.
Qed.

Lemma find_class_decompose_program:
  forall P C D,
    find_class P C = Some D ->
    exists P0 P1,
      P = P0 ++ (D :: P1).
Proof.
  induction P; sauto.
  +  hammer_hook "JaSyntax" "JaSyntax.find_class_decompose_program.subgoal_1".
     exists [], P; auto.
  +  hammer_hook  "JaSyntax" "JaSyntax.find_class_decompose_program.subgoal_2".
     Reconstr.hobvious (@IHP, @H)
                       (@Coq.Lists.List.app_comm_cons)
                       Reconstr.Empty.
Qed.

Lemma find_class_lift_cons:
  forall P cname C D,
    find_class P cname = Some C ->
    exists C',
      find_class (D :: P) cname = Some C'.
Proof.
  sauto.
Qed.

Lemma find_class_lift:
  forall P1 P2 cname C,
    find_class P2 cname = Some C ->
    exists C',
      find_class (P1 ++ P2) cname = Some C'.
Proof.
  induction P1; sauto.
Qed.

(** Checks if the given program [P] contains a class declaration of the
    given name [cname].
*)
Fixpoint program_contains (P:JFProgram) (cname:JFClassName) : bool :=
  match P with
    | [] => false
    | JFCDecl dname _ _ _ :: P' => if JFClassName_dec cname dname then true else program_contains P' cname
  end.

Lemma program_contains_further_neq:
  forall P C D ex fields methods,
    C <> D ->
    program_contains (JFCDecl C ex fields methods :: P) D = true ->
    program_contains P D = true.
Proof.
  sauto.
Qed.

Lemma program_contains_further:
  forall P C D ex fields methods,
    program_contains P D = true ->
    program_contains (JFCDecl C ex fields methods :: P) D = true.
Proof.
  sauto.
Qed.

Lemma program_contains_find_class:
  forall P D,
    program_contains P D = true ->
    exists cd, find_class P D = Some cd.
Proof.
  induction P; sauto.
Qed.

Lemma find_class_program_contains:
  forall P D cd,
    find_class P D = Some cd ->
    program_contains P D = true.
Proof.
  induction P; sauto.
Qed.


(** Finds the method [m] in the class of the name [C] in the program [P],
    traversing the inheritance hierarchy of [C] in the program [P].
    In case the program [P] does not contain a class with name [C]
    the function returns [None]. In case the class does not contain
    the method [m], it returns [None] too. Otherwise, [Some] method
    declaration is returned.
*)
Fixpoint methodLookup (P:JFProgram) (C:JFClassName)
           (m:JFMId)  : option JFMethodDeclaration :=
  match P with
  | [] => None
  | (JFCDecl D ex _ mthds) :: P1 =>
    if JFClassName_dec C D
    then match find_method mthds m with
         | None => match ex with
                   | None => None
                   | Some DD => methodLookup P1 DD m
                   (* Correction: semantically P in place of P1
                      changes the meaning in case C=D=DD and there
                              is no m in mthds, which occurs only in
                              non-wellformeed programs. So we can
                              redefine it. *)
                   end
         | Some md => Some md
         end
    else
      methodLookup P1 C m
  end.

Lemma methodLookup_raw_empty:
  forall j m,
    methodLookup [] j m = None.
Proof.
  intros. simpl; auto.
Qed.

Lemma methodLookup_prog_monotone_eq:
  forall P Dd C D m md,
    C = (name_of_cd Dd) ->
    find_method (mthds_of_cd Dd) m = None ->
    extds_of_cd Dd = Some D ->
    methodLookup P D m = Some md ->
    methodLookup (Dd :: P) C m = Some md.
Proof.
  sauto.
Qed.

Lemma methodLookup_raw_neq:
  forall C D tl m md fields methods,
    C <> D ->
    methodLookup tl D m = Some md ->
    methodLookup (JFCDecl C (Some D) fields methods :: tl) D m = Some md.
Proof.
  sauto.
Qed.


Lemma methodLookup_find_class:
  forall P C m dcl,
    methodLookup P C m = Some dcl ->
    exists cdcl, find_class P C = Some cdcl.
Proof.
  induction P; sauto.
Qed.

(** Predicate that checks if the given method in the class declaration
    is local sensitive. *)
Inductive isLSForId : JFProgram -> JFClassName -> JFMId -> Prop  :=
| isLStrue : forall P C m md,
    methodLookup P C m = Some md  ->
    isLS md ->
    isLSForId P C m.

Lemma isLSForId_dec:
  forall P C m, isLSForId P C m \/ ~ isLSForId P C m.
Proof.
  intros.
  destruct (methodLookup P C m) eqn:?.
  + destruct j.
    ++ pose isLStrue; scrush.
    ++ right; intro H; inversion H; scrush.
  + scrush.
Qed.

Hint Resolve in_find_field find_class_in isLSForId_dec find_class_lift_cons find_class_lift : myhints.

End JaSyntax.

Module JaTactics.
(** * Collection of genaral tactics **)

(**
   In case one has a hypothesis
   [H : match e with ... => None end  =  Some ...]
   one wants to do [destruct e; discriminate H]

   [destr_discr H] does exactly this.

   However, doing this (esp. in a loop) can lead to loss of information
   in case [e] is not a variable.
   Therefore [auto_destr_discr H] does destruct and loop only if [e] is
   a variable.

   In case [e] is not a variable but one wants do do destruct anyway,
   one can use [destr_discr H] which does not apply any check.

   [destr_discr_raw check H] is an workhorse tactic used by the two
   and [accept] is an accept-all one argument tactic.
**)

Ltac destr_discr_raw check H :=
  discriminate H
  ||
  ( match type of H with
      (match ?t with _ => _ end = _) => check t; destruct t
    end;
    try discriminate H ).

Ltac auto_destr_discr H :=
  repeat destr_discr_raw is_var H.

Ltac accept H := idtac.

Ltac destr_discr H :=
  destr_discr_raw accept H.


(**
    [substh id hyp] works similar to [subst id], but only in the hypothesis [hyp].
**)

(* TODO: zrobić tactic notation subst id in H *)

Ltac substh id hyp :=
  match goal with [ H : id = _ |- _ ] => rewrite H in hyp end.

(** Cool tactic taken from
    # <a href="https://stackoverflow.com/questions/22404394/how-to-automatically-generate-good-names-when-decomposing-existential-hypothes%2322543921">a stackoverflow question</a> #
   which destructs a given hypothesis [H : ∃ (x:A) (y:B) (z:C), P x y z] into
   - [x : A]
   - [y : B]
   - [z : C]
   - [H : P x y z]
*)

Ltac decompose_ex H :=
  repeat match type of H with
           | ex (fun x => _) =>
             let x := fresh x in
             destruct H as [x H]
         end.




(** [decompose_and H as (? & Y & H)].
   It destructs completely a conjunction [H] giving a name [Y]
   to the second conjunct and automatic names to the others.
   The initial conjunction is cleared.
   If [H] is not present at the end of the intropattern,
   the conjunction is not decomposed completely.
   *)
Tactic Notation "decompose_and" ident(H) :=
  decompose [and] H; clear H.

Tactic Notation "decompose_and" ident(H) "as" simple_intropattern(patt) :=
  destruct H as patt;
  try (progress decompose [and] H; clear H).





(** [ssplit] - safe split - splits _only_ conjunctions in the goal and
   only the main line. Normal [repeat split] may do some unwanted evar
   instantiations and apply constructors in other one-constructor
   inductive types *)
Ltac ssplit :=
  lazymatch goal with
  [ |- (_ /\ _) ] =>
    split; [ssplit | ssplit]
  | _ => idtac
  end.

(** [subtle] solve trivial goals _without_ instantiating evars;
   recommended for [repeat (ssplit; subtle)] *)
Ltac subtle := try match goal with [ |- ?G ] => has_evar G; fail 2 end || trivial.

Import JaSyntax.

Ltac destruct_eq := try match goal with
                          [ |- context [string_dec ?C ?C] ] => destruct (string_dec C C); try contradiction
                        | [ |- context [JFXId_dec ?C ?C] ] => destruct (JFXId_dec C C); try contradiction
                        | [ |- context [JFClassName_dec ?C ?C] ] => destruct (JFClassName_dec C C); try contradiction
                        | [ H : (?C <> ?D) |- context [string_dec ?C ?D] ] => destruct (string_dec C D); try contradiction
                        end.

End JaTactics.

Require Import String.
Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.
Require Import NPeano.
Require Import PeanoNat.
Require Export Arith.
Open Scope nat_scope.

Module JaProgram.

Import JaSyntax.

Definition is_class_name cname cdecl :=
  match cdecl with
    | JFCDecl ccname _ _ _ => if JFClassName_dec ccname cname then true else false
  end.

Lemma is_class_name_name:
  forall C ex fields methods,
    is_class_name C (JFCDecl C ex fields methods) = true.
Proof.
  scrush.
Qed.

Lemma is_class_name_name_cd:
  forall cd,
    is_class_name (name_of_cd cd) cd = true.
Proof.
  scrush.
Qed.

Lemma is_class_name_neq:
  forall C D ex fields methods,
    C<>D ->
    is_class_name C (JFCDecl D ex fields methods) = false.
Proof.
  scrush.
Qed.


Lemma is_class_name_equal:
  forall C D ex fields methods,
    is_class_name C (JFCDecl D ex fields methods) = true ->
    C = D.
Proof.
  scrush.
Qed.

Lemma is_class_name_nequal:
  forall C D ex fields methods,
    is_class_name C (JFCDecl D ex fields methods) = false ->
    C <> D.
Proof.
  scrush.
Qed.

Lemma program_contains_counts_occ:
  forall P D,
    program_contains P D = true ->
    (count_occ Bool.bool_dec (map (is_class_name D) P) true > 0)%nat.
Proof.
  induction P.
  * scrush.
  * try hammer_hook "JaProgram" "JaProgram.program_contains_counts_occ.subgoal_0".
    intros.
    destruct a.
    destruct (JFClassName_dec D D0).
    ** try hammer_hook "JaProgram" "JaProgram.program_contains_counts_occ.subgoal_1".
       subst.
       rewrite map_cons.
       unfold is_class_name.
       destruct (JFClassName_dec D0 D0); try contradiction.
       try hammer_hook "JaProgram" "JaProgram.program_contains_counts_occ.subgoal_1_1".
       rewrite count_occ_cons_eq; auto.
       try hammer_hook "JaProgram" "JaProgram.program_contains_counts_occ.subgoal_1_2".
       auto with zarith.
    ** try hammer_hook "JaProgram" "JaProgram.program_contains_counts_occ.subgoal_2".
       scrush.
Qed.

(** The property to check that class name [cname] occurs only once in the program [P]. *)
Definition name_once (P:JFProgram) (cname:JFClassName) :=
 count_occ Bool.bool_dec (map (is_class_name cname) P) true = 1%nat.

Lemma in_head_not_in_tail:
  forall (P:JFProgram) (cname:JFClassName) (cdecl:JFClassDeclaration),
    (is_class_name cname cdecl) = true ->
    name_once (cdecl :: P) cname -> ~ name_once P cname.
Proof.
  induction P; scrush.
Qed.

Lemma name_once_further:
  forall C D P ex fields methods,
  C<>D ->
  name_once (JFCDecl C ex fields methods :: P) D -> name_once P D.
Proof.
  scrush.
Qed.

Lemma name_once_further_neq:
  forall C D P ex ms fs,
    C <> D ->
    name_once P D ->
    name_once (JFCDecl C ex ms fs :: P) D.
Proof.
  try hammer_hook "JaProgram" "JaProgram.name_once_further_neq".
  unfold name_once; scrush.
Qed.

Lemma name_once_further_eq:
  forall C P ex fields methods,
    count_occ Bool.bool_dec (map (is_class_name C) P) true = 0%nat ->
    name_once (JFCDecl C ex fields methods :: P) C.
Proof.
  try hammer_hook "JaProgram" "JaProgram.name_once_further_eq".
  unfold name_once; scrush.
Qed.

Lemma count_occ_zero_is_class_name_false:
  forall P cname cdecl,
    count_occ Bool.bool_dec (map (is_class_name cname) P) true = 0%nat ->
    In cdecl P ->
    is_class_name cname cdecl = false.
Proof.
  induction P; scrush.
Qed.

(** The property to check that declaraion [cdecl] occurs only once in the program [P]. *)
Definition decl_once (P:JFProgram) (cdecl:JFClassDeclaration) :=
  match cdecl with
    | JFCDecl cname _ _ _ => name_once P cname
  end.

Lemma count_occ_zero_decl_once:
  forall P C ex ms fs ex1 ms1 fs1,
    count_occ Bool.bool_dec (map (is_class_name C) P) true = 0%nat ->
    decl_once (JFCDecl C ex ms fs :: P) (JFCDecl C ex1 ms1 fs1).
Proof.
  try hammer_hook "JaProgram" "JaProgram.count_occ_zero_decl_once".
  Reconstr.hobvious Reconstr.Empty
                    (@name_once_further_eq)
                    (@decl_once).
Qed.

Lemma decl_in_head_not_in_tail:
  forall (P:JFProgram) (cname:JFClassName) (cdecl:JFClassDeclaration),
    (is_class_name cname cdecl) = true ->
    (decl_once (cdecl :: P) cdecl) ->
    ~ (decl_once P cdecl).
Proof.
  scrush.
Qed.

Lemma decl_in_head_false_in_tail:
  forall (P:JFProgram) (cname:JFClassName) (cdecl:JFClassDeclaration),
    (is_class_name cname cdecl) = true ->
    (decl_once (cdecl :: P) cdecl) ->
    Forall (fun x0 => is_class_name cname x0 = false) P.
Proof.
  try hammer_hook "JaProgram" "JaProgram.decl_in_head_false_in_tail".
  intros.
  unfold decl_once in *.
  destruct cdecl.
  apply is_class_name_equal in H.
  subst.
  unfold name_once in H0.
  try hammer_hook "JaProgram" "JaProgram.decl_in_head_false_in_tail.subgoal_0_1".
  rewrite map_cons in H0.
  rewrite is_class_name_name in H0.
  rewrite count_occ_cons_eq in H0; auto.
  try hammer_hook "JaProgram" "JaProgram.decl_in_head_false_in_tail.subgoal_0_2".
  injection H0; intros.
  apply Forall_forall.
  try hammer_hook "JaProgram" "JaProgram.decl_in_head_false_in_tail.subgoal_0_3".
  Reconstr.hobvious (@H)
                    (@count_occ_zero_is_class_name_false)
                    Reconstr.Empty.
Qed.

Lemma decs_once_monotone:
  forall (P:JFProgram) (cdecl:JFClassDeclaration)
         (ddecl:JFClassDeclaration) (cname:JFClassName),
    decl_once (cdecl :: P) ddecl ->
    is_class_name cname cdecl = true ->
    is_class_name cname ddecl = false ->
    decl_once P ddecl.
Proof.
  intros.
  unfold decl_once.
  destruct ddecl.
  unfold decl_once in H.
  try hammer_hook "JaProgram" "JaProgram.decs_once_monotone.subgoal_0".
  destruct cdecl.
  scrush.
Qed.

(** The property that all class names occur in the program uniquely. *)
Definition names_unique (P:JFProgram) :=
  Forall (decl_once P) P.

Lemma names_unique_zero:
  forall P D ex fields methods,
    names_unique (JFCDecl D ex fields methods :: P) ->
    count_occ Bool.bool_dec (map (is_class_name D) P) true = 0%nat.
Proof.
  scrush.
Qed.

Lemma names_unique_compose:
  forall P C ex ms fs,
    count_occ Bool.bool_dec (map (is_class_name C) P) true = 0%nat ->
    names_unique P ->
    names_unique (JFCDecl C ex ms fs::P).
Proof.
  try hammer_hook "JaProgram" "JaProgram.names_unique_compose".
  intros.
  unfold names_unique.
  apply Forall_cons.
  + try hammer_hook "JaProgram" "JaProgram.names_unique_compose.subgoal_1".
    Reconstr.htrivial (@H)
                      (@count_occ_zero_decl_once)
                      Reconstr.Empty.
  + try hammer_hook "JaProgram" "JaProgram.names_unique_compose.subgoal_2".
    apply Forall_forall.
    intros.
    unfold names_unique in H0.
    try hammer_hook "JaProgram" "JaProgram.names_unique_compose.subgoal_2_1".
    assert (forall y, In y P -> (decl_once P) y).
    try hammer_hook "JaProgram" "JaProgram.names_unique_compose.assert_1".
    Reconstr.hobvious (@H0, @H)
                      (@Coq.Lists.List.Forall_forall)
                      Reconstr.Empty.
    destruct x.
    assert (is_class_name C (JFCDecl D ex0 fields methods) = false) by scrush.
    apply (is_class_name_nequal) in H3.
    unfold decl_once.
    try hammer_hook "JaProgram" "JaProgram.names_unique_compose.subgoal_2_2".
    apply name_once_further_neq; scrush.
Qed.

Lemma names_unique_further:
  forall (P:JFProgram) (cdecl:JFClassDeclaration),
    names_unique (cdecl::P) ->
    names_unique P.
Proof.
  try hammer_hook "JaProgram" "JaProgram.names_unique_further".
  intros.
  unfold names_unique in H.
  inversion H.
  unfold names_unique.
  assert (forall x, In x P -> (decl_once P) x).
  try hammer_hook "JaProgram" "JaProgram.names_unique_further.assert_1".
  intros.
  assert (forall x, In x P -> (decl_once (cdecl :: P)) x).
  try hammer_hook "JaProgram" "JaProgram.names_unique_further.assert_2".
  apply -> (Forall_forall (decl_once (cdecl :: P)) P).
  auto.
  assert (decl_once (cdecl :: P) x0) by scrush.
  destruct cdecl.
  apply (decs_once_monotone P (JFCDecl D ex fields methods) x0 D).
  auto.
  unfold is_class_name.
  destruct (JFClassName_dec D D).
  auto.
  tauto.
  assert (Forall (fun x0 => is_class_name D x0 = false) P).
  try hammer_hook "JaProgram" "JaProgram.names_unique_further.assert_3".
  apply (decl_in_head_false_in_tail P D (JFCDecl D ex fields methods)).
  unfold is_class_name.
  destruct (JFClassName_dec D D);auto.
  auto.
  assert (forall x, In x P -> (is_class_name D x = false)).
  try hammer_hook "JaProgram" "JaProgram.names_unique_further.assert_4".
  apply Forall_forall.
  auto.
  scrush.
  try hammer_hook "JaProgram" "JaProgram.names_unique_further.subgoal_0".
  apply Forall_forall.
  auto.
Qed.

Lemma names_unique_decompose_program:
  forall (P1 P2:JFProgram),
    names_unique (P1 ++ P2) ->
    names_unique P2.
Proof.
  induction P1.
  + scrush.
  + try hammer_hook "JaProgram" "JaProgram.names_unique_decompose_program.subgoal_2".
    Reconstr.hobvious (@IHP1)
                      (@names_unique_compose, @names_unique_further, @Coq.Lists.List.app_comm_cons)
                      (@names_unique).
Qed.

Lemma names_unique_further_further:
  forall (P:JFProgram) (cdecl ddecl:JFClassDeclaration),
    names_unique (cdecl::ddecl::P) ->
    names_unique (cdecl::P).
Proof.
  intros.
  destruct cdecl.
  try hammer_hook "JaProgram" "JaProgram.names_unique_further_further.subgoal_0".
  apply names_unique_compose.
  - scrush.
  - try hammer_hook "JaProgram" "JaProgram.names_unique_further_further.subgoal_2".
    eauto using names_unique_further.
Qed.

Lemma count_zero_count_nzero:
  forall CC cname ex fields methods,
         count_occ JFClassDeclaration_dec CC
         (JFCDecl cname ex fields methods) > 0 ->
         count_occ Bool.bool_dec (map (is_class_name cname) CC) true = 0 ->
         False.
Proof.
  induction CC; intros.
  - scrush.
  - try hammer_hook "JaProgram" "JaProgram.names_unique_further_further.subgoal_2".
    destruct a.
    destruct (JFClassName_dec D cname).
    + try hammer_hook "JaProgram" "JaProgram.names_unique_further_further.subgoal_2_1".
      rewrite e in *.
      rewrite map_cons in H0.
      rewrite is_class_name_name in H0.
      rewrite count_occ_cons_eq in H0.
      discriminate H0.
      auto.
    + try hammer_hook "JaProgram" "JaProgram.names_unique_further_further.subgoal_2_2".
      rewrite map_cons in H0.
      rewrite is_class_name_neq in H0.
      rewrite count_occ_cons_neq in H0.
      rewrite count_occ_cons_neq in H.
      eauto using IHCC.
      congruence.
      congruence.
      auto.
Qed.

Lemma names_unique_find_class_unique:
  forall P cname C C',
         names_unique P ->
         find_class P cname = Some C ->
         find_class P cname = Some C' ->
         C = C'.
Proof.
  induction P; scrush.
Qed.

Hint Resolve names_unique_zero names_unique_compose names_unique_further names_unique_further_further names_unique_decompose_program count_zero_count_nzero is_class_name_name is_class_name_name_cd names_unique_find_class_unique : myhints.

Lemma in_names_unique_eq:
  forall CC cname ex fields methods ex0 fields0 methods0,
    In (JFCDecl cname ex fields methods)
       (JFCDecl cname ex0 fields0 methods0 :: CC) ->
    names_unique  (JFCDecl cname ex0 fields0 methods0 :: CC) ->
    (ex = ex0 /\ fields = fields0 /\ methods = methods0).
Proof.
  try hammer_hook "JaProgram" "JaProgram.in_names_unique_eq".
  unshelve (Reconstr.hcrush Reconstr.Empty
                  (@count_occ_zero_decl_once, @JaSyntax.find_class_further_neq, @name_once_further, @JaSyntax.find_class_in, @JaSyntax.find_class_same, @count_occ_zero_is_class_name_false, @Coq.Lists.List.Forall_forall, @name_once_further_eq, @names_unique_compose, @names_unique_further, @JaSyntax.find_class_eq, @names_unique_further_further, @is_class_name_nequal, @names_unique_zero, @Coq.Bool.Bool.absurd_eq_true)
                  (@JaSyntax.JFProgram, @Coq.Lists.List.map, @Coq.Lists.List.In, @name_once)); auto.
Qed.

Hint Resolve  in_names_unique_eq : myhints.

Lemma in_find_class_raw:
  forall CC cname ex fields methods,
    In (JFCDecl cname ex fields methods) CC ->
    exists ex1 fields1 methods1,
    find_class CC cname = Some (JFCDecl cname ex1 fields1 methods1).
Proof.
  induction CC; scrush.
Qed.

Lemma in_find_class:
  forall CC cname ex fields methods,
    names_unique CC ->
    In (JFCDecl cname ex fields methods) CC ->
    find_class CC cname = Some (JFCDecl cname ex fields methods).
Proof.
  induction CC;intros.
  - scrush.
  - destruct (JFClassDeclaration_dec (JFCDecl cname ex fields methods) a).
    + scrush.
    + try hammer_hook "JaProgram" "JaProgram.in_find_class.subgoal_2".
      destruct a.
      simpl.
      destruct (JFClassName_dec D cname).
      * try hammer_hook "JaProgram" "JaProgram.in_find_class.subgoal_2_1".
        (* Eprover finds a proof which is not reconstructible *)
        rewrite e in *.
        assert (ex = ex0 /\ fields = fields0 /\ methods = methods0)
          by eauto with myhints.
        scrush.
      * try hammer_hook "JaProgram" "JaProgram.in_find_class.subgoal_2_2".
        apply in_inv in H0.
        destruct H0.
        scrush.
        try hammer_hook "JaProgram" "JaProgram.in_find_class.subgoal_2_2_1".
        Reconstr.hobvious (@H0, @H, @IHCC)
                (@names_unique_further)
                Reconstr.Empty.
Qed.

Lemma names_unique_neq_but_in:
  forall CC cdecl ddecl,
         In cdecl (cdecl :: CC) ->
         ddecl <> cdecl ->
         names_unique (cdecl :: CC) ->
         In ddecl CC -> name_of_cd ddecl <> name_of_cd cdecl.
Proof.
  try hammer_hook "JaProgram" "JaProgram.names_unique_neq_but_in".
  (* Eprover finds a proof which is not reconstructible *)
  intros.
  destruct cdecl.
  destruct ddecl.
  simpl.
  try hammer_hook "JaProgram" "JaProgram.names_unique_neq_but_in.subgoal_0".
  Reconstr.hcrush (@H2, @H1)
                  (@count_occ_zero_is_class_name_false, @names_unique_zero, @is_class_name_nequal)
                  Reconstr.Empty.
Qed.

Lemma in_find_class_eq:
  forall CC cdecl cdecl',
    names_unique CC ->
    In cdecl CC ->
    find_class CC (name_of_cd cdecl) = Some cdecl' -> cdecl = cdecl'.
Proof.
  induction CC;intros.
  - scrush.
  - destruct (JFClassDeclaration_dec cdecl a).
    + scrush.
    + try hammer_hook "JaProgram" "JaProgram.in_find_class_eq.subgoal_1".
      (* EProver finds a proof which cannot be reconstructed *)
      assert (names_unique CC) by eauto using names_unique_further.
      assert (a = cdecl \/ In cdecl CC) by eauto.
      destruct H3. symmetry in H3. contradiction.
      assert (name_of_cd cdecl <> name_of_cd a).
      try hammer_hook "JaProgram" "JaProgram.in_find_class_eq.assert_1".
      (* Vampire finds a proof which cannot be reconstructed *)
      apply (names_unique_neq_but_in CC a cdecl); auto using in_eq.
      scrush.
Qed.

Hint Resolve in_find_class : myhints.

End JaProgram.

Require Coq.Program.Equality.

Module JaSubtype.

Import JaSyntax.
Import JaProgram.
Open Scope list_scope.
Import NPeano.
Import PeanoNat.

(**
  By [extends P C D] we mean that in the program [P] the class [C] is declared
  as a direct subclass of [D]. This is the formalisation of the *direct subtype relation, <_1*
  as defined in Section 4.10 of Java Language Specification.
*)
Inductive extends : JFProgram -> JFClassName -> JFClassName -> Prop  :=
| base : forall C D fields methods tl ex fields' methods',
           In (JFCDecl D ex fields' methods') tl ->
           extends ((JFCDecl C (Some D) fields methods) :: tl)%list C D
(** As written in Section 8.1.4 of Java Language Specification,
    "The optional extends clause in a normal class declaration specifies the direct
    superclass of the current class."
    We add here the check of the accessibility of the superclass as further it
    is written that
    "The ClassType must name an accessible class type (§6.6), or a compile-time
    error occurs." *)
| ind  : forall C1 C2 D1 D2 fields methods tl,
           extends tl C2 D2 ->
           extends ((JFCDecl C1 D1 fields methods) :: tl)%list C2 D2.
(** The extension of the direct subtype relation to the whole program. *)

Hint Constructors extends : myhints.

Lemma extends_in_first:
  forall P x x0,
    extends P x x0 ->
    (exists fields' methods',  In (JFCDecl x (Some x0) fields' methods') P).
Proof.
  induction P; scrush.
Qed.

Lemma extends_in_second:
  forall P x x0,
    extends P x x0 ->
    (exists ex fields' methods',  In (JFCDecl x0 ex fields' methods') P).
Proof.
  induction P; scrush.
Qed.

Lemma extends_in_second_second:
  forall P x x0,
    extends P x x0 ->
    forall P0 a,
      P = a :: P0 ->
      (exists ex fields' methods',  In (JFCDecl x0 ex fields' methods') P0).
Proof.
  induction 1.
  + sauto.
  + destruct tl; scrush.
Qed.

Lemma extends_narrower:
  forall (P : list JFClassDeclaration) (x x0 x1 : JFClassName)
    (ex : option JFClassName) (fields : list JFFieldDeclaration)
    (methods : list JFMethodDeclaration),
    extends (JFCDecl x0 ex fields methods :: P) x x1 ->
    x<>x0 ->
    extends P x x1.
Proof.
  scrush.
Qed.

Lemma extends_neq:
  forall P D1 C D0 ex fields methods,
  names_unique (JFCDecl D1 ex fields methods :: P) ->
  (exists cname dname : JFClassName,
         C = JFClass cname /\
         D0 = JFClass dname /\
         extends (JFCDecl D1 ex fields methods :: P) cname dname) ->
  D0 <> JFClass D1.
Proof.
  try hammer_hook "JaSubtype" "JaSubtype.extends_neq".
  intros.
  destruct H0, H0.
  decompose [and] H0; clear H0.
  eapply extends_in_second_second  in H4; [idtac | reflexivity].
  try hammer_hook "JaSubtype" "JaSubtype.extends_neq.subgoal_1".
  pose names_unique_zero; pose count_occ_not_In; scrush.
Qed.

Lemma extends_neq_none:
  forall P D1 cname dname fields methods,
    names_unique (JFCDecl D1 None fields methods :: P) ->
    extends (JFCDecl D1 None fields methods :: P) cname dname ->
    D1 <> cname.
Proof.
  assert (forall L cname dname,
             names_unique L ->
             extends L cname dname ->
             forall P D1 fields methods, L = JFCDecl D1 None fields methods :: P ->
             D1 <> cname); [idtac | scrush].
  induction 2.
  + sauto.
  + intros ? ? ? ? H2.
    injection H2.
    try hammer_hook "JaSubtype" "JaSubtype.extends_neq_none.subgoal_1".
    pose extends_in_first; pose count_occ_zero_is_class_name_false; scrush.
Qed.

Lemma extends_equals_first:
  forall C D E fields methods P,
    names_unique (JFCDecl C (Some D) fields methods :: P) ->
      extends (JFCDecl C (Some D) fields methods :: P) C E ->
      E = D.
Proof.
  intros C D E fields methods P Nuq Ext.
  inversion Ext.
  * auto.
  * subst.
    try hammer_hook "JaSubtype" "JaSubtype.extends_equals_first.subgoal_1".
    assert (forall x, In x P -> decl_once P x).
    assert (names_unique P).
    try hammer_hook "JaSubtype" "JaSubtype.extends_equals_first.assert_1".
    Reconstr.hobvious (@Nuq)
                      (@JaProgram.names_unique_further)
                      (@JaSyntax.JFProgram).
    try hammer_hook "JaSubtype" "JaSubtype.extends_equals_first.subgoal_1_1".
    Reconstr.hobvious (@H)
                      (@Coq.Lists.List.Forall_forall)
                      Reconstr.Empty.
    try hammer_hook "JaSubtype" "JaSubtype.extends_equals_first.subgoal_1_2".
    pose extends_in_first; scrush.
Qed.

Lemma names_unique_extends_non_refl:
  forall P C D,
    names_unique P -> extends P C D -> C <> D.
Proof.
  intros P C D Nuq H.
  induction H.
  + try hammer_hook "JaSubtype" "JaSubtype.names_unique_extends_non_refl.subgoal_1".
    Reconstr.hcrush Reconstr.AllHyps
                    (@JaProgram.names_unique_zero, @JaProgram.is_class_name_name,
                     @JaProgram.count_occ_zero_is_class_name_false)
                    Reconstr.Empty.
  + try hammer_hook "JaSubtype" "JaSubtype.names_unique_extends_non_refl.subgoal_2".
    Reconstr.hobvious (@Nuq, @IHextends)
                      (@JaProgram.names_unique_further)
                      Reconstr.Empty.
Qed.

Hint Resolve extends_narrower names_unique_extends_non_refl : myhints.


Fixpoint number_of_extends (P:JFProgram) (C:JFClassName) :=
  match P with
    | [] => None
    | (JFCDecl x (Some ex) fields' methods') :: P' =>
      if JFClassName_dec x C
      then match (number_of_extends P' ex) with
             | None => None
             | Some n => Some (n+1)
           end
      else number_of_extends P' C
    | (JFCDecl x None fields' methods') :: P' =>
      if JFClassName_dec x JFObjectName
      then if JFClassName_dec C JFObjectName
           then Some 0
           else number_of_extends P' C
      else None
  end.

Lemma number_of_extends_compose:
  forall ex flds mthds P C D n,
    D<>C ->
    number_of_extends P C = Some n ->
    number_of_extends ((JFCDecl D (Some ex) flds mthds) :: P) C = Some n.
Proof.
  scrush.
Qed.


Lemma number_of_extends_compose_eq:
  forall flds mthds P C D n,
    number_of_extends P C = Some n ->
    number_of_extends ((JFCDecl D (Some C) flds mthds) :: P) D = Some (n+1).
Proof.
  scrush.
Qed.


Lemma number_of_extends_decompose:
  forall ex flds mthds P C n,
    number_of_extends ((JFCDecl C (Some ex) flds mthds) :: P) C = Some n ->
    number_of_extends P ex = Some (n-1) /\ n > 0.
Proof.
  try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_decompose".
  intros.
  unfold number_of_extends in H.
  destruct (JFClassName_dec C C).
  + fold (number_of_extends P ex) in H.
    destruct (number_of_extends P ex).
    ++ try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_decompose.subgoal_1".
       Reconstr.hobvious (@H)
                         (@Coq.Arith.PeanoNat.Nat.pred_succ, @Coq.Arith.PeanoNat.Nat.add_1_r, @Coq.Arith.PeanoNat.Nat.sub_1_r, @Coq.Arith.Gt.gt_Sn_O)
                         Reconstr.Empty.
    ++ discriminate H.
  + tauto.
Qed.


Lemma number_of_extends_decompose_neq:
  forall ex flds mthds P C D n,
    C<>D ->
    number_of_extends ((JFCDecl C ex flds mthds) :: P) D = Some n ->
    number_of_extends P D = Some n.
Proof.
  scrush.
Qed.

Lemma number_of_extends_none:
  forall P D fields methods,
    D <> JFObjectName ->
    number_of_extends (JFCDecl D None fields methods :: P) D = None.
Proof.
  scrush.
Qed.


Lemma number_of_extends_find_class_simple:
  forall P j n,
    number_of_extends P j = Some (n) ->
         exists x,find_class P j = Some x.
Proof.
  induction P.
  * sauto.
  * try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class_simple.subgoal_2".
    intros.
    unfold number_of_extends in H.
    destruct a.
    destruct ex.
    destruct (JFClassName_dec D j).
    clear H.
    scrush.
    scrush.
    fold (number_of_extends P j) in H.
    destruct (JFClassName_dec j JFObjectName).
    scrush.
    scrush.
Qed.

Lemma number_of_extends_zero:
  forall P cn,
    number_of_extends P cn = Some 0 ->
    cn = JFObjectName.
Proof.
  induction P; scrush.
Qed.

Lemma names_unique_number_of_extends_loop:
  forall C flds mthds P,
         names_unique ((JFCDecl C (Some C) flds mthds) :: P) ->
         number_of_extends ((JFCDecl C (Some C) flds mthds) :: P) C = None.
Proof.
  try hammer_hook "JaSubtype" "JaSubtype.names_unique_number_of_extends_loop".
  pose number_of_extends_find_class_simple; pose names_unique_zero;
    pose find_class_program_contains; pose program_contains_counts_occ;
      scrush.
Qed.

Hint Resolve number_of_extends_compose number_of_extends_compose_eq number_of_extends_decompose
     number_of_extends_decompose_neq number_of_extends_none : myhints.

Lemma is_class_and_occ_zero:
  forall P C D CC, names_unique P ->
            find_class P C = Some CC ->
            count_occ Bool.bool_dec (map (is_class_name D) P) true = 0 ->
            C <> D.
Proof.
  induction P.
  + sauto.
  + try hammer_hook "JaSubtype" "JaSubtype.is_class_and_occ_zero.subgoal_2".
    intros.
    destruct a.
    assert ({C=D} + {C<>D}) by apply JFClassName_dec.
    destruct H2.
    * try hammer_hook "JaSubtype" "JaSubtype.is_class_and_occ_zero.subgoal_2_1".
      rewrite e in *.
      rewrite map_cons in H1.
      unfold is_class_name in H1.
      destruct (JFClassName_dec D0 D).
      - scrush.
      - try hammer_hook "JaSubtype" "JaSubtype.is_class_and_occ_zero.subgoal_2_1_1".
        pose count_occ_cons_neq; pose names_unique_further;
          pose find_class_further_neq; scrush.
    * auto.
Qed.

Lemma names_unique_in_neq:
  forall P C D ex fields methods ex1 fields1 methods1,
    names_unique (JFCDecl C ex fields methods :: P) ->
    In (JFCDecl D ex1 fields1 methods1) P ->
    C <> D.
Proof.
  try hammer_hook "JaSubtype" "JaSubtype.names_unique_in_neq".
  Reconstr.hsimple Reconstr.Empty
                   (@JaProgram.in_find_class_raw, @JaProgram.is_class_name_name, @JaProgram.names_unique_zero, @JaProgram.count_occ_zero_is_class_name_false, @Coq.Bool.Bool.diff_false_true, @JaProgram.names_unique_further)
                   Reconstr.Empty.
Qed.

Hint Resolve names_unique_in_neq : myhints.

Lemma names_unique_count_zero:
  forall P D ex fields methods,
    names_unique (JFCDecl D ex fields methods :: P) ->
    count_occ Bool.bool_dec (map (is_class_name D) P) true = 0.
Proof.
  scrush.
Qed.

Lemma number_of_extends_find_class:
  forall (P:JFProgram) (C D:JFClassName) fields methods (n:nat) (CC:JFClassDeclaration),
    names_unique (JFCDecl C (Some D) fields methods :: P) ->
    number_of_extends (JFCDecl C (Some D) fields methods :: P) C =
       Some n ->
  exists CC : JFClassDeclaration,
    find_class (JFCDecl C (Some D) fields methods :: P) D = Some CC.
Proof.
  induction P.
  - sauto.
  - intros.
    destruct a.
    assert ({D=D0}+{D<>D0}) by auto using JFClassName_dec.
    destruct H1.
    * try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.subgoal_2".
      rewrite e in *. (* D = D0 *)
      assert (C<>D0) by scrush.
      unfold names_unique in H.
      assert (forall x, In x (JFCDecl C (Some D0) fields methods
         :: JFCDecl D0 ex fields0 methods0 :: P) ->  (decl_once
           (JFCDecl C (Some D0) fields methods
                    :: JFCDecl D0 ex fields0 methods0 :: P)) x).
      try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.assert_1".
      apply Forall_forall; auto.
      assert (decl_once
         (JFCDecl C (Some D0) fields methods
                  :: JFCDecl D0 ex fields0 methods0 :: P)
         (JFCDecl D0 ex fields0 methods0)).
      try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.assert_2".
      apply H2; sauto.
      exists (JFCDecl D0 ex fields0 methods0).
      scrush.
    * assert ({C=D} + {C<>D}) by apply JFClassName_dec.
      destruct H1.
      + scrush.
      + try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.subgoal_3_1".
        assert (exists CC0 : JFClassDeclaration,
                  find_class (JFCDecl C (Some D) fields methods :: P) D =
                  Some CC0).
        try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.assert_3".
        apply (IHP C D fields methods n).
        auto.
        apply (names_unique_further_further P
                (JFCDecl C (Some D) fields methods)
                (JFCDecl D0 ex fields0 methods0)).
        auto.
        apply number_of_extends_decompose in H0.
        assert (number_of_extends P D =
                Some (n - 1)) by scrush.
        assert (HH: n = n - 1 + 1).
        try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.assert_4".
        Reconstr.hobvious (@H0)
                (@Coq.Arith.PeanoNat.Nat.sub_1_r, @Coq.Arith.PeanoNat.Nat.succ_pred, @Coq.Arith.PeanoNat.Nat.neq_0_lt_0, @Coq.Arith.PeanoNat.Nat.add_1_r)
                Reconstr.Empty.
        scrush.
        try hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.subgoal_3_2".
        Reconstr.hobvious (@H1)
                (@JaSyntax.find_class_further_neq, @JaSyntax.find_class_same)
                (@JaSyntax.JFProgram).
Qed.

Definition subtype_well_founded (P:JFProgram) :=
  forall (C:JFClassName) (CC:JFClassDeclaration),
    find_class P C = Some CC -> exists (n:nat), number_of_extends P C = Some n.

Lemma subtype_well_founded_further:
  forall P C,
    names_unique (C::P) ->
    subtype_well_founded (C :: P) -> subtype_well_founded P.
Proof.
  intros.
  unfold subtype_well_founded in *.
  intros.
  destruct C.
  assert (count_occ Bool.bool_dec (map (is_class_name D) P) true = 0) by
      (apply (names_unique_count_zero P D ex fields methods); auto).
  assert (C0 <> D) by
  (try apply (is_class_and_occ_zero P C0 D CC);
   auto using (names_unique_further P (JFCDecl D ex fields methods))).
  destruct ex.
  assert ({j=C0} + {j<>C0}) by apply JFClassName_dec.
  destruct H4.
  - scrush.
  - try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_further.subgoal_2".
    lapply (H0 C0 CC); intros.
    destruct H4.
    exists x.
    scrush.
    scrush.
  - try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_further.subgoal_3".
    assert ( exists n : nat,
               number_of_extends (JFCDecl D None fields methods :: P) C0 = Some n).
    try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_further.assert_1".
    Reconstr.hcrush (@H3, @H1, @H0)
                    (@JaSyntax.find_class_same)
                    (@JaSyntax.JFProgram).
    scrush.
Qed.

Lemma subtype_well_founded_decompose_program:
  forall P P',
    names_unique (P ++ P') ->
    subtype_well_founded (P ++ P') -> subtype_well_founded P'.
Proof.
  induction P.
  + sauto.
  + try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_decompose_program.subgoal_2".
    Reconstr.hobvious (@IHP)
                      (@Coq.Lists.List.Forall_forall, @Coq.Lists.List.Forall_cons, @Coq.Init.Datatypes.list_ind, @Coq.Lists.List.app_comm_cons, @is_class_and_occ_zero, @JaProgram.names_unique_compose, @JaProgram.names_unique_further, @subtype_well_founded_further, @JaProgram.names_unique_decompose_program)
                      (@Coq.Lists.List.In, @JaSyntax.JFClassName, @Coq.Lists.List.count_occ, @Coq.Lists.List.map, @Coq.Init.Datatypes.app, @JaSyntax.find_class, @JaProgram.names_unique, @number_of_extends, @JaSyntax.JFProgram, @subtype_well_founded).
Qed.

Lemma subtype_get_superclass:
  forall (P:JFProgram) (C x ex:JFClassName) fields methods,
      names_unique P ->
      subtype_well_founded P ->
      find_class P C = Some (JFCDecl x (Some ex) fields methods) ->
      exists CC,
      find_class P ex = Some CC.
Proof.
  induction P.
  + scrush.
  + try hammer_hook "JaSubtype" "JaSubtype.subtype_get_superclass.subgoal_2".
    intros.
    destruct a.
    assert ({D=ex}+{D<>ex}) by apply JFClassName_dec; destruct H2; auto.
    exists (JFCDecl D ex0 fields0 methods0).
    scrush.
    assert ({C=D} + {C <> D}) by apply JFClassName_dec; destruct H2; auto.
    rewrite e in *.
    simpl in H1.
    destruct (JFClassName_dec D D).
    assert (D=x);injection H1;auto.
    intros.
    rewrite H6 in *.
    unfold subtype_well_founded in H0.
    assert ({x=ex}+{x<>ex}) by apply JFClassName_dec; destruct H7; auto.
    rewrite e1 in *.
    exists (JFCDecl ex ex0 fields0 methods0).
    scrush.
    assert ( exists n : nat,
               number_of_extends (JFCDecl x ex0 fields0 methods0 :: P) x = Some n).
    try hammer_hook "JaSubtype" "JaSubtype.subtype_get_superclass.assert_1".
    Reconstr.hobvious (@H0)
                      (@JaSyntax.find_class_eq)
                      Reconstr.Empty.
    destruct H7.
    rewrite H5 in *.
    try hammer_hook "JaSubtype" "JaSubtype.subtype_get_superclass.subgoal_2_1".
    Reconstr.hcrush (@H, @H7)
                    (@number_of_extends_find_class)
                    (@JaSyntax.JFProgram).
    scrush.
    simpl.
    destruct (JFClassName_dec D ex).
    exists (JFCDecl D ex0 fields0 methods0).
    auto.
    try hammer_hook "JaSubtype" "JaSubtype.subtype_get_superclass.subgoal_2_2".
    eapply IHP.
    eapply names_unique_further.
    apply H.
    eapply subtype_well_founded_further.
    scrush.
    scrush.
    scrush.
    Unshelve.
    dsolve.
    dsolve.
Qed.

Lemma subtype_well_founded_superclass:
  forall (P:JFProgram) (C D:JFClassName) (ex:option JFClassName) fields methods,
    subtype_well_founded P ->
    names_unique P ->
    find_class P C = Some (JFCDecl D ex fields methods) ->
    C <> JFObjectName ->
    exists D',
      find_class P C = Some (JFCDecl D (Some D') fields methods).
Proof.
  induction P.
  + scrush.
  + intros.
    simpl.
    destruct a.
    simpl in H1.
    destruct (JFClassName_dec D0 C).
    ++ try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_superclass.subgoal_1".
       subst.
       unfold subtype_well_founded in H.
       simpl in H1.
       assert (exists n : nat, number_of_extends (JFCDecl C ex0 fields0 methods0 :: P) C = Some n).
       try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_superclass.assert_1".
       Reconstr.hobvious (@H)
                         (@JaSyntax.find_class_eq)
                         Reconstr.Empty.
       scrush.
    ++ try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_superclass.subgoal_2".
       eapply IHP; eauto.
       eapply subtype_well_founded_further.
       scrush.
       scrush.
       try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_superclass.subgoal_2_1".
       Reconstr.hobvious (@H0)
                         (@JaProgram.names_unique_further)
                         (@JaSyntax.JFProgram).
Qed.

Lemma find_class_extends:
  forall P cname name dname fields methods D,
    find_class P cname = Some (JFCDecl name (Some dname) fields methods) ->
    find_class P dname = Some D ->
    subtype_well_founded P ->
    names_unique P ->
    cname <> dname ->
    extends P cname dname.
Proof.
  induction P.
  + scrush.
  + intros.
    destruct a.
    simpl in H.
    destruct (JFClassName_dec D0 cname).
    ++ (* D0 = cname *)
      subst.
      try hammer_hook "JaSubtype" "JaSubtype.find_class_extends.subgoal_1".
      injection H;intros;clear H;subst.
      destruct D.
      assert (dname=D) by eauto using find_class_eq_name.
      subst.
      eapply find_class_in in H0.
      apply in_inv in H0.
      destruct H0.
      +++ scrush.
      +++ try hammer_hook "JaSubtype" "JaSubtype.find_class_extends.subgoal_1_1".
          Reconstr.reasy (@base, @Coq.Init.Peano.f_equal_nat) Reconstr.Empty.
    ++ (* D0 <> cname *)
      apply ind.
      try hammer_hook "JaSubtype" "JaSubtype.find_class_extends.subgoal_2".
      assert (exists P0 P1,
                 P = P0 ++ ((JFCDecl name (Some dname) fields methods) :: P1)).
      try hammer_hook "JaSubtype" "JaSubtype.find_class_extends.assert_1".
      Reconstr.reasy (@JaSyntax.find_class_decompose_program) (@JaSyntax.JFProgram).
      destruct H4 as [P0 [P1 H4]].
      rewrite H4 in *.
      assert (exists D', find_class
                           (JFCDecl name (Some dname) fields methods ::P1)
                           dname = Some D').
      try hammer_hook "JaSubtype" "JaSubtype.find_class_extends.assert_2".
      {
        rewrite app_comm_cons in H1.
        assert (subtype_well_founded
                  (JFCDecl name (Some dname) fields methods :: P1)).
        try hammer_hook "JaSubtype" "JaSubtype.find_class_extends.assert_3".
        rewrite app_comm_cons in H2; eauto using subtype_well_founded_decompose_program.
        eapply subtype_get_superclass;eauto 3 using subtype_well_founded_further with myhints .
        assert (find_class (JFCDecl name (Some dname) fields methods :: P1)
                           name =
                Some (JFCDecl name (Some dname) fields methods)).
        simpl.
        destruct (JFClassName_dec name name); try contradiction;auto with myhints.
        apply H6.
      }
      destruct H5.
      assert (exists C',
                 find_class
                   (P0 ++ (JFCDecl name (Some dname) fields methods) :: P1)
                   dname = Some C').
      try hammer_hook "JaSubtype" "JaSubtype.find_class_extends.assert_4".
      Reconstr.reasy (@JaSyntax.find_class_lift) (@JaSyntax.JFProgram).
      try hammer_hook "JaSubtype" "JaSubtype.find_class_extends.subgoal_2_1".
      destruct H6.
      eapply IHP; eauto 2 using subtype_well_founded_further with myhints.
Qed.

Lemma subtype_well_founded_contains_object:
  forall P name cl,
    names_unique P ->
    subtype_well_founded P ->
    find_class P name = Some cl ->
    program_contains P JFObjectName = true.
Proof.
  induction P.
  * scrush.
  * intros.
    destruct a.
    destruct (JFClassName_dec D JFObjectName).
    rewrite e.
    unfold program_contains.
    destruct (JFClassName_dec JFObjectName JFObjectName).
    - auto.
    - intuition.
    - try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1".
      destruct (JFClassName_dec D name).
      destruct P.
      (* P = [] *)
      unfold subtype_well_founded in H0.
      destruct ex.
      unfold number_of_extends in H0.
      lapply (H0 D cl); intros.
      destruct H2.
      destruct (JFClassName_dec D D).
      discriminate H2.
      discriminate H2.
      rewrite e in *.
      auto.
      unfold number_of_extends in H0.
      lapply (H0 D cl); intros.
      destruct (JFClassName_dec D JFObjectName).
      auto.
      destruct H2.
      discriminate H2.
      lapply (H0 D cl); intros.
      destruct (JFClassName_dec D JFObjectName).
      intuition.
      destruct H2.
      discriminate H2.
      auto.
      rewrite e in *.
      auto.
      (* P = hd :: tl *)
      destruct j.
      lapply (IHP D0 (JFCDecl D0 ex0 fields0 methods0));intros.
      assert (program_contains (JFCDecl D0 ex0 fields0 methods0 :: P) JFObjectName = true).
      try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.assert_1".
      apply H2.
      + try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_1".
        eapply subtype_well_founded_further.
        apply H.
        apply H0.
      + try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_2".
        Reconstr.reasy (@JaSyntax.find_class_eq) Reconstr.Empty.
      + try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_3".
        Reconstr.reasy (@JaSyntax.program_contains_further) (@JaSyntax.JFClassName, @JaSyntax.JFProgram).
      + try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_4".
        Reconstr.reasy (@JaProgram.names_unique_further) (@JaSyntax.JFProgram).
      + try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_5".
        assert (program_contains P JFObjectName = true).
        try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.assert_2".
        apply (IHP name cl).
        try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_5_1".
        Reconstr.reasy (@JaProgram.names_unique_further) (@JaSyntax.JFProgram).
        try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_5_2".
        Reconstr.reasy (@subtype_well_founded_further) Reconstr.Empty.
        scrush.
        try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_5_3".
        Reconstr.reasy (@JaSyntax.program_contains_further) (@JaSyntax.JFClassName, @JaSyntax.JFProgram).
Qed.

Lemma subtype_well_founded_program_contains_further:
  forall P a b,
    names_unique (a::b::P) ->
    (program_contains (a::b::P) JFObjectName) = true ->
    subtype_well_founded (a::b::P) ->
    (program_contains (b::P) JFObjectName) = true.
Proof.
  induction P.
  * try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_program_contains_further.subgoal_1".
    intros.
    destruct a.
    destruct b.
    destruct (JFClassName_dec D JFObjectName).
    ** subst.
       assert (JFObjectName <> D0) by scrush.
       unfold subtype_well_founded in H1.
       assert (exists n : nat,
                  number_of_extends
                    [JFCDecl JFObjectName ex fields methods;
                     JFCDecl D0 ex0 fields0 methods0] D0 = Some n).
       try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_program_contains_further.assert_1".
       eapply H1.
       eapply find_class_same;eauto 2.
       apply find_class_eq.
       unfold number_of_extends in H3.
       destruct ex.
       *** scrush.
       *** scrush.
    ** try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_program_contains_further.subgoal_1_1".
       eapply program_contains_further_neq; eauto.
  * try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_program_contains_further.subgoal_2".
    intros.
    destruct b.
    eapply subtype_well_founded_contains_object;eauto 2 with myhints.
    eauto using subtype_well_founded_further with myhints.
    eapply find_class_eq.
Qed.

Lemma subtype_well_founded_neq:
  forall P name name' fields methods,
    names_unique  (JFCDecl name (Some name') fields methods :: P) ->
    subtype_well_founded (JFCDecl name (Some name') fields methods :: P) ->
    name <> name'.
Proof.
  intros.
  unfold subtype_well_founded in H0.
  intro.
  subst name'.
  specialize H0 with name (JFCDecl name (Some name) fields methods).
  try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_neq.subgoal_0".
  lapply H0;intros.
  + try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_neq.subgoal_1".
    Reconstr.rcrush (@names_unique_number_of_extends_loop) Reconstr.Empty.
  + scrush.
Qed.

Lemma subtype_well_founded_find_class_neq:
  forall P name name' fields methods,
    names_unique  P ->
    subtype_well_founded P ->
    find_class P name = Some (JFCDecl name (Some name') fields methods) ->
    name <> name'.
Proof.
  induction P.
  + scrush.
  + try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_find_class_neq.subgoal_1".
    intros.
    destruct a.
    simpl in H1.
    destruct (JFClassName_dec D name).
    ++ try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_find_class_neq.subgoal_1_1".
       Reconstr.rcrush (@subtype_well_founded_neq) Reconstr.Empty.
    ++ try hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_find_class_neq.subgoal_1_2".
       Reconstr.rcrush (@subtype_well_founded_further, @JaProgram.names_unique_further) (@JaSyntax.JFProgram).
Qed.

(** The property that all class names occur in the program uniquely. *)
Definition if_not_extended_then_object (cdecl:JFClassDeclaration) :=
  match cdecl with
    | JFCDecl cname None _ _ => cname = JFObjectName
    | JFCDecl _ (Some _) _ _ => cdecl = cdecl
  end.

(** The property that only Object class is not an extension of another class *)
Definition extensions_in_all_but_object (P:JFProgram) :=
  Forall (if_not_extended_then_object) P.

Lemma extensions_in_all_but_object_further:
forall (P:JFProgram) (cdecl:JFClassDeclaration),
    extensions_in_all_but_object (cdecl::P) ->
    extensions_in_all_but_object P.
Proof.
  scrush.
Qed.

Hint Resolve  extensions_in_all_but_object_further subtype_well_founded_further subtype_well_founded_decompose_program : myhints.

(** The property that Object class is not extended. As
    Java Language Specification says in Section 8.1.4:
    "The extends clause must not appear in the definition
    of the class Object, or a compile-time error occurs,
    because it is the primordial class and has no direct superclass." *)
Definition object_not_extended (cdecl:JFClassDeclaration) :=
  match cdecl with
    | JFCDecl cname x _ _ => cname = JFObjectName -> x = None
  end.


(** A single check that Object is not extended is
    lifted to the whole program. *)
Definition object_is_not_extended (P:JFProgram) :=
  Forall (object_not_extended) P.

Lemma object_is_not_extended_further:
forall (P:JFProgram) (cdecl:JFClassDeclaration),
    object_is_not_extended (cdecl::P) ->
    object_is_not_extended P.
Proof.
  scrush.
Qed.

Lemma object_is_not_extended_first:
  forall (P:JFProgram) cname x fs ms,
    object_is_not_extended (JFCDecl cname (Some x) fs ms :: P) ->
    cname <> JFObjectName.
Proof.
  scrush.
Qed.

Lemma extends_further_object:
  forall (P:JFProgram) (C:JFClassDeclaration) (cname dname:JFClassName),
   object_is_not_extended (C :: P) ->
   JFObject = JFClass cname -> extends (C :: P) cname dname -> extends P cname dname.
Proof.
  induction P.
  + scrush.
  + try hammer_hook "JaSubtype" "JaSubtype.extends_further_object.subgoal_1".
    intros.
    inversion H1.
    unfold JFObject in H0.
    injection H0; intros.
    rewrite <- H7 in *.
    unfold object_is_not_extended in H.
    scrush.
    auto.
Qed.

Lemma object_is_not_extended_extends_neq:
  forall P cname dname,
    object_is_not_extended P ->
    extends P cname dname ->
    cname <> JFObjectName.
Proof.
  induction 2; scrush.
Qed.

Hint Resolve  object_is_not_extended_extends_neq extends_further_object object_is_not_extended_first object_is_not_extended_further : myhints.

(*
Inductive subtyping : JFProgram -> JFCId -> JFCId -> Prop :=
| subrefl  : forall (P:JFProgram) (C:JFCId), subtyping P C C
| subobj   : forall (P:JFProgram) (C:JFCId), subtyping P C JFObject
| botobj   : forall (P:JFProgram) (C:JFCId), subtyping P JFBotClass C
| subext   : forall (P:JFProgram) (C:JFCId) (D:JFCId), extends P C D -> subtyping P C D
| subtrans : forall (P:JFProgram) (C:JFCId) (D:JFCId) (E:JFCId), subtyping P C D -> subtyping P D E -> subtyping P C E.
 *)

Inductive subtyping : JFProgram -> JFCId -> JFCId -> Prop :=
| subrefl  : forall (P:JFProgram) (C:JFCId), subtyping P C C
| subobj   : forall (P:JFProgram) (C:JFCId), subtyping P C JFObject
| botobj   : forall (P:JFProgram) (C:JFCId), subtyping P JFBotClass C
| substep  : forall (P:JFProgram) (C:JFCId) (D:JFCId) (E:JFCId)
                    (cname:JFClassName) (dname:JFClassName),
               C = JFClass cname -> D = JFClass dname ->
               extends P cname dname ->
               subtyping P D E -> subtyping P C E.

Hint Constructors subtyping : myhints.


Lemma subtyping_further:
  forall (P:JFProgram) (cid:JFCId) (did:JFCId) (E:JFClassDeclaration),
    subtyping P cid did -> subtyping (E :: P) cid did.
Proof.
  induction 1.
  * scrush.
  * scrush.
  * scrush.
  * try hammer_hook "JaSubtype" "JaSubtype.subtyping_further.subgoal_1".
    eapply (substep (E :: P) C D E0).
    + scrush.
    + scrush.
    + inversion H1.
      - destruct E.
        try hammer_hook "JaSubtype" "JaSubtype.subtyping_further.subgoal_1_1".
        Reconstr.reasy (@ind) Reconstr.Empty.
      - destruct E.
        try hammer_hook "JaSubtype" "JaSubtype.subtyping_further.subgoal_1_2".
        Reconstr.reasy (@ind) Reconstr.Empty.
    + auto.
Qed.

Lemma object_is_not_subtype:
  forall (P:JFProgram) (E:JFCId),
    names_unique P ->
    object_is_not_extended P ->
    extensions_in_all_but_object P ->
    subtyping P JFObject E -> E = JFObject.
Proof.
  induction P.
  * scrush.
  * intros.
    apply IHP.
    + try hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.subgoal_1".
      Reconstr.reasy (@JaProgram.names_unique_further) (@object_not_extended, @JaSyntax.JFProgram).
    + scrush.
    + scrush.
    + inversion H2.
      - scrush.
      - scrush.
      - unfold object_is_not_extended in H0.
        try hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.subgoal_2".
        { inversion H5.
          + try hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.subgoal_2_1".
            rewrite H11 in *.
            apply Forall_inv in H0.
            rewrite <- H10 in *.
            unfold object_not_extended in H0.
            lapply H0; intros; clear H0.
            discriminate H15.
            unfold JFObject in H3.
            congruence.
          +  assert (exists ex0 fields' methods',  In (JFCDecl cname (Some ex0) fields' methods') P).
             try hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.assert_1".
             Reconstr.reasy (@extends_in_first) (@JaSyntax.JFProgram).
             try hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.subgoal_2_2".
             destruct H15, H15, H15.
             assert (forall x, In x (a :: P) -> object_not_extended x).
             try hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.assert_2".
             apply -> (Forall_forall object_not_extended (a :: P)).
             auto.
             assert (object_not_extended (JFCDecl cname (Some x) x0 x1)).
             apply H16.
             apply in_cons.
             auto.
             lapply H17 ; intros.
             discriminate H18.
             unfold JFObject in H3.
             congruence.
          }
Qed.

Lemma subtrans : forall (P:JFProgram) (C:JFCId) (D:JFCId) (E:JFCId),
                   (program_contains P JFObjectName) = true ->
                   names_unique P ->
                   object_is_not_extended P ->
                   extensions_in_all_but_object P ->
                   subtyping P C D -> subtyping P D E -> subtyping P C E.
Proof.
  induction P.
  + scrush.
  + induction 5.
    - auto.
    - try hammer_hook "JaSubtype" "JaSubtype.subtrans.subgoal_1".
      Reconstr.reasy (@subobj, @object_is_not_subtype) Reconstr.Empty.
    - scrush.
    - try hammer_hook "JaSubtype" "JaSubtype.subtrans.subgoal_2".
      Reconstr.reasy (@substep) Reconstr.Empty.
Qed.

Lemma subtyping_greater_in:
  forall P C D,
    subtyping P C D ->
    forall cn dn,
    C = (JFClass cn) ->
    D = (JFClass dn) ->
    names_unique P ->
    object_is_not_extended P ->
    extensions_in_all_but_object P ->
    cn <> dn ->
    dn <> JFObjectName ->
    exists ex fields methods,
      In (JFCDecl dn ex fields methods) P.
Proof.
  intros P C D H.
  induction H; sauto.
  * ycrush.
  * try hammer_hook "JaSubtype" "JaSubtype.subtyping_greater_in.subgoal_0".
    destruct (JFClassName_dec dname dn).
    ** try hammer_hook "JaSubtype" "JaSubtype.subtyping_greater_in.subgoal_1".
       Reconstr.reasy (@extends_in_second) Reconstr.Empty.
    ** scrush.
Qed.

Lemma subtyping_further_neq:
  forall P P0 D E,
    subtyping P0 D E ->
    names_unique P0 ->
    forall C ex fields methods,
      P0 = (JFCDecl C ex fields methods :: P) ->
      D <> JFClass C ->
      subtyping P D E.
Proof.
  induction 1; sauto.
  - try hammer_hook "JaSubtype" "JaSubtype.subtyping_further_neq.subgoal_1".
    Reconstr.rblast (@extends_narrower, @JaProgram.count_occ_zero_is_class_name_false, @substep, @JaProgram.is_class_name_nequal, @extends_in_second) (@JaSyntax.JFProgram).
Qed.

Lemma subtyping_not_bot:
  forall P C D,
    subtyping P C D -> D = JFBotClass  -> C = JFBotClass.
Proof.
  induction 1; sauto.
Qed.

Lemma subtyping_find_class:
  forall P C D Cid,
    C <> D ->
    D <> JFObject ->
    JFClass Cid = C ->
    names_unique P ->
    subtyping P C D ->
    exists CC, find_class P Cid = Some CC.
Proof.
  intros.
  inversion H3; sauto.
  + try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class.subgoal_1".
    assert (exists
               (ex0 : JFClassName) (fields' : list JFFieldDeclaration)
               (methods' : list JFMethodDeclaration),
               In (JFCDecl cname (Some ex0) fields' methods') P).
    try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class.assert_1".
    Reconstr.reasy (@extends_in_first) Reconstr.Empty.
    destruct H1, H1, H1.
    exists (JFCDecl cname (Some x) x0 x1).
    try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class.subgoal_1_1".
    Reconstr.reasy (@JaProgram.in_find_class) Reconstr.Empty.
Qed.

Lemma subtyping_find_class_gt:
  forall P C D Did,
    C <> D ->
    C <> JFBotClass ->
    JFClass Did = D ->
    names_unique P ->
    subtype_well_founded P ->
    program_contains P JFObjectName = true ->
    subtyping P C D ->
    exists CC, find_class P Did = Some CC.
Proof.
  induction P.
  + scrush.
  + intros C D Did CDneq CJFB DidD Nuq Swf PctsObj Sub.
    inversion Sub.
    ++ contradiction.
    ++ subst.
       try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_1".
       injection H1;intros.
       subst.
       apply program_contains_find_class;auto.
    ++ subst. contradiction.
    ++ subst.
       destruct a.
       unfold find_class.
       destruct (JFClassName_dec D Did).
       +++ scrush.
       +++ fold (find_class P Did).
           try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2".
           assert (exists
                      (ex0 : option JFClassName)
                      (fields' : list JFFieldDeclaration)
                      (methods' : list JFMethodDeclaration),
                      In (JFCDecl dname ex0 fields' methods') P).
           try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.assert_1".
           eauto using extends_in_second_second.
           do 3 destruct H.
           destruct (JFClassName_dec D cname).
           * subst.
             try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_1".
             destruct (JFClassName_dec cname dname).
             ** try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_1_1".
                (* EProver finds a proof which cannot be reconstructed *)
                subst.
                assert (JFClass dname <> JFClass dname).
                eapply extends_neq;eauto.
                contradiction.
             ** assert (JFClass cname <> JFClass dname) by congruence.
                try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_1_2".
                destruct (JFClassName_dec dname Did).
                *** try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_1_2_1".
                    subst; eauto with myhints.
                *** try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_1_2_2".
                    assert (subtyping P (JFClass dname) (JFClass Did)).
                    try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.assert_2".
                    eapply subtyping_further_neq ;
                      try apply H2;eauto 2 with myhints.
                    eapply IHP;
                      try apply H3; try apply CDneq;
                        try apply CJFB;try congruence;eauto 2 with myhints.
                    {
                      destruct P.
                      * inversion H.
                      * try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_1_2_2_1".
                        Reconstr.reasy (@subtype_well_founded_program_contains_further) Reconstr.Empty.
                    }
           * subst.
             try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_2".
             assert (JFClass dname <> JFClass D).
             try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.assert_3".
             clear -H1 Nuq.
             eapply extends_neq; eauto.
             assert (JFClass D <> JFClass Did) by congruence.
             destruct (JFClassName_dec dname Did).
             ** try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_2_1".
                subst; eauto with myhints.
             ** assert (JFClass dname <> JFClass Did) by congruence.
                try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_2_2".
                eapply IHP; try eapply H4; eauto 2 with myhints.
                *** discriminate.
                *** destruct P.
                    **** inversion H.
                    **** eauto using subtype_well_founded_program_contains_further with myhints.
                *** try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_gt.subgoal_2_2_2_1".
                    eapply subtyping_further_neq; eauto.
Qed.

Lemma subtyping_neq_object:
  forall P dname D,
    object_is_not_extended P ->
    (JFClass dname) <> D  ->
    subtyping P (JFClass dname) D ->
    JFClass dname <> JFObject.
Proof.
  intros.
  inversion H1; sauto.
  + try hammer_hook "JaSubtype" "JaSubtype.subtyping_neq_object.subgoal_1".
    Reconstr.rcrush (@object_is_not_extended_extends_neq) (@JaSyntax.JFObject, @JaSyntax.JFObjectName).
Qed.

Lemma subtyping_find_class_further:
  forall P D E,
    subtyping P D E ->
    forall  P0 cd cn' ex fields methods dn en,
      P = (cd :: P0) ->
      cd = JFCDecl cn' ex fields methods ->
      D = (JFClass dn) ->
      E = (JFClass en) ->
      E <> JFObject ->
      dn <> en ->
      dn <> cn' ->
      exists cd, find_class P0 dn = Some cd.
Proof.
  intros P D E H.
  induction H; sauto.
  * try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_further.subgoal_1".
    eapply extends_in_first in H1.
    destruct H1. destruct H.
    eapply in_inv in H.
    destruct H.
    ** congruence.
    ** try hammer_hook "JaSubtype" "JaSubtype.subtyping_find_class_further.subgoal_1_1".
       eapply in_find_class_raw in H.
       scrush.
Qed.

Hint Resolve subtyping_further object_is_not_subtype subtrans subtyping_further_neq subtyping_find_class : myhints.


Lemma subtyping_object_supremum:
  forall P C,
    names_unique P ->
    object_is_not_extended P ->
    extensions_in_all_but_object P ->
      subtype_well_founded P ->
    subtyping P JFObject C ->
    C = JFObject.
Proof.
  induction P.
  * scrush.
  * try hammer_hook "JaSubtype" "JaSubtype.subtyping_object_supremum.subgoal_1".
    intros.
    apply IHP;eauto 2 with myhints.
    destruct a.
    destruct (JFCId_dec (JFClass D) JFObject).
    assert (C = JFObject).
    try hammer_hook "JaSubtype" "JaSubtype.subtyping_object_supremum.assert_1".
    eapply object_is_not_subtype;
      try apply H;eauto with myhints.
    scrush.
    try hammer_hook "JaSubtype" "JaSubtype.subtyping_object_supremum.subgoal_1_1".
    Reconstr.reasy (@subrefl, @object_is_not_subtype) (@JaSyntax.JFProgram).
Qed.

Hint Resolve  subtyping_neq_object subtyping_object_supremum : myhints.

Lemma lookup_cons_neq:
  forall P cn dn ex fields methods m md,
    cn <> dn ->
    methodLookup (JFCDecl cn ex fields methods :: P) dn m = Some md ->
    methodLookup  P dn m = Some md.
Proof.
  scrush.
Qed.

Lemma lookup_in_supertype_subtype_extends:
  forall P cname dname m md,
    names_unique P ->
    extends P cname dname ->
    methodLookup P dname m = Some md ->
    exists md' : JFMethodDeclaration,
      methodLookup P cname m = Some md'.
Proof.
  induction P; intros cname dname m md.
  * scrush.
  * intros Nuq Exts mthLkp.
    unfold methodLookup in mthLkp.
    unfold methodLookup.
    fold methodLookup in *.
    destruct a.
    destruct (JFClassName_dec cname D).
    ** try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.subgoal_1".
       (* Vampire finds a proof which cannot be reconstructed *)
       destruct (find_method methods m).
       *** scrush.
       *** destruct ex.
           + subst.
             try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.subgoal_1_1".
             destruct (JFClassName_dec dname D).
             ++ firstorder.
             ++ try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.subgoal_1_1_1".
                Reconstr.rcrush (@extends_equals_first) (@JaSyntax.methodLookup, @JaSyntax.JFProgram).
           + subst.
             inversion Exts.
             subst.
             try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.subgoal_1_2".
             Reconstr.rcrush (@JaSyntax.methodLookup_find_class, @extends_in_first, @Coq.Init.Datatypes.list_ind, @JaSyntax.methodLookup_raw_neq, @number_of_extends_none, @JaProgram.count_occ_zero_is_class_name_false, @extends_neq_none, @lookup_cons_neq, @JaSyntax.isLSForId_ind, @JaSyntax.methodLookup_prog_monotone_eq, @JaSyntax.methodLookup_raw_empty, @JaSyntax.isLStrue) (@JaSyntax.JFMId_dec, @JaSyntax.isLS, @JaSyntax.JFXId, @JaSyntax.JFACId, @JaSyntax.JFProgram, @JaProgram.names_unique, @Coq.Bool.Bool.bool_dec, @Coq.Lists.List.In, @Coq.Lists.List.map, @Coq.Lists.List.count_occ, @JaSyntax.JFClassName, @JaSyntax.extds_of_cd, @JaSyntax.mthds_of_cd, @JaSyntax.name_of_cd, @JaProgram.decl_once, @JaProgram.is_class_name, @JaSyntax.JFMId, @JaSyntax.find_method, @JaSyntax.methodLookup, @number_of_extends, @JaSyntax.find_class, @JaSyntax.JFObjectName, @JaSyntax.JFClassName_dec).
   ** destruct (JFClassName_dec dname D).
      *** subst. clear -Nuq Exts n.
          try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.subgoal_2".
          (* Vampire finds a proof which cannot be reconstructed *)
          assert (exists (ex0 : option JFClassName) (fields' : list JFFieldDeclaration) (methods' : list JFMethodDeclaration),
                     In (JFCDecl D ex0 fields' methods') P).
          try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.assert_1".
          Reconstr.reasy (@Coq.Init.Datatypes.list_ind, @subtyping_greater_in, @extends_in_second_second, @extends_in_second, @extends_in_first, @base, @JaProgram.count_occ_zero_is_class_name_false, @extends_neq, @extends_neq_none, @JaProgram.in_find_class_raw, @subtyping_ind, @extends_ind, @Coq.Lists.List.in_map_iff) (@JaSyntax.JFObject, @JaSyntax.JFProgram, @JaSyntax.JFClassName, @object_is_not_extended, @extensions_in_all_but_object, @JaProgram.names_unique, @Coq.Bool.Bool.bool_dec, @JaProgram.decl_once, @JaProgram.is_class_name, @JaSyntax.find_class, @Hammer.Reconstr.rdone, @Coq.Lists.List.In, @Coq.Lists.List.map, @Coq.Lists.List.count_occ, @JaSyntax.JFObjectName, @JaSyntax.JFClassName_dec).
          destruct H as [ex0 [fields' [methods' H]]].
          assert (names_unique P).
          try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.assert_2".
          Reconstr.reasy (@JaProgram.names_unique_further) (@JaSyntax.JFProgram).
          unfold names_unique in H0.
          assert (forall x, In x P -> decl_once P x).
          try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.assert_3".
          Reconstr.reasy (@JaProgram.decl_in_head_not_in_tail, @JaProgram.decs_once_monotone, @Coq.Lists.List.in_map_iff, @Coq.Lists.List.count_occ_not_In, @JaProgram.is_class_name_name, @Coq.Lists.List.Forall_forall) (@Coq.Lists.List.In, @JaSyntax.JFProgram, @JaProgram.decl_once, @JaSyntax.JFClassName).
          scrush.
      *** try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.subgoal_3".
          inversion Exts.
           + subst. contradiction.
           + try hammer_hook "JaSubtype" "JaSubtype.lookup_in_supertype_subtype_extends.subgoal_3_1".
             Reconstr.reasy (@JaProgram.names_unique_further) (@JaSyntax.JFProgram).
Qed.

Lemma lookup_in_object_subtype:
  forall P cn m md cd,
    names_unique P ->
    subtype_well_founded P ->
    extensions_in_all_but_object P ->
    methodLookup P JFObjectName m = Some md ->
    find_class P cn = Some cd ->
    exists md' : JFMethodDeclaration, methodLookup P cn m = Some md'.
Proof.
  induction P.
  * intros.
    simpl in H2.
    discriminate H2.
  * intros.
    destruct a.
    destruct (JFClassName_dec JFObjectName D).
    ** subst.
       destruct (JFClassName_dec JFObjectName cn).
       *** subst. firstorder.
       *** assert (program_contains P JFObjectName = true).
           assert (find_class P cn = Some cd)
             by eauto using find_class_further_neq.
           eapply subtype_well_founded_contains_object;eauto 2 with myhints.
           assert (count_occ Bool.bool_dec
                             (map (is_class_name JFObjectName) P) true > 0)
             by eauto using program_contains_counts_occ with myhints.
           apply names_unique_zero in H.
           rewrite H in H5.
           apply Gt.gt_irrefl in H5.
           contradiction.
    ** unfold methodLookup in H2.
       unfold methodLookup.
       fold methodLookup in *.
       destruct (JFClassName_dec JFObjectName D); try contradiction.
       destruct (JFClassName_dec cn D).
       *** subst.
           destruct (find_method methods m).
           + exists j;trivial.
           + destruct ex.
             ++ assert (exists jd : JFClassDeclaration,
                           find_class (JFCDecl D (Some j) fields methods :: P)
                                      j = Some jd).
                {
                  destruct cd.
                  assert (ex = Some j).
                  {
                    simpl in H3.
                    destruct (JFClassName_dec D D);try contradiction.
                    injection H3;intros;intuition.
                  }
                  eapply subtype_get_superclass;try apply H3;eauto 2.
                  subst.
                  apply H3.
                }
                destruct H4.
                apply(IHP j m md x);eauto 2 with myhints.
                destruct (JFClassName_dec D j).
                +++ subst.
                    assert (j<>j) by eauto 2 using subtype_well_founded_neq with myhints.
                    contradiction.
                +++ eauto using find_class_further_neq with myhints.
             ++ unfold extensions_in_all_but_object in H1.
                apply Forall_inv in H1.
                simpl in H1.
                rewrite H1 in *. contradiction.
       *** eapply IHP;eauto 2 with myhints.
           apply (find_class_further_neq P cn D ex fields methods cd);auto.
Qed.


Lemma lookup_in_supertype_subtype:
  forall P C D,
    subtyping P C D ->
    names_unique P ->
    object_is_not_extended P ->
    subtype_well_founded P ->
    extensions_in_all_but_object P ->
    forall cn dn m md cd,
    C = JFClass cn ->
    D = JFClass dn ->
    find_class P cn = Some cd ->
    methodLookup P dn m = Some md ->
    exists md',
      methodLookup P cn m = Some md'.
Proof.
  intros P C D.
  intro.
  induction H.
  * intros.
    subst.
    assert (cn=dn) by congruence.
    subst.
    clear -H6.
    firstorder.
  * intros.
    eapply lookup_in_object_subtype;eauto.
    injection H4;intros.
    rewrite <- H7 in *.
    eauto.
  * intros.
    inversion H3.
  * intros.
    subst.
    injection H7;intros;clear H7;subst.
    destruct (JFClassName_dec dname cn).
    ** subst.
       assert (cn<>cn) by eauto using names_unique_extends_non_refl.
       contradiction.
    ** assert (exists cd, find_class P dname = Some cd).
       assert (exists
                  (ex0 : option JFClassName)
                  (fields' : list JFFieldDeclaration)
                  (methods' : list JFMethodDeclaration),
                  In (JFCDecl dname ex0 fields' methods') P)
         by eauto using extends_in_second.
       do 3 destruct H.
       exists (JFCDecl dname x x0 x1).
       eauto using in_find_class.
       destruct H.
       assert (exists md' : JFMethodDeclaration,
                 methodLookup P dname m = Some md').
       eapply IHsubtyping;try apply H10;
         eauto using lookup_in_supertype_subtype_extends.
       destruct H0.
       eauto using lookup_in_supertype_subtype_extends.
Qed.

(*
Inductive subtyping_wfd : JFProgram -> JFCId -> nat -> Prop :=
| sub_wfd_obj   : forall (P:JFProgram), subtyping_wfd P JFObject 0
| sub_wfd_trans : forall (P:JFProgram) (C:JFCId) (D:JFCId) (n:nat),
                     subtyping_wfd P D n -> extends P C D -> subtyping_wfd P C (n+1).
*)

(* Functions about subtyping.
  Suitable lemmas [subtype_bool_complete] and [subtype_bool_correct] below
*)

(**
   Effective version of the subtyping that returns booleans
   instead predicting the property. The function is correct
   only when the program is well formed.
*)
Fixpoint subtype_class_bool (P:JFProgram) (C D: JFClassName) : bool :=
  if JFClassName_dec C D
  then true
  else if JFClassName_dec D JFObjectName
       then true
       else
         match P with
           | [] => false
           | JFCDecl C' (Some D') _ _ :: P' =>
             if JFClassName_dec C C'
             then if JFClassName_dec D' D
                  then true
                  else subtype_class_bool P' D' D
             else subtype_class_bool P' C D
           | JFCDecl C' None _ _ :: P' =>
             if JFClassName_dec C C'
             then false
             else subtype_class_bool P' C D
         end.



Lemma subtype_class_bool_simple:
  forall P C D fields methods,
    subtype_class_bool (JFCDecl C (Some D) fields methods :: P) C D = true.
Proof.
  intros.
  unfold subtype_class_bool.
  destruct (JFClassName_dec C D).
  * auto.
  * destruct (JFClassName_dec D JFObjectName).
    auto.
    destruct (JFClassName_dec C C).
    - destruct (JFClassName_dec D D).
      + auto.
      + tauto.
    - tauto.
Qed.

Lemma subtype_class_bool_same:
  forall P C,
    subtype_class_bool P C C = true.
Proof.
  intros.
  unfold subtype_class_bool.
  destruct P;destruct (JFClassName_dec C C); auto.
Qed.

Lemma subtype_class_bool_object:
  forall P C,
    subtype_class_bool P C JFObjectName = true.
Proof.
  intros.
  unfold subtype_class_bool.
  destruct P;destruct (JFClassName_dec C JFObjectName); auto.
Qed.

Hint Resolve subtype_class_bool_same subtype_class_bool_object : myhints.

Lemma subtype_class_bool_direct_extends:
  forall P C D flds mthds,
    subtype_class_bool (JFCDecl C (Some D) flds mthds :: P) C D = true.
Proof.
  intros.
  unfold subtype_class_bool.
  destruct (JFClassName_dec C D); try subst C; auto.
  destruct (JFClassName_dec D JFObjectName); try subst D; auto.
  destruct (JFClassName_dec C C); try tauto.
  destruct (JFClassName_dec D D); try tauto.
Qed.

Hint Resolve subtype_class_bool_direct_extends : myhints.


Lemma subtype_class_bool_eq:
  forall P C C' D' flds mthds,
  subtype_class_bool P C' D' = true ->
  subtype_class_bool (JFCDecl C (Some C') flds mthds :: P) C D'=true.
Proof.
  destruct P.
  * unfold subtype_class_bool.
    intros.
    destruct (JFClassName_dec C D'); auto.
    destruct (JFClassName_dec D' JFObjectName); auto.
    destruct (JFClassName_dec C C); auto.
    destruct (JFClassName_dec C' D'); auto.
  * intros.
    unfold subtype_class_bool.
    unfold subtype_class_bool in H.
    destruct (JFClassName_dec C D'); try subst C; auto.
    destruct (JFClassName_dec D' JFObjectName); try subst D'; auto.
    destruct (JFClassName_dec C C); try tauto.
    destruct (JFClassName_dec C' D'); try auto.
Qed.


Hint Resolve subtype_class_bool_eq : myhints.


Lemma subtype_class_bool_neq:
  forall P C D E ex flds mthds,
    subtype_class_bool P C D = true ->
    C<>E ->
    subtype_class_bool (JFCDecl E ex flds mthds :: P) C D = true.
Proof.
  destruct P.
  - intros.
    simpl in H.
    simpl.
    destruct (JFClassName_dec C D); eauto 2.
    destruct (JFClassName_dec D JFObjectName); eauto 2.
    discriminate H.
  - intros.
    destruct (JFClassName_dec C D); try rewrite e; eauto 2 with myhints.
    destruct (JFClassName_dec D JFObjectName); try rewrite e; eauto 2 with myhints.
    destruct ex.
    + unfold subtype_class_bool.
      unfold subtype_class_bool in H.
      destruct (JFClassName_dec C D); try rewrite e; eauto 2 with myhints.
      destruct (JFClassName_dec D JFObjectName); try rewrite e; eauto 2 with myhints.
      destruct (JFClassName_dec C E); eauto 3 with myhints.
    + unfold subtype_class_bool.
      unfold subtype_class_bool in H.
      destruct (JFClassName_dec C D); try rewrite e; eauto 2 with myhints.
      destruct (JFClassName_dec D JFObjectName); try rewrite e; eauto 2 with myhints.
      destruct (JFClassName_dec C E); eauto 3 with myhints.
Qed.

Hint Resolve subtype_class_bool_neq : myhints.

Lemma names_unique_count_class_name:
  forall P C1 x x0 x1,
    names_unique P ->
    count_occ Bool.bool_dec (map (is_class_name C1) P)
              true = 0 ->
    count_occ JFClassDeclaration_dec P (JFCDecl C1 x x0 x1) = 0.
Proof.
  induction P.
  - intros; simpl; auto.
  - intros.
    rewrite map_cons in H0.
    destruct (Bool.bool_dec (is_class_name C1 a) true).
    + rewrite count_occ_cons_eq in H0; auto.
      discriminate H0.
    + rewrite count_occ_cons_neq.
      eapply IHP.
      eauto using names_unique_further.
      rewrite count_occ_cons_neq in H0; auto.
      destruct a.
      assert (is_class_name C1 (JFCDecl D ex fields methods) = false).
      simpl in n.
      destruct (JFClassName_dec D C1).
      tauto.
      simpl. destruct (JFClassName_dec D C1); tauto.
      apply is_class_name_nequal in H1.
      congruence.
Qed.



Lemma extends_subtype_bool_complete:
  forall P C D cl,
    names_unique P ->
    program_contains P JFObjectName = true ->
    object_is_not_extended P ->
    subtype_well_founded P ->
    JFClass C <> JFObject ->
    find_class P C = Some cl ->
    extends P C D ->
    subtype_class_bool P C D = true.
Proof.
  induction P.
  - intros. unfold find_class in H4.
    discriminate H4.
  - intros. inversion H5.
    + eauto with myhints.
    + assert (  exists
                 (ex0 : JFClassName) (fields' : list JFFieldDeclaration)
                 (methods' : list JFMethodDeclaration),
                 In (JFCDecl C (Some ex0) fields' methods') P) by eauto using extends_in_first.
      destruct H11, H11, H11.
      rewrite <- H6 in *.
      assert (C1<>C) by eauto 2 with myhints.
      eapply subtype_class_bool_neq.
      eapply IHP; eauto 3 with myhints.
      assert (find_class P C = Some cl)
        by eauto 2 using find_class_further_neq with myhints.
      eapply subtype_well_founded_contains_object;eauto 3 with myhints.
      auto.
Qed.

Lemma decompose_subtype_class_bool:
  forall P Cid Did D1 j fields methods,
    (Cid = D1 -> subtype_class_bool P j Did = true) ->
    (Cid <> D1 -> subtype_class_bool P Cid Did = true) ->
    subtype_class_bool (JFCDecl D1 (Some j) fields methods :: P) Cid Did = true.
Proof.
  intros.
  simpl.
  destruct (JFClassName_dec Cid Did); eauto 2.
  destruct (JFClassName_dec Did JFObjectName); eauto 2.
  destruct (JFClassName_dec Cid D1).
  - destruct (JFClassName_dec j Did).
    * auto.
    * auto.
  - apply H0.
    auto.
Qed.

Lemma decompose_subtype_class_bool_none:
  forall P Cid Did D1 fields methods,
    Cid <> D1 ->
    subtype_class_bool P Cid Did = true ->
    subtype_class_bool (JFCDecl D1 None fields methods :: P) Cid Did = true.
Proof.
  intros.
  simpl.
  destruct (JFClassName_dec Cid Did); eauto 2.
  destruct (JFClassName_dec Did JFObjectName); eauto 2.
  destruct (JFClassName_dec Cid D1).
  + congruence.
  + auto.
Qed.

Hint Resolve subtype_class_bool_simple decompose_subtype_class_bool
     extends_subtype_bool_complete decompose_subtype_class_bool_none : myhints.


Lemma names_unique_extends_eq:
  forall P D1 j fields methods dname,
    names_unique (JFCDecl D1 (Some j) fields methods :: P) ->
    extends (JFCDecl D1 (Some j) fields methods :: P) D1 dname ->
    j = dname.
Proof.
  intros.
  inversion H0.
  - auto.
  - assert  (exists
                (ex0 : JFClassName) (fields' : list JFFieldDeclaration)
                (methods' : list JFMethodDeclaration),
                In (JFCDecl D1 (Some ex0) fields' methods') P)
      by eauto using extends_in_first.
    destruct H9. destruct H9. destruct H9.
    assert (count_occ Bool.bool_dec (map (is_class_name D1) P) true = 0)
      by eauto using names_unique_count_zero.
    apply <- count_occ_not_In in H10.
    assert False.
    replace true with (is_class_name D1 (JFCDecl D1 (Some x) x0 x1)) in H10.
    apply H10.
    apply in_map.
    auto.
    apply is_class_name_name.
    tauto.
Qed.

Hint Resolve names_unique_count_zero names_unique_extends_eq : myhints.

Lemma subtype_class_bool_complete :
  forall P C D,
    names_unique P ->
    program_contains P JFObjectName = true ->
    object_is_not_extended P ->
    subtype_well_founded P ->
    subtyping P C D  ->
    forall  Cid Did cl,
    C = (JFClass Cid) ->
    D = (JFClass Did) ->
    JFClass Cid <> JFObject ->
    find_class P Cid = Some cl ->
    Cid <> Did ->
    subtype_class_bool P Cid Did = true.
Proof.
  induction P; intros.
  + simpl in H7.
    discriminate H7.
  +  inversion H3.
     - congruence.
     - assert (Did = JFObjectName).
       rewrite <- H11 in *.
       unfold JFObject in H5.
       congruence.
       rewrite H12.
       eauto with myhints.
     - rewrite H4 in *.
       discriminate H10.
     - destruct a.
       { destruct ex.
         + apply decompose_subtype_class_bool.
           intros.
           assert (cname = D1) by congruence.
           rewrite <- H17 in *.
           assert (Cid <> JFObjectName). {
             intro.
             rewrite H18 in H6.
             auto.
           }
           assert (j=dname) by eauto with myhints.
           subst j.
           destruct (JFClassName_dec dname Did); try rewrite e; eauto 2 with myhints.
           assert (exists CC : JFClassDeclaration,
                      find_class (JFCDecl cname (Some dname) fields methods :: P) dname = Some CC). {
             eapply subtype_get_superclass; eauto 2 with myhints.
             assert (find_class (JFCDecl cname (Some dname) fields methods :: P) cname =
                     Some (JFCDecl cname (Some dname) fields methods)) by eauto using find_class_eq with myhints.
             apply H19.
           }
           destruct H19.
           assert (subtyping P D0 D). {
             destruct (JFCId_dec D0 D); try rewrite e; eauto 2 with myhints.
             eapply subtyping_further_neq;eauto 2 with myhints.
             eapply extends_neq;eauto with myhints.
           }
           eapply IHP;eauto 2 with myhints. (* subtype_class_bool P j Did = true *)
           - rewrite H9 in H4. injection H4;intros.
             eauto 3 using program_contains_further_neq with myhints.
           - subst.
             eapply (subtyping_neq_object (JFCDecl D1 (Some dname) fields methods :: P) dname (JFClass Did)).
             * apply H1.
             * congruence.
             * auto with myhints.
           - assert (JFClass dname <> JFClass cname). {
               eapply extends_neq.
               apply H.
               exists cname, dname.
               intuition.
             }
             eapply find_class_further_neq.
             assert (cname<>dname) by congruence.
             apply H22.
             eauto 1 with myhints.
           - intros.
             { destruct (JFClassName_dec Cid Did); eauto 3 with myhints.
               destruct (JFClassName_dec Did JFObjectName); try rewrite e; eauto 2 with myhints.
               assert (exists CC : JFClassDeclaration, find_class P Cid = Some CC). {
                 eapply (subtyping_find_class P C D Cid);eauto 2 with myhints.
                 congruence.
                 unfold JFObject. congruence.
                 eapply subtyping_further_neq.
                 apply H3.
                 eauto 2 with myhints.
                 eauto 2 with myhints.
                 congruence.
               }
               destruct H17.
               assert (subtyping P C D). {
                   eapply (subtyping_further_neq).
                   apply H3.
                   auto with myhints.
                   auto with myhints.
                   congruence.
                 }
               eapply IHP; try apply H18; eauto 2 with myhints.
               - eapply program_contains_further_neq.
                 * assert (D1<>JFObjectName) by eauto 2 with myhints.
                   apply H19.
                 * apply H0.
             }
        + assert (Cid=cname) by congruence.
          subst Cid.
          assert (D1<>cname) by
              (eapply (extends_neq_none P D1 cname dname fields methods); eauto with myhints).
          apply decompose_subtype_class_bool_none.
          auto with myhints.
          subst.
          assert (subtyping P (JFClass cname) (JFClass Did)). {
            eapply subtyping_further_neq.
            apply H3.
            auto with myhints.
            eauto with myhints.
            congruence.
          }
          eapply IHP; try apply H4;eauto 2 with myhints.
           - eapply subtype_well_founded_contains_object;eauto 2 with myhints.
             assert (find_class P cname = Some cl) by
                 eauto 2 using find_class_further_neq with myhints.
             apply H5.
           - eauto 2 using find_class_further_neq with myhints.
       }
Qed.

Lemma subtype_class_bool_find_class:
  forall name name0,
    name <> name0 ->
    name0 <> JFObjectName ->
    forall P,
    subtype_class_bool P name name0 = true ->
    exists cl, find_class P name = Some cl.
Proof.
  induction P;intros.
  + simpl in H1.
    destruct (JFClassName_dec name name0).
    congruence.
    destruct (JFClassName_dec name0 JFObjectName).
    congruence.
    discriminate H1.
  + destruct a.
    destruct (JFClassName_dec D name).
    * subst D.
      exists (JFCDecl name ex fields methods).
      eapply find_class_eq.
    * unfold subtype_class_bool in H1.
      destruct (JFClassName_dec name name0).
      - subst name0.
        tauto.
      - destruct (JFClassName_dec name0 JFObjectName).
        { subst name0.
          lapply IHP; intros.
          destruct H2.
          exists x.
          eapply find_class_same; eauto.
          eauto.
        }
        { destruct ex.
          + destruct (JFClassName_dec name D).
            * congruence.
            * lapply IHP; eauto.
              intros.
              destruct H2.
              exists x.
              clear H1.
              eauto using find_class_same.
          + fold (subtype_class_bool P name name0) in H1.
            lapply IHP; eauto 2; intros.
            ++ destruct H2.
               exists x.
               clear H1.
               eauto using find_class_same.
            ++ destruct (JFClassName_dec name D); eauto.
        }
Qed.


(** This is the `lifting' of the class subtyping to subtyping on class
    identifiers.
 *)
Definition subtype_bool (P:JFProgram) (Cid Did: JFCId) : bool :=
  match Cid, Did with
  | JFBotClass, _ => true
  | _, JFBotClass => false
  | JFClass C, JFClass D => subtype_class_bool P C D
  end.


Inductive leqAnnLS : JFProgram -> JFCId -> JFMId -> JFAMod -> JFAMod -> Prop:=
| isLSTrueAnn : forall (P:JFProgram) (C:JFCId) (cname:JFClassName) (m:JFMId) (ra:JFAMod) (rb:JFAMod),
    C = JFClass cname ->
    isLSForId P cname m ->
    leqAnn ra rb ->
    leqAnnLS P C m ra rb
| isLSFalseAnn : forall (P:JFProgram) (C:JFCId) (cname:JFClassName) (m:JFMId) (ra:JFAMod) (rb:JFAMod),
    C = JFClass cname ->
    ~ isLSForId P cname m ->
    leqAnnLS P C m ra rb.
(* TODO: zastąpić C przez cname *)


(**
   We have two related orders on JFACIds that depend on whether the method
   local sensitive or not local sensitive. It is defined as
   <:^{\isLocalSensitive(C,m)} in Section~{sec:type-system}.
*)
Inductive leqIsLS : JFProgram -> JFCId -> JFMId -> JFACId -> JFACId -> Prop :=
| isLSTrue : forall (P:JFProgram) (Cid:JFCId) (cname:JFClassName)
                    (mid:JFMId) (ls:JFACId) (lc:JFCId) (la:JFAMod) (rs:JFACId) (rc:JFCId) (ra:JFAMod),
    Cid = JFClass cname ->
    isLSForId P cname mid ->
    ls = (lc, la) ->
    rs = (rc, ra) ->
    subtyping P lc rc ->
    leqAnn la ra ->
    leqIsLS P Cid mid ls rs
| isLSFalse : forall (P:JFProgram) (Cid:JFCId) (cname:JFClassName)
                    (mid:JFMId) (ls:JFACId) (lc:JFCId) (la:JFAMod) (rs:JFACId) (rc:JFCId) (ra:JFAMod),
    Cid = JFClass cname ->
    ~ isLSForId P cname mid ->
    ls = (lc, la) ->
    rs = (rc, ra) ->
    subtyping P lc rc ->
    leqIsLS P Cid mid ls rs.

Lemma leqIsLS_refl:
  forall P Cid cname cdecl mid ls,
    Cid = JFClass cname ->
    find_class P cname = Some cdecl ->
    leqIsLS P Cid mid ls ls.
Proof.
  intros.
  assert (isLSForId P cname mid \/ ~isLSForId P cname mid) by auto with myhints.
  destruct ls.
  destruct H1.
  + eapply isLSTrue;eauto with myhints.
  + eapply isLSFalse;eauto with myhints.
Qed.

Lemma leqIsLS_trans:
  forall P Cid cname cdecl mid mu mu' mu'',
    (program_contains P JFObjectName) = true ->
    names_unique P ->
    object_is_not_extended P ->
    extensions_in_all_but_object P ->
    Cid = JFClass cname ->
    find_class P cname = Some cdecl ->
    leqIsLS P Cid mid mu mu' ->
    leqIsLS P Cid mid mu' mu'' ->
    leqIsLS P Cid mid mu mu''.
Proof.
  intros P Cid cname cdecl mid mu mu' mu''.
  intros Pctns Nuq Oine Einabo Cideq Fcls LeqISLSmumu' LeqISLSmu'mu''.
  assert (isLSForId P cname mid \/ ~isLSForId P cname mid)
    as IsLSDec by auto with myhints.
  destruct mu as [C md].
  destruct mu'' as [C'' md''].
  destruct LeqISLSmumu' as [P cname0 mid ls lc la rs rc ra
                              Cideq' IsLSForcname0 lseq rseq Sub LeqAnn|
                            P' cid cname0 mid ls lc la rs rc ra
                               Cideq'
                               IsLSForcname0 lseq rseq Sub].
  + subst.
    injection IsLSForcname0;intros;clear IsLSForcname0;subst.
    eapply isLSTrue;try apply Cideq;auto;
    try (inversion LeqISLSmu'mu'' as [P' Cid cname mid0 ls0 lc la0 rs0 rc ra0
                                       Mideq IsLSForIdcname raeq C''eq Sub'
                                       LeqAnn'|
                                    P' Cid cname mid0 ls0 lc la0 rs0 rc ra0
                                       Mideq IsLSForIdcname raeq C''eq Sub'];
         (subst;
          injection Mideq;intros;clear Mideq;
          injection raeq;intros;clear raeq;
          injection C''eq;intros;clear C''eq;
          subst;
          subst)).
    ++ eauto using subtrans.
    ++ eauto using subtrans.
    ++ eauto using leqAnn_trans.
    ++ contradiction.
  + subst.
    injection Cideq';intros;clear Cideq';subst.
    eapply isLSFalse;try apply IsLSForcname0;auto.
    inversion LeqISLSmu'mu'' as [P'' Cid cname mid0 ls0 lc' la0 rs0 rc' ra0
                                    Mideq IsLSForIdcname raeq C''eq Sub'
                                    LeqAnn'|
                                 P'' Cid cname mid0 ls0 l'c la0 rs0 rc' ra0
                                    Mideq IsLSForIdcname raeq C''eq Sub'];
    (subst;
         injection Mideq;intros;clear Mideq;
           injection raeq;intros;clear raeq;
            injection C''eq;intros;clear C''eq;
              subst;
       eauto using subtrans).
Qed.

Lemma minimalIsLS:
  forall P m cls amod cname md,
(*    find_class P cname = Some cdecl -> *)
(*    cdecl = JFCDecl cname ex flds mthds -> *)
    methodLookup P cname m = Some md ->
    leqIsLS P (JFClass cname) m (JFBotClass,  JFrwr) (cls, amod).
Proof.
  intros.
  edestruct (isLSForId_dec P cname m).
  * inversion H0.
    eapply isLSTrue; eauto with myhints.
  * eapply isLSFalse; eauto with myhints.
Qed.

Hint Resolve minimalIsLS leqIsLS_refl leqIsLS_trans : myhints.

(**
   Lifting of an inequality predicate that compares using a given parameter predicate P an element
   of JFACId with a list of JFACId's. It holds true when at least one comparison holds.
*)
Inductive isLeqIn : (JFACId -> JFACId -> Prop) -> JFACId -> list JFACId -> Prop :=
  | consNotIn : forall  (P:JFACId -> JFACId -> Prop) (caid:JFACId) (daid:JFACId) (l:list JFACId),
      ~P caid daid ->
      isLeqIn P caid l ->
      isLeqIn P caid (daid :: l)
  | consIsIn : forall  (P:JFACId -> JFACId -> Prop) (caid:JFACId) (daid:JFACId) (l:list JFACId),
      P caid daid ->
      isLeqIn P caid (daid :: l).

(**
   Lifting of an inequality predicate that compares using a given parameter predicate P a list
   of JFACId's with a list of JFACId's. It holds true when at least one comparison holds.
*)
Inductive isLeqIncluded : (JFACId -> JFACId -> Prop) -> list JFACId -> list JFACId -> Prop :=
  | emptyFirst : forall  (P:JFACId -> JFACId -> Prop) (l2:list JFACId),
      isLeqIncluded P [] l2
  | consFirst : forall  (P:JFACId -> JFACId -> Prop) (caid:JFACId) (l1:list JFACId) (l2:list JFACId),
      isLeqIn P caid l2 ->
      isLeqIncluded P (caid :: l1) l2.

Definition leqACId (P:JFProgram) (C D:JFACId) : Prop :=
  let (Cc,Can) := C in
  let (Dc,Dan) := D in
  subtyping P Cc Dc /\ leqAnn Can Dan.

Lemma leqACId_refl:
  forall (P:JFProgram) (C:JFACId),
    leqACId P C C.
Proof.
  intros.
  unfold leqACId.
  destruct C.
  auto with myhints.
Qed.

Lemma leqACId_trans:
  forall (P:JFProgram) (C D E:JFACId),
    (program_contains P JFObjectName) = true ->
    names_unique P ->
    object_is_not_extended P ->
    extensions_in_all_but_object P ->
    leqACId P C D -> leqACId P D E -> leqACId P C E.
Proof.
  intros P C D E Pcont Nu Onex extns lCD lDE.
  unfold leqACId in *.
  destruct C.
  destruct D.
  destruct E.
  intuition.
  +
    inversion H.
    ++ rewrite H5 in *.
      eapply subtrans;eauto with myhints.
    ++ rewrite <- H5 in *.
       eauto with myhints.
    ++ rewrite <- H5 in *.
       eauto with myhints.
    ++ eapply subtrans;eauto with myhints.
  + eauto with myhints.
Qed.

Hint Resolve leqACId_refl leqACId_trans : myhints.

Fixpoint infClass_aux (P:JFProgram) (Cn Dn: JFClassName) (n:nat) {struct n} :=
  match n with
  | 0 => None
  | S n0 => if subtype_class_bool P Cn Dn
            then Some Dn
            else if subtype_class_bool P Dn Cn
                 then Some Cn
                 else match find_class P Cn with
                      | None => None
                      | Some (JFCDecl _ None _ _) => Some JFObjectName
                      | Some (JFCDecl _ (Some cn) _ _) =>
                        infClass_aux P cn Dn n0
                      end
  end.


(** The lower bound operation for the lattice of class types. *)
Definition infClass (P:JFProgram) (Cid Did:JFCId) :=
  match Cid with
  | JFClass cn => match Did with
                  | JFClass dn => match (number_of_extends P cn) with
                                  | None => None
                                  | Some n =>
                                    match infClass_aux P cn dn n with
                                    | Some rn => Some (JFClass rn)
                                    | None => None
                                    end
                                  end
                  | JFBotClass => Some JFBotClass
                  end
  | JFBotClass => Some JFBotClass
  end.

Definition infACId (P:JFProgram) (acida acidb:JFACId) :=
  let (tpa,ana) := acida in
  let (tpb,anb) := acidb in
  match infClass P tpa tpb with
  | None => None
  | Some tpr => Some (tpr, infAnn ana anb)
  end.

End JaSubtype.

Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Lists.List.
Import ListNotations.

Require Import Coq.Structures.Equalities.
Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Module Jafun.

Import JaSyntax.
Import JaProgram.
Import JaSubtype.
Import JaTactics.

(* TODO: initial hierarchy of classes *)

(*
Error: Cannot guess decreasing argument of fix.
*)
(**
   Calculates the list of fields in an object of the given class name
   [cname] traversing recursively its subtyping hierarchy up to _Object_.
   The parameter [n] is added to ensure the correcntess of
   structural recursion. The parameter [res] contains the triples
   of fields collected so far in possibly earlier computation.

   The function returns [Some] value in case its calculation is
   correct. In case the calculation is not correct (when
   - the structural induction parameter is too small,
   - there is a non _Object_ class, which is not extended,
   - there is no class of the given name in the program),
   the function returns [None].
 *)
Fixpoint flds_aux (CC:JFProgram) cname n res {struct n} : option (list (bool * JFCId * JFXId)) :=
  let cls := find_class CC cname in
  match cls with
  | None => None
  | Some l =>
    let fr := get_fields_raw l in
    match l with
    | JFCDecl _ None _ _ => Some (res ++ fr)
    | JFCDecl _ (Some ex) _ _ =>
      match n with
      | 0 => None
      | S k => flds_aux CC ex k (res ++ fr)
      end
    end
  end.





Lemma flds_aux_not_object_not_find_class:
  forall P cname n fds,
    find_class P cname = None ->
    cname <> JFObjectName ->
    flds_aux P cname n fds = None.
Proof.
  destruct n.
  * intros. simpl.
    rewrite H.
    auto.
  * intros. simpl.
    rewrite H.
    auto.
Qed.

Lemma flds_aux_not_object_find_class_ex_zero:
  forall P cname dname fields methods fds,
    find_class P cname = Some (JFCDecl cname (Some dname) fields methods) ->
    flds_aux P cname 0 fds = None.
Proof.
  intros.
  simpl.
  rewrite H.
  auto.
Qed.

Lemma flds_aux_not_object_in_first_none:
  forall P n cname fields methods fds,
    exists flds',
    flds_aux ((JFCDecl cname None fields methods) :: P) cname n fds = Some flds'.
Proof.
  intros.
  destruct n.
  + simpl.
    destruct_eq.
    eexists.
    auto.
  + simpl.
    destruct_eq.
    eexists.
    auto.
Qed.


Lemma flds_aux_nil:
    forall n P name fds,
      flds_aux P name n fds = Some [] ->
      fds = [].
Proof.
  induction n.
  * intros.
    simpl in H.
    destruct (find_class P name).
    ** destruct j.
       destruct ex.
       *** discriminate H.
       *** injection H;intros.
           assert ( fds = [] /\ map
                           (fun field : JFFieldDeclaration =>
                              match field with
                              | JFFDecl phi C x => (phi, C, x)
                              end) fields = []).
           eapply app_eq_nil.
           auto.
           intuition.
    ** discriminate H.
  * intros.
    simpl in H.
    destruct (find_class P name).
    ** destruct j.
       destruct ex.
       + assert (fds ++ (get_fields_raw (JFCDecl D (Some j) fields methods))
                 = []).
         eapply IHn.
         apply H.
         assert (fds = [] /\ (get_fields_raw (JFCDecl D (Some j) fields methods)) = []).
         eapply app_eq_nil.
         auto.
         intuition.
       + injection H;intros.
         assert (fds  = [] /\ map
                       (fun field : JFFieldDeclaration =>
                          match field with
                          | JFFDecl phi C x => (phi, C, x)
                          end) fields = []).
         eapply app_eq_nil.
         auto.
         intuition.
    ** discriminate H.
Qed.

Lemma flds_monotone_n_Sn:
  forall P n dname fd fds,
         flds_aux P dname n fd = Some fds ->
         flds_aux P dname (S n) fd = Some fds.
Proof.
  induction n.
  + intros.
    simpl in H.
    simpl.
    destruct (find_class P dname); try discriminate H.
    destruct j.
    destruct ex; try discriminate H.
    auto.
  + intros.
    unfold flds_aux.
    fold flds_aux.
    simpl in H.
    destruct (find_class P dname); try discriminate H.
    destruct j.
    destruct ex; try discriminate H.
    assert (flds_aux P j (S n) (fd ++ get_fields_raw (JFCDecl D (Some j) fields methods)) = Some fds).
    auto.
    Opaque get_fields_raw.
    simpl in H0.
    auto.
    auto.
Qed.

Lemma flds_monotone_n:
  forall P n m dname fd fds,
    flds_aux P dname n fd = Some fds ->
    m > n ->
    flds_aux P dname m fd = Some fds.
Proof.
  induction m.
  + intros.
    assert (n >=0) by auto with zarith.
    assert (0 > 0) by auto with zarith.
    assert (0<>0) by auto with zarith.
    contradiction.
  + intros.
    apply flds_monotone_n_Sn.
    assert (m > n \/ n=m) by auto using gt_S.
    destruct H1.
    ++ apply IHm; auto.
    ++ rewrite <- H1.
       auto.
Qed.


Lemma flds_monotone_P:
  forall P n dname cname ex flds mths fd fds,
    flds_aux P dname n fd = Some fds ->
    cname <> dname ->
    names_unique (JFCDecl cname ex flds mths :: P) ->
    subtype_well_founded ((JFCDecl cname ex flds mths) :: P) ->
    flds_aux (JFCDecl cname ex flds mths :: P) dname n fd = Some fds.
Proof.
  induction n.
  + intros.
    simpl.
    simpl in H.
    destruct (JFClassName_dec cname dname); try contradiction.
    auto.
  + intros.
    simpl.
    simpl in H.
    destruct (JFClassName_dec cname dname); try contradiction.
    destruct (find_class P dname) eqn:?;try discriminate H.
    destruct j.
    destruct ex0; try discriminate H.
    assert (cname <> j). {
      assert (exists CC,find_class P j = Some CC) by eauto 4 using subtype_get_superclass with myhints.
      destruct H3.
      destruct x.
      assert (j=D0) by eauto 2 using find_class_eq_name with myhints.
      subst D0.
      eauto 3 using names_unique_in_neq with myhints.
    }
    apply IHn;auto with myhints.
    auto with myhints.
Qed.

Lemma flds_aux_decompose_program_neq:
  forall n fds fd P cname dname x fields methods,
    names_unique ((JFCDecl cname x fields methods) :: P) ->
    subtype_well_founded ((JFCDecl cname x fields methods) :: P) ->
    flds_aux ((JFCDecl cname x fields methods) :: P) dname n fd = Some fds ->
    cname <> dname ->
    flds_aux P dname n fd = Some fds.
Proof.
  induction n.
  * intros fds fd P cname dname x fields methods.
    intros Nuq SbWfd FldsAux cneq.
    simpl in FldsAux.
    simpl.
    destruct (JFClassName_dec cname dname);try contradiction.
    destruct (find_class P dname); try discriminate FldsAux.
    destruct j.
    destruct ex;try discriminate FldsAux.
    auto.
  * intros fds fd P cname dname x fields methods.
    intros Nuq SbWfd FldsAux Neq.
    simpl; simpl in FldsAux.
    destruct (JFClassName_dec cname dname);try contradiction.
    destruct (find_class P dname) eqn:?; try discriminate FldsAux.
    destruct j.
    destruct ex;auto.
    assert (cname <>j). {
         assert (exists CC : JFClassDeclaration, find_class P j = Some CC) by eauto 4 using subtype_get_superclass with myhints.
         destruct H.
         destruct x0.
         erewrite <- (find_class_eq_name P j D0) in H.
         assert (In (JFCDecl j ex fields1 methods1) P) by eauto 2 using find_class_in with myhints.
         eauto 2 using names_unique_in_neq with myhints.
         eauto 1 with myhints.
       }
    eapply IHn;eauto 1.
Qed.

Lemma flds_aux_decompose_acc:
  forall n fds fd P name,
    flds_aux P name n fd = Some fds ->
    exists fds',
      fds = fd ++ fds'.
Proof.
  induction n.
  * intros.
    simpl in H.
    destruct (find_class P name).
    ** destruct j.
       destruct ex.
       *** discriminate H.
       *** injection H;intros.
           rewrite <- H0.
           eexists;auto.
    ** discriminate H.
  * intros.
    simpl in H.
    destruct (find_class P name).
    ** destruct j.
       destruct ex.
       *** assert ( exists fds' : list (bool * JFCId * JFXId), fds =
                            (fd ++ get_fields_raw (JFCDecl D (Some j) fields methods)) ++ fds').
           {
             eapply IHn.
             apply H. }
           destruct H0.
           rewrite H0.
           eexists.
           auto using app_assoc.
       *** injection H;intros.
           rewrite <- H0.
           eexists. auto.
    ** discriminate H.
Qed.

Lemma flds_aux_decompose_second_same:
  forall n fd1 fd2 fd1' fd' P name,
    flds_aux P name n (fd1 ++ fd1') = Some (fd1 ++ fd1' ++ fd') ->
    flds_aux P name n (fd2 ++ fd1') = Some (fd2 ++ fd1' ++ fd').
Proof.
  induction n.
  * simpl.
    intros.
    destruct (find_class P name); try discriminate H.
    destruct j.
    destruct ex;try discriminate H.
    injection H;intros.
    rewrite app_assoc in H0.
    apply app_inv_head in H0.
    rewrite H0.
    rewrite app_assoc.
    auto.
  * simpl.
    intros.
    destruct (find_class P name); try discriminate H.
    destruct j.
    destruct ex;try discriminate H.
    **  rewrite <- 1 app_assoc in H.
        assert (exists ff, fd1 ++ fd1' ++ fd' = (fd1 ++ fd1' ++ (get_fields_raw (JFCDecl D (Some j) fields methods))) ++ ff)
          by eauto 2 using flds_aux_decompose_acc.
        destruct H0.
        rewrite <- 2 app_assoc in H0.
        apply app_inv_head in H0.
        apply app_inv_head in H0.
        rewrite <- app_assoc.
        assert (flds_aux P j n (fd2 ++ fd1' ++ get_fields_raw (JFCDecl D (Some j) fields methods)) =
               Some (fd2 ++ (fd1'  ++ get_fields_raw (JFCDecl D (Some j) fields methods)) ++ x)). {
         eapply IHn.
         rewrite H.
         rewrite H0.
         repeat rewrite app_assoc.
         auto 1.
        }
        rewrite H1.
        rewrite H0.
        repeat rewrite app_assoc.
        auto 1.
    ** injection H. intros.
       rewrite <- app_assoc in H0.
       apply app_inv_head in H0.
       apply app_inv_head in H0.
       rewrite H0.
       rewrite app_assoc.
       congruence.
Qed.

Lemma flds_aux_decompose_first_same:
  forall (n : nat) (fd1 fd1' fd2' fd' : list (bool * JFCId * JFXId)) (P : JFProgram) (name : JFClassName),
    flds_aux P name n (fd1 ++ fd1') = Some (fd1 ++ fd1' ++ fd') ->
    flds_aux P name n (fd1 ++ fd2') = Some (fd1 ++ fd2' ++ fd').
Proof.
  intros.
  rewrite app_assoc in H.
  replace (fd1 ++ fd1') with ((fd1 ++ fd1') ++ []) in H by
      (rewrite <- app_assoc;rewrite app_nil_r;auto).
  replace (((fd1 ++ fd1') ++ []) ++ fd') with ((fd1 ++ fd1') ++ [] ++ fd') in H
    by (rewrite app_assoc;rewrite app_nil_r;auto).
  eapply flds_aux_decompose_second_same in H.
  rewrite app_nil_r in H.
  rewrite H.
  repeat rewrite app_assoc.
  rewrite app_nil_r.
  auto 1.
Qed.

Lemma flds_aux_flds_aux:
  forall n P dname' fds x7 x7',
    flds_aux P dname' n x7 = Some fds ->
    (exists fds',
        flds_aux P dname' n x7' = Some fds').
Proof.
  induction n.
  * intros.
    simpl.
    simpl in H.
    destruct (find_class P dname').
    ** destruct j.
       destruct ex.
       *** discriminate H.
       *** eexists. auto 1.
    ** discriminate H.
  * intros.
    simpl.
    simpl in H.
    destruct (find_class P dname').
    ** destruct j.
       destruct ex.
       *** eapply IHn.
           apply H.
       *** eexists. auto 1.
    ** discriminate H.
Qed.

Lemma flds_aux_extends:
  forall P n,
  forall cname dname fl fl',
    extends P cname dname ->
    flds_aux P dname n fl = Some (fl ++ fl') ->
    names_unique P ->
    subtype_well_founded P ->
    extensions_in_all_but_object P ->
    exists flds',
      flds_aux P cname (n+1) fl = Some (fl ++ flds' ++ fl').
Proof.
  Opaque get_fields_raw.
  induction n.
  + induction 1.
    ++ intros Flds Nuq Swf Eiabo.
       replace (0 + 1) with (S 0) by auto 1 with zarith.
       simpl.
       simpl in Flds.
       destruct_eq.
       assert (C<>D) by eauto 2 using names_unique_in_neq.
       destruct (JFClassName_dec C D); try contradiction.
       destruct (find_class tl D); try discriminate Flds.
       destruct j.
       destruct ex0;  try discriminate Flds.
       injection Flds;intros.
       apply app_inv_head in H1.
       rewrite H1.
       eexists. rewrite app_assoc.
       auto 1.
    ++ intros Flds Nuq Swf Eiabo.
       assert (C1 <> D2).  {
         assert (exists (ex0 : option JFClassName)
                        (fields' : list JFFieldDeclaration)
                        (methods' : list JFMethodDeclaration),
                    In (JFCDecl D2 ex0 fields' methods') tl) by eauto using extends_in_second.
         destruct H0 as [ex0 [fields' [methods']]].
         eauto 2 using names_unique_in_neq.
       }
       assert (flds_aux tl D2 0 fl = Some (fl ++ fl')) by eauto using
                                                                flds_aux_decompose_program_neq with myhints.
       assert (exists flds' : list (bool * JFCId * JFXId), flds_aux tl C2 (0 + 1) fl = Some (fl ++ flds' ++ fl'))
         by eauto 5 with myhints.
       destruct H2 as [flds'].
       eexists.
       assert (exists (fields' : list JFFieldDeclaration)
                      (methods' : list JFMethodDeclaration),
                  In (JFCDecl C2 (Some D2) fields' methods') tl) by eauto 2 using extends_in_first.
       destruct H3 as [fields' [methods']].
       apply flds_monotone_P; eauto 2 with myhints.
  + intros cname dname fl fl' Ext Flds Nuq Swf Eiabo.
    replace (S n + 1) with (S (n + 1)) by auto 1 with zarith.
    simpl in Flds.
    destruct (find_class P dname) eqn:?;try discriminate Flds.
    destruct j.
    assert (dname = D) by eauto using find_class_eq_name.
    subst D.

    generalize Ext;intro.
    apply extends_in_first in Ext0.
    destruct Ext0 as [fields' [methods']].
    apply in_find_class in H;eauto 1.

    destruct ex; try discriminate Flds.
    ++ generalize Flds; intro.
       apply flds_aux_decompose_acc in Flds0.
       destruct Flds0.
       rewrite <- app_assoc in H0.
       apply app_inv_head in H0.
       generalize Heqo;intro.
       eapply subtype_get_superclass in Heqo0;eauto 1.
       assert (exists CC, find_class P j = Some CC) by eauto using subtype_get_superclass.
       destruct H1.

       assert (extends P dname j). {
         eapply find_class_extends; eauto 2.
         assert (exists P0 P1 : list JFClassDeclaration, P = P0 ++ (JFCDecl dname (Some j) fields methods) :: P1) by
               eauto 2 using find_class_decompose_program.
           destruct H2 as [P0 [P1]].
           assert (exists CC, find_class (JFCDecl dname (Some j) fields methods :: P1) j = Some CC). {
             eapply subtype_get_superclass.
             rewrite H2 in Swf, Nuq.
             eauto 2 using names_unique_decompose_program.
             rewrite H2 in Swf, Nuq.
             eauto 2 using subtype_well_founded_decompose_program.
             eapply find_class_eq.
           }
           destruct H3.
           eapply subtype_well_founded_neq.
           rewrite H2 in Nuq.
           eauto 2 using names_unique_decompose_program.
           rewrite H2 in Nuq, Swf.
           eauto 2 using subtype_well_founded_decompose_program.
       }

       generalize Flds;intros.
       rewrite H0 in Flds0.
       generalize H2;intros.
       rewrite app_assoc in Flds0.
       eapply IHn in H2; eauto 2.

       simpl.
       rewrite H.
       destruct H2.
       replace ((fl ++ get_fields_raw (JFCDecl dname (Some j) fields methods)) ++ x1 ++ x)
       with (fl ++ get_fields_raw (JFCDecl dname (Some j) fields methods) ++ (x1 ++ x)) in H2 by
           (rewrite app_assoc; auto 1).
       eapply flds_aux_decompose_first_same in H2.
       rewrite H2.
       rewrite H0.
       assert (flds_aux P dname (n + 1) fl =  Some (fl  ++ x1 ++ x)).
       {
         replace fl with (fl ++ []) by (rewrite app_nil_r; auto 1).
         rewrite <- app_assoc.
         eapply flds_aux_decompose_first_same.
         apply H2.
       }
       replace (n+1) with (S n) in H4 by auto 1 with zarith.
       simpl in H4.
       rewrite Heqo in H4.
       rewrite Flds0 in H4.
       injection H4;intros.
       rewrite <- app_assoc in H5.
       apply app_inv_head in H5.
       apply app_inv_tail in H5.
       rewrite H5.
       eexists.
       eauto 1.
    ++ simpl.
       rewrite H.
       replace (n+1) with (S n) by auto 1 with zarith.
       simpl.
       rewrite Heqo.
       injection Flds;intros.
       apply app_inv_head in H0.
       rewrite H0.
       rewrite <- app_assoc.
       eexists. auto 1.
Qed.

Lemma flds_aux_decompose_object:
  forall m P fl fl' fldlst dname decl n flds',
    flds_aux P JFObjectName n fl = Some (fl++fldlst) ->
    (program_contains P JFObjectName) = true ->
    find_class P dname = Some decl ->
    flds_aux P dname m fl' = Some (fl'++flds') ->
    subtype_well_founded P ->
    extensions_in_all_but_object P ->
    names_unique P ->
    exists flds'', flds' = flds'' ++ fldlst.
Proof.
  induction m.
  + intros P fl fl' fldlst dname decl n flds'.
    intros FldsAuxO PcontObj Fcls FldsAuxD Swf Eiabo Nuq.
    simpl in FldsAuxD.
    rewrite Fcls in FldsAuxD.
    destruct decl.
    generalize Fcls;intros.
    eapply find_class_eq_name in Fcls0;subst.
    generalize Fcls;intros.
    eapply find_class_in in Fcls0.
    unfold extensions_in_all_but_object in Eiabo.
    generalize Fcls;intros.
    eapply Forall_forall in Fcls0;try eapply Eiabo.
    destruct ex;try discriminate FldsAuxD.
    unfold if_not_extended_then_object in Fcls0.
    subst.
    injection FldsAuxD.
    intros.
    destruct n.
    ++ simpl in FldsAuxO.
       rewrite Fcls1 in FldsAuxO.
       injection FldsAuxO;intros;subst.
       eapply program_contains_find_class in PcontObj.
       destruct PcontObj.
       exists [].
       rewrite app_nil_l.
       eapply  app_inv_head in H.
       eapply  app_inv_head in H0.
       congruence.
    ++ simpl in FldsAuxO.
       rewrite Fcls in FldsAuxO.
       injection FldsAuxO;intros;subst.
       exists [];auto.
       rewrite app_nil_l.
       eapply  app_inv_head in H.
       eapply  app_inv_head in H0.
       congruence.
  + intros P fl fl' fldlst dname decl n flds'.
    intros FldsAuxO PcontObj Fcls FldsAuxD Swf Eiabo Nuq.
    generalize FldsAuxD;intros.
    simpl in FldsAuxD0.
    rewrite Fcls in FldsAuxD0.
    destruct decl.
    destruct ex.
    ++ generalize FldsAuxD0;intros.
       eapply flds_aux_decompose_acc in FldsAuxD1.
       destruct FldsAuxD1.
       rewrite H in FldsAuxD0.
       generalize Fcls;intros.
       eapply subtype_get_superclass in Fcls0;eauto 1.
       destruct Fcls0.

       eapply IHm in FldsAuxD0; eauto 2.
       rewrite app_ass in H.
       apply app_inv_head in H.
       rewrite H.
       destruct FldsAuxD0.
       rewrite H1.
       replace (get_fields_raw (JFCDecl D (Some j) fields methods) ++ x1 ++ fldlst)
       with ((get_fields_raw (JFCDecl D (Some j) fields methods) ++ x1) ++ fldlst)
         by (rewrite app_ass;auto).
       eexists;eauto.
    ++ generalize Fcls;intros.
       eapply find_class_eq_name in Fcls0.
       subst.
       generalize Fcls;intros.
       unfold extensions_in_all_but_object in Eiabo.
       eapply find_class_in in Fcls0.
       eapply Forall_forall in Fcls0; try eapply Eiabo.
       unfold if_not_extended_then_object in Fcls0.
       subst.
       assert (flds_aux P JFObjectName (S m) fl = Some (fl ++ flds')). {
         replace fl with (fl ++ []) by eauto using app_nil_r.
         rewrite app_ass.
         eapply flds_aux_decompose_second_same.
         replace fl' with (fl' ++ []) in FldsAuxD by eauto using app_nil_r.
         rewrite app_ass in FldsAuxD.
         eauto.
       }
       assert (Some (fl ++ flds') = Some (fl ++ fldlst)). {
         assert (S m <= n \/ n < S m) by auto using NPeano.Nat.le_gt_cases.
         destruct H0.
         assert (S m < n \/ S m = n) by  eauto using le_lt_or_eq.
         destruct H1.
         eapply flds_monotone_n in H1;eauto.
         rewrite H1 in FldsAuxO.
         auto.
         rewrite H1 in H.
         rewrite H in FldsAuxO.
         auto.
         eapply flds_monotone_n in FldsAuxO;eauto.
         rewrite FldsAuxO in H.
         auto.
       }
       injection H0;intros.
       apply app_inv_head in H1.
       subst.
       exists [].
       rewrite app_nil_l.
       auto.
 Qed.

(** How many extends steps there are to reach Object. *)
Fixpoint get_class_height (CC:JFProgram) (cn:JFClassName) : nat :=
  match CC with
  | [] => 0
  | (JFCDecl name (Some name') _ _) :: CC' =>
    if (JFClassName_dec name cn)
    then S (get_class_height CC' name')
    else get_class_height CC' cn
  | (JFCDecl name None _ _) :: CC' =>
    if (JFClassName_dec name cn)
    then 1
    else get_class_height CC' cn
  end.

Lemma get_class_height_non_zero:
  forall P D ex fields methods,
  In (JFCDecl D ex fields methods) P ->
         get_class_height P D <> 0.
Proof.
  induction P.
  + intros.
    auto 2 using in_nil.
  + intros.
    simpl.
    destruct a.
    destruct ex0.
    ++ destruct (JFClassName_dec D0 D).
       +++ auto 1.
       +++ apply in_inv in H.
           destruct H.
           ++++ injection H;intros;contradiction.
           ++++ eauto 2.
    ++ destruct (JFClassName_dec D0 D).
       +++ auto 1.
       +++ apply in_inv in H.
           destruct H.
           ++++ injection H;intros;contradiction.
           ++++ eauto 2.
Qed.

Lemma extends_get_class_height:
      forall P name dname,
        extends P name dname ->
        names_unique P ->
        (get_class_height P name) = S (get_class_height P dname).
Proof.
  induction P.
  * intros.
    inversion H.
  * intros.
    inversion H.
    ** subst.
       simpl.
       destruct (JFClassName_dec name name);try contradiction.
       eapply names_unique_extends_non_refl in H;auto 1.
       destruct (JFClassName_dec name dname);try contradiction.
       auto 1.
    ** subst.
       assert (C1 <> name).
       {
         eapply extends_in_first in H5.
         decompose_ex H5.
         eauto 2 using names_unique_in_neq.
       }
       assert (C1 <> dname).
       {
         eapply extends_in_second in H5.
         decompose_ex H5.
         eauto 2 using names_unique_in_neq.
       }
       generalize H5;intro.
       eapply IHP in H3;eauto 2 with myhints.
       simpl.
       destruct D1 eqn:?.
       *** destruct (JFClassName_dec C1 name); try contradiction.
           destruct (JFClassName_dec C1 dname); try contradiction.
           auto 1 with myhints.
       *** destruct (JFClassName_dec C1 name); try contradiction.
           destruct (JFClassName_dec C1 dname); try contradiction.
           auto 1 with myhints.
Qed.

Lemma find_class_get_class_height:
  forall P cn C,
    find_class P cn = Some C ->
    get_class_height P cn <> 0.
Proof.
  induction P.
  + intros.
    discriminate H.
  + intros.
    destruct a.
    simpl.
    simpl in H.
    intro.
    destruct (JFClassName_dec D cn).
    +++ destruct ex;discriminate H0.
    +++ destruct ex;eapply IHP;eauto.
Qed.

Lemma find_class_get_class_height_find_class:
  forall P cn dn en fields methods,
    find_class P cn = Some (JFCDecl dn (Some en) fields methods) ->
    names_unique P ->
    subtype_well_founded P ->
    exists edecl,
      find_class P en = Some edecl.
Proof.
  destruct P.
  + intros.
    discriminate H.
  + intros.
    destruct j.
    simpl.
    generalize H;intros.
    simpl in H.
    destruct (JFClassName_dec D cn).
    +++ subst.
        injection H;intros.
        subst.
        generalize H2;intros.
        eapply subtype_get_superclass in H3;eauto.
    +++ eapply find_class_further_neq in H2;eauto with myhints.
        eapply subtype_get_superclass in H2;eauto with myhints.
        destruct (JFClassName_dec D en);eauto with myhints.
Qed.

Lemma find_class_flds_aux:
  forall n P cn C flds,
    find_class P cn = Some C ->
    get_class_height P cn = n ->
    subtype_well_founded P ->
    names_unique P ->
    exists flds', flds_aux P cn n flds = Some flds'.
Proof.
  induction n.
  + intros.
    eapply find_class_get_class_height in H.
    congruence.
  + intros.
    simpl.
    rewrite H.
    destruct C.
    destruct ex.
    ++ generalize H;intros.
       eapply find_class_get_class_height_find_class in H;eauto.
       destruct H.
       assert (extends P cn j). {
         eapply find_class_extends;eauto 1.
         assert (cn=D) by eauto 2 using find_class_eq_name.
         subst.
         eauto 2 using subtype_well_founded_find_class_neq.
       }
       generalize H4;intros.
       eapply extends_in_second in H4.
       destruct H4 as [ex0 [fields' [methods' Inj]]].
       eapply in_find_class in Inj;eauto.
       eapply extends_get_class_height in H5;eauto.
       rewrite H0 in H5.
       injection H5;intros.
       eapply IHn;eauto.
    ++ eauto.
Qed.

(** Calculates the list of field identifiers in an object of the given
    class identifier [cls]. In case [cls] is the bottom class
    the function returns None. Otherwise it traverses the
    object hierarchy and collects filelds.

    Defined in Figure {fig:syntax} as the function flds. *)
Definition flds (CC:JFProgram) (cls:JFCId) :=
  match cls with
    | JFClass cname =>
      match flds_aux CC cname (get_class_height CC cname) [] with
        | None => None
        | Some l => Some (map name_of_fd l)
      end
    | JFBotClass => None
  end.


(** Calculates the list of field declarations in an object of the given
    class identifier [cls]. In case [cls] is the bottom class
    the function returns None. Otherwise it traverses the
    object hierarchy and collects filelds.

    Defined in Figure {fig:auxiliary-notation} as the function flds with overline bar. *)
Definition flds_overline (CC:JFProgram) (cls:JFCId)
: option (list (bool * JFCId * JFXId)) :=
  match cls with
    | JFClass cname =>
      flds_aux CC cname (get_class_height CC cname) []
    | JFBotClass => None
  end.

Lemma flds_overline_extends_decompose:
  forall P cname dname fldlst,
    extends P cname dname ->
    object_is_not_extended P ->
    names_unique P ->
    subtype_well_founded P ->
    extensions_in_all_but_object P ->
    flds_overline P (JFClass dname) = Some fldlst ->
    exists fldsn,
      flds_overline P (JFClass cname) = Some (fldsn ++ fldlst).
Proof.
  intros.
  simpl.
  simpl in H3.
  destruct (get_class_height P cname) eqn:?.
  + assert
      (exists (fields : list JFFieldDeclaration) (methods : list JFMethodDeclaration), In (JFCDecl cname (Some dname) fields methods) P)
      by eauto 2 using extends_in_first.
    destruct H5 as [fields [methods]].
    assert (get_class_height P cname <> 0) by eauto 2 using get_class_height_non_zero.
    contradiction.
  + replace fldlst with ([] ++ fldlst) in H4 by apply app_nil_l.
    generalize H;intros.
    eapply flds_aux_extends in H; eauto 1.
    replace (S n) with (n+1) by auto 1 using NPeano.Nat.add_1_r.
    destruct H.
    eexists.

    erewrite extends_get_class_height in Heqn; try apply H; eauto 1.
    injection Heqn;intros.
    rewrite <- H6. eauto 1.
Qed.

Lemma flds_overline_decompose:
  forall P C D fldlst,
    subtyping P D C ->
    flds_overline P C = Some fldlst ->
    object_is_not_extended P ->
    names_unique P ->
    subtype_well_founded P ->
    extensions_in_all_but_object P ->
    C <> JFObject ->
    D <> JFBotClass ->
    exists fldsn,
      flds_overline P D = Some (fldsn ++ fldlst).
Proof.
  induction 1.
  + eexists.
    replace fldlst with ([] ++ fldlst) in H by eauto using app_nil_l.
    eauto 1.
  + contradiction.
  + contradiction.
  + intros.
    assert (exists fldsn : list (bool * JFCId * JFXId), flds_overline P D = Some (fldsn ++ fldlst)). {
      eapply IHsubtyping;eauto 1.
      rewrite H0.
      discriminate.
    }
    destruct H10.
    rewrite H0 in H10.
    rewrite H.
    eapply flds_overline_extends_decompose in H1; try apply H10; eauto 1.
    destruct H1.
    rewrite H1.
    eexists.
    rewrite app_assoc.
    auto 1.
Qed.


Lemma flds_overline_find_class_decompose:
    forall P C D,
      subtyping P D C ->
      forall dname decl fldlst,
        D = (JFClass dname) ->
        flds_overline P C = Some fldlst ->
        object_is_not_extended P ->
        names_unique P ->
        subtype_well_founded P ->
        extensions_in_all_but_object P ->
        find_class P dname = Some decl ->
        exists fldsn,
          flds_overline P (JFClass dname) = Some (fldsn ++ fldlst).
Proof.
  induction 1.
  + eexists.
    rewrite H in H0.
    replace fldlst with ([] ++ fldlst) in H0 by eauto using app_nil_l.
    eauto 1.
  + intros.
    assert (subtyping P C C);eauto with myhints.
    generalize H5;intros.
    eapply find_class_flds_aux in H5;eauto with myhints.
    destruct H5.
    replace (get_class_height P dname + 0) with (get_class_height P dname) in H5 by auto with zarith.
    replace (flds_aux P dname (get_class_height P dname) [])
    with (flds_overline P C) in H5 by (rewrite H;simpl;auto).
    destruct (JFCId_dec C JFObject).
    ++ subst.
       rewrite e in *.
       replace fldlst with ([] ++ fldlst) in H0 by eauto using app_nil_l.
       eexists;eauto.
    ++ eapply flds_overline_decompose in H6;eauto; try (rewrite H;congruence).
       simpl.
       assert (exists flds' : list (bool * JFCId * JFXId), flds_aux P dname (get_class_height P dname) [] = Some flds'). {
         eapply find_class_flds_aux;eauto.
       }
       simpl in H0.
       replace fldlst with ([] ++ fldlst) in H0 by eauto using app_nil_l.
       destruct H8.
       replace x0 with ([] ++ x0) in H8 by eauto using app_nil_l.
       generalize H8;intros.
       eapply flds_aux_decompose_object in H8;eauto.
       rewrite H9.
       destruct H8.
       rewrite H8.
       rewrite <- app_ass.
       eexists;eauto.
       eapply subtype_well_founded_contains_object; eauto.
  + intros. discriminate H.
  + intros.
    generalize H0;intros.
    generalize H1;intros.
    eapply  extends_in_second in H11;eauto.
    destruct H11 as [ex0 [fields' [methods']]].
    eapply in_find_class in H11;eauto.
    eapply IHsubtyping in H10;eauto.
    simpl.
    rewrite H in H3;injection H3;intros;subst;clear H3.
    replace (get_class_height P dname0) with ((get_class_height P dname) +1) by
        (replace (get_class_height P dname + 1) with (S (get_class_height P dname)) by
            auto with zarith;
         symmetry;
         eapply extends_get_class_height;eauto).
    generalize H1;intros.
    destruct H10.
    simpl in H.
    replace  (x ++ fldlst) with  ([] ++ x ++ fldlst) in H by eauto using app_nil_l.
    eapply flds_aux_extends in H0;eauto.
    destruct H0.
    rewrite H0.
    rewrite app_nil_l.
    rewrite <- app_ass.
    eexists;eauto.
Qed.


Lemma flds_overline_subtyping:
  forall P C D,
    subtyping P C D ->
    subtype_well_founded P ->
    names_unique P ->
    extensions_in_all_but_object P ->
    forall cname flds,
    flds_overline P D = Some flds ->
    D <> JFObject ->
    C = JFClass cname ->
    exists flds',
    flds_overline P (JFClass cname) = Some flds'.
Proof.
  intros P C D.
  induction 1  using subtyping_ind.
  + intros Swf Nuq Eiabo cname flds Flds Dneq Ceq.
    exists flds.
    subst.
    auto 1.
  + contradiction.
  + intros. discriminate H4.
  + subst. intros Swf Nuq Eiabo name flds.
    intros Flds' Eneq Nameq.
    injection Nameq;intros;clear Nameq.
    subst.
    destruct E.
    ++ eapply IHsubtyping in Flds'; try trivial.
       destruct Flds'.
       unfold flds_overline in H.
       simpl.
       generalize H1;intros.
       eapply extends_get_class_height in H0;eauto 1.
       rewrite H0.
       replace  (S (get_class_height P dname)) with ((get_class_height P dname) + 1)  by auto 1 using NPeano.Nat.add_1_r.
       generalize H1;intros.
       replace x with ([] ++ x) in H by auto 1 using app_nil_l.
       eapply flds_aux_extends in H3; try apply H;eauto 1.
       destruct H3.
       rewrite H3.
       eexists.
       auto 1.
    ++ simpl in Flds'.
       discriminate Flds'.
Qed.

(** Calculates the type of the parameter [num] in the method [mid] in
    the class [cls]. In case [cls] is the bottom class the function
    returns None. Otherwise it looks up the method [mid] in the class
    declaration of [cls] in [CC]. If it succeeds it returns the type
    of the paramter. Otherwise it returns None. We use here the
    operation (.)^rwr in case method has no annotations. The value
    num=0 is for the type of this.

    Defined in Figure {fig:auxiliary-notation} as the function parTypM.
  *)
Definition parTypM_of_md (cls:JFCId) (md: JFMethodDeclaration) (num:nat) : JFACId :=
  match md with
  | JFMDecl D mu mn vs excs E =>
    match num with
    | 0 => (cls, mu)
    | _ => nth (num-1) (map snd vs) (JFObject, JFrwr)
    end
  | JFMDecl0 D mn vs excs E =>
    match num with
    | 0 => (cls, JFrwr)
    | _ => (nth (num-1) (map snd vs) JFObject, JFrwr)
    end
  end.


Definition parTypM (CC:JFProgram) (cls:JFCId) (mid:JFMId) (num:nat)
  : option JFACId :=
  match cls with
    | JFClass cname =>
      let mdo := methodLookup CC cname mid in
      match mdo with
      | Some md => Some (parTypM_of_md cls md num)
      | None => None
      end
    | JFBotClass => None
  end.


Definition retTypM (CC:JFProgram) (cls:JFCId) (mid:JFMId)
  : option JFACId :=
  match cls with
    | JFClass cname =>
      let mdo := methodLookup CC cname mid in
      match mdo with
        | Some md => Some (rettyp_of_md md)
        | None => None
      end
    | JFBotClass => None
  end.


Definition thrs (CC:JFProgram) (cls:JFCId) (mid:JFMId)
  : option (list JFACId) :=
  match cls with
    | JFClass cname =>
      let mdo := methodLookup CC cname mid in
      match mdo with
        | Some md => Some (thrs_of_md md)
        | None => None
      end
    | JFBotClass => None
  end.



Definition body (CC:JFProgram) (cls:JFCId) (mid:JFMId)
  : option JFExpr :=
  match cls with
    | JFClass cname =>
      let mdo := methodLookup CC cname mid in
      match mdo with
        | Some md =>
          Some (body_of_md md)
        | None => None
      end
    | JFBotClass => None
  end.

(*-------------------------- Objects ------------------------------------------*)

Module JFXIdDecidable <: DecidableType.
  Definition t := JFXId.
  Definition eq := @eq t.
  Include EqNotation.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Instance eq_equiv : Equivalence eq.
  Proof.
    split; red; firstorder.
    eapply eq_trans; eassumption.
  Qed.
  Definition eq_dec := string_dec.
End JFXIdDecidable.

Module JFXIdMap := FMapWeakList.Make(JFXIdDecidable).

Definition RawObj := JFXIdMap.t Loc.  (* JFXId => Loc *)
Module RawObj := JFXIdMap. (* to make it possible to use RawObj.find instead JFXIdMap.find *)

(*
Definition find k (m: map_nat_nat) := M.find k m.

Definition update (p: nat * nat) (m: map_nat_nat) :=
  M.add (fst p) (snd p) m.

Notation "k |-> v" := (pair k v) (at level 60).
Notation "[ ]" := (M.empty nat).
Notation "[ p1 , .. , pn ]" := (update p1 .. (update pn (M.empty nat)) .. ).
*)


Definition Obj : Type := (RawObj * JFClassName)%type.

(*
Definition get_fields (CC:JFProgram) : JFCId -> list JFXId :=
*)

(**
    The function creates an object of the given class name [cname]
    with the fields from [flds] initialised to [null].

    This is as defined in Figure {fig:semantics}, case newk.
*)
Definition create_initial_obj (flds : list JFXId) (cname : JFClassName) : Obj :=
  let create_initial_obj_aux :=
      fix F flds o :=
        match flds with
        | [] => o
        | hd :: tl => F tl (JFXIdMap.add hd null o)
        end
  in (create_initial_obj_aux flds (JFXIdMap.empty Loc), cname).

Definition init_obj (flds : list JFXId) (cname : JFClassName) (vals : list Loc) : option Obj :=
  let init_obj_aux :=
      fix F flds vals (o : RawObj) : option RawObj :=
        match flds, vals with
        | [], [] => Some o
        | fhd :: ftl, vhd :: vtl => F ftl vtl (JFXIdMap.add fhd vhd o)
        | _, _ => None
        end
  in
  match init_obj_aux flds vals (JFXIdMap.empty _) with
  | None => None
  | Some ro => Some (ro, cname)
  end.


(*-------------------------- Heaps --------------------------------------------*)

Module NatMap := FMapAVL.Make(Nat_as_OT).
Module Heap := NatMap.

Definition Heap : Type :=  NatMap.t Obj. (* Loc => Obj *)

Definition getClassName (h:Heap) (n:nat) :=
  match Heap.find n h with
    | None => None
    | Some (_, cid) => Some cid
  end.

(* --- Initially on a heap --- *)
Definition Object_object := create_initial_obj [] JFObjectName.
Definition Object_object_loc := 0%nat.
Definition Object_val := JFVLoc (JFLoc Object_object_loc).
Definition NPE_object := create_initial_obj [] JFNPEName.
Definition NPE_object_loc := 2.
Definition NPE_val := JFVLoc (JFLoc NPE_object_loc).

Definition create_initial_heap :Heap :=
  let h0 := NatMap.add Object_object_loc Object_object (NatMap.empty Obj) in
  let h2 := NatMap.add NPE_object_loc NPE_object h0
  in h2.

Definition class (h:Heap) (n : nat) : option JFClassName :=
  match NatMap.find n h with
  | None => None
  | Some (_,c) => Some c
  end.

Definition field_correct_heap (CC:JFProgram) (robj:RawObj) (h:Heap)
           (fd:bool * JFCId * JFXId) :=
  match fd with
  | (_,fc, fn) => exists (l:Loc),
      RawObj.find fn robj = Some l /\
      match l with
      | null => True
      | JFLoc n => exists cn' robj',
          Heap.find n h = Some (robj', cn')  /\
          subtyping CC (JFClass cn') (JFClass fn)
      end
  end.


Definition object_correct_heap (CC:JFProgram) (robj:RawObj) (cn:JFClassName) (h:Heap) :=
  forall flds,
    flds_overline CC (JFClass cn) = Some flds ->
    Forall (field_correct_heap CC robj h) flds.

Definition type_correct_heap CC h : Prop :=
  forall (n : nat) (robj:RawObj) (cn:JFClassName),
    Heap.find n h = Some (robj,cn) ->
    (exists (cdecl:JFClassDeclaration),
        find_class CC cn = Some cdecl) /\
    (* class is declared *)
    (forall (fnm:JFXId) (l:Loc), JFXIdMap.find (elt:=Loc) fnm robj = Some l ->
                                 exists fds, flds CC (JFClass cn) = Some fds /\
                                             In fnm fds) /\
    (* all the fields of the object are in the class *)
    object_correct_heap CC robj cn h.
    (* all the fields in the class are in the object and have the
       declared type in the heap *)

Lemma type_correct_heap_find_class:
  forall CC h n robj cn,
    type_correct_heap CC h ->
    Heap.find n h = Some (robj,cn) ->
    exists (cdecl:JFClassDeclaration),
      find_class CC cn = Some cdecl.
Proof.
  intros.
  unfold type_correct_heap in H.
  apply H in H0.
  destruct H0.
  destruct H0.
  eexists;eauto.
Qed.

Lemma type_correct_heap_find_field:
  forall fs P h n oo C x fd,
    type_correct_heap P h ->
    Heap.find (elt:=Obj) n h = Some (oo, C) ->
    flds_aux P C (get_class_height P C) [] = Some fs ->
    JFXIdMap.find (elt:=Loc) x oo = Some fd ->
    exists fdcs,
      find_field fs x = Some fdcs.
Proof.
  induction fs.
  + intros.
    unfold type_correct_heap in H.
    eapply H in H0.
    destruct H0.
    eapply H3 in H2.
    simpl in H2.
    destruct (get_class_height P C) eqn:gch.
    ++ simpl in H1.
       simpl in H2.
       destruct (find_class P C) eqn:fcls;try discriminate H1.
       destruct j;try discriminate H1.
       destruct ex; try discriminate H1.
       injection H1;intros.
       rewrite H4 in H2.
       simpl in H2.
       destruct H2.
       destruct H2.
       injection H2;intros;subst.
       contradiction.
    ++ rewrite H1 in H2.
       simpl in H2.
       destruct H2.
       destruct H2.
       injection H2;intros;subst.
       contradiction.
  + intros.
    destruct a.
    unfold type_correct_heap in H.
    eapply H in H0.
    destruct H0.
    eapply H3 in H2.
    simpl in H2.
    rewrite H1 in H2.
    destruct H2.
    destruct H2.
    injection H2;intros;subst.
    destruct p.
    apply in_inv in H4.
    simpl.
    destruct (JFXId_dec x j).
    ++ eexists;auto.
    ++ destruct H4;try (symmetry in H4;contradiction).
       eauto with myhints.
Qed.


Definition alloc (CC:JFProgram) (h:Heap) (cname:JFClassName): Loc * Heap :=
  let domain := NatMap.fold (fun k e res => k :: res) h [] in
  let get_first_free := fix F maxx (prev:nat) (lst:list nat) :=
      match lst with
      | [] => maxx
      | hd :: tl => if (Nat.eqb (hd + 1) prev)
                    then (F maxx hd tl)
                    else hd + 1
      end in
   let freeloc := get_first_free 0 0 domain in
   let objflds := flds CC (JFClass cname) in
   let newobject := match objflds with
                    | None => create_initial_obj [] cname
                    | Some fl => create_initial_obj fl cname
                    end in
   let newheap := NatMap.add freeloc newobject h
   in (JFLoc freeloc, newheap).


Definition alloc_init (CC:JFProgram) (h:Heap) (cname:JFClassName) (vals: list Loc): option (Loc * Heap) :=
  let domain := NatMap.fold (fun k e res => k :: res) h [] in
  let get_first_free := fix F maxx (prev:nat) (lst:list nat) :=
      match lst with
      | [] => maxx
      | hd :: tl => if (Nat.eqb (hd + 1) prev)
                    then (F maxx hd tl)
                    else hd + 1
      end in
   let freeloc := get_first_free 0 0 domain in
   let objflds := flds CC (JFClass cname) in
   let newobject := match objflds with
                    | None => init_obj [] cname vals
                    | Some fl => init_obj fl cname vals
                    end in
   match newobject with
   | Some o => let newheap := NatMap.add freeloc o h
              in Some (JFLoc freeloc, newheap)
   | None => None
   end.

Inductive JFContextNode : Set :=
| JFCtxLet (C:JFClassName) (x:JFXId) (Ctx:unit) (E2:JFExpr)
| JFCtxTry (Ctx:unit) (mu:JFAMod) (C:JFClassName) (x:JFXId) (E2:JFExpr).

Definition JFContext : Set := list JFContextNode.

Definition JFEvMode : Set := option JFClassName.

Definition NPE_mode := Some JFNPEName.

Inductive Frame :=
  MkFrame (Ctx:JFContext) (E:JFExpr) (A:JFEvMode).



Definition FrameStack := list Frame.


(**
   - all class names are unique
   - contains Object
   - contains NPE
   - Object is not extended
   - if class is not extension then it is the class of Object
   - subtyping is well founded
*)
Definition Well_formed_program (P:JFProgram) :=
  names_unique P /\
  (program_contains P JFObjectName) = true /\
  (program_contains P JFNPEName) = true /\
  object_is_not_extended P /\
  extensions_in_all_but_object P /\
  subtype_well_founded P.

Lemma well_formed_program_names_unique:
  forall P,
    Well_formed_program P -> names_unique P.
Proof.
  intros. red in H.
  intuition.
Qed.

Lemma well_formed_program_contains_object:
  forall P,
    Well_formed_program P -> (program_contains P JFObjectName) = true.
Proof.
  intros. red in H.
  intuition.
Qed.

Lemma well_formed_program_contains_npe:
  forall P,
    Well_formed_program P -> (program_contains P JFNPEName) = true.
Proof.
  intros. red in H.
  intuition.
Qed.

Lemma well_formed_program_object_is_not_extended:
  forall P,
    Well_formed_program P ->   object_is_not_extended P.
Proof.
  intros. red in H.
  intuition.
Qed.

Lemma well_formed_program_extensions_in_all_but_object:
  forall P,
    Well_formed_program P -> extensions_in_all_but_object P.
Proof.
  intros. red in H.
  intuition.
Qed.

Lemma well_formed_program_subtype_well_founded:
  forall P,
    Well_formed_program P -> subtype_well_founded P.
Proof.
  intros. red in H.
  intuition.
Qed.

Hint Resolve well_formed_program_names_unique  well_formed_program_contains_object
     well_formed_program_contains_npe well_formed_program_object_is_not_extended
     well_formed_program_extensions_in_all_but_object well_formed_program_subtype_well_founded
     type_correct_heap_find_class type_correct_heap_find_field : myhints.



Lemma well_formed_program_further:
  forall C P,
    program_contains P JFObjectName = true ->
    program_contains P JFNPEName = true ->
    Well_formed_program (C :: P) ->
    Well_formed_program P.
Proof.
  intros.
  unfold Well_formed_program in *.
  decompose [and] H1; clear H1.
  repeat split.
  + apply (names_unique_further P C); auto 1.
  + auto 1.
  + auto 1.
  + apply (object_is_not_extended_further P C); auto 1.
  + apply (extensions_in_all_but_object_further P C); auto 1.
  + apply (subtype_well_founded_further P C); auto 1.
Qed.


Lemma subtype_bool_complete :
  forall P Cid Did, Well_formed_program P ->
                    subtyping P Cid Did ->
                    subtype_bool P Cid Did = true.
Proof.
  intuition.
    unfold subtype_bool.
    destruct Cid.
    destruct Did.
    + unfold JFObject.
      unfold Well_formed_program in H.
      decompose [and] H.
      destruct (JFClassName_dec name name0); [rewrite e; eauto 1 with myhints|].
      destruct (JFClassName_dec name0 JFObjectName); [rewrite e; eauto 1 with myhints|].
      destruct (JFClassName_dec name JFObjectName).
      subst name.
      assert (JFClass name0 = JFObject).
      eapply object_is_not_subtype; eauto 1.
      unfold JFObject in H6. congruence.
      assert (exists CC : JFClassDeclaration, find_class P name = Some CC).
      { eapply subtyping_find_class.
        assert (JFClass name <> JFClass name0) by congruence.
        apply H6.
        unfold JFObject.
        congruence.
        congruence.
        auto 1.
        auto 1.
      }
      destruct H6.
      eapply subtype_class_bool_complete; eauto 1.
      unfold JFObject.
      congruence.
    + inversion H0.
      assert (D= JFBotClass).
      eapply subtyping_not_bot.
      apply H4.
      auto 1.
      congruence.
    + auto 1.
Qed.

Lemma subtype_bool_correct_technical:
  forall P Cid Did,
    names_unique P ->
    program_contains P JFObjectName = true ->
    object_is_not_extended P ->
    extensions_in_all_but_object P -> subtype_well_founded P ->
    subtype_bool P Cid Did = true ->
    subtyping P Cid Did.
Proof.
  induction P; intros.
  - unfold Well_formed_program in H.
    unfold program_contains in H0.
    discriminate H0.
  - unfold subtype_bool in H4.
    destruct Cid.
    + destruct Did.
      unfold subtype_class_bool in H4.
      destruct (JFClassName_dec name name0); [rewrite e; eauto 1 with myhints|].
      destruct (JFClassName_dec name0 JFObjectName); [rewrite e; eauto 1 with myhints|].
      { destruct a.
        - destruct ex.
          fold (subtype_class_bool P name name0) in H4.
          fold (subtype_class_bool P j name0) in H4.
          destruct (JFClassName_dec name D).
          + destruct (JFClassName_dec j name0).
            * subst D.
              subst j.
              eapply substep.
              eauto 1.
              assert (JFClass name0 = JFClass name0) by auto 1.
              apply H5.

              assert (exists CC : JFClassDeclaration, find_class (JFCDecl name (Some name0) fields methods :: P) name0 = Some CC).
              { eapply subtype_get_superclass;eauto 2.
                assert (find_class
                          (JFCDecl name (Some name0) fields methods :: P) name =
                        Some (JFCDecl name (Some name0) fields methods)).
                apply find_class_eq.
                apply H5.
              }
              destruct H5.
              assert (find_class P name0 = Some x). {
                eapply find_class_further_neq.
                apply n.
                apply H5.
              }
              destruct x.
              eapply base.
              apply find_class_in.
              assert (name0=D). {
                eapply find_class_eq_name.
                apply H6.
              }
              subst D.
              apply H6.
              apply subrefl.
            * subst D.
              eapply substep.
              auto 1.
              assert (JFClass j = JFClass j) by auto 1.
              apply H5.

              assert (exists CC : JFClassDeclaration, find_class (JFCDecl name (Some j) fields methods :: P) j = Some CC).
              { eapply subtype_get_superclass;eauto 1.
                assert (find_class
                          (JFCDecl name (Some j) fields methods :: P) name =
                        Some (JFCDecl name (Some j) fields methods)).
                apply find_class_eq.
                apply H5.
              }
              destruct H5.
              assert (find_class P j = Some x). {
                eapply find_class_further_neq.
                assert (name<>j) by eauto 2 using subtype_well_founded_neq.
                apply H6.
                apply H5.
              }
              destruct x.
              eapply base.
              apply find_class_in.
              assert (j=D). {
                eapply find_class_eq_name.
                apply H6.
              }
              subst D.
              apply H6.
              apply subtyping_further.
              eapply IHP; eauto 2 with myhints.
              assert (name<>JFObjectName) by eauto 2 with myhints.
              eauto 2 using program_contains_further_neq.
          + apply subtyping_further.
            apply IHP; eauto 2 with myhints.
            assert (D<>JFObjectName) by eauto 2 with myhints.
            eauto 2 using program_contains_further_neq.
          + destruct (JFClassName_dec name D).
            discriminate H4.
            fold (subtype_class_bool P name name0) in H4.
            apply subtyping_further.
            apply IHP; eauto 2 with myhints.
            assert (exists cl, find_class P name = Some cl) by eauto 2 using subtype_class_bool_find_class.
            destruct H5.
            eapply subtype_well_founded_contains_object; eauto 2 with myhints.
      }
      discriminate H4.
  + auto 2 with myhints.
Qed.

Lemma subtype_bool_correct:
  forall P Cid Did,
    Well_formed_program P ->
    subtype_bool P Cid Did = true ->
    subtyping P Cid Did.
Proof.
  intros.
  unfold Well_formed_program in *.
  decompose [and] H; clear H.
  eauto 2 using subtype_bool_correct_technical.
Qed.

Lemma find_field_in_subclass:
  forall P C C' D fldlst rep x n h o,
    subtype_well_founded P ->
    names_unique P ->
    object_is_not_extended P ->
    extensions_in_all_but_object P ->
    type_correct_heap P h ->
    flds_overline P C = Some fldlst ->
    In (rep, C', x) fldlst ->
    Heap.find (elt:=Obj) n h = Some (o, D) ->
    subtyping P (JFClass D) C ->
    exists l,
      JFXIdMap.find (elt:=Loc) x o = Some l.
Proof.
  intros P C C' D fldlst rep x n h o.
  intros Swf Nuq Oine Eiabo Tchp Flds Inn Hpfnd Sub.
  unfold type_correct_heap in Tchp.
  unfold object_correct_heap in Tchp.
  assert (exists cdecl : JFClassDeclaration,
        find_class P D = Some cdecl /\
        (forall flds : list (bool * JFCId * JFXId),
         flds_overline P (JFClass D) = Some flds ->
         Forall (field_correct_heap P o h) flds)). {
    eapply Tchp in Hpfnd.
    destruct Hpfnd.
    destruct H.
    exists x0.
    split.
    auto.
    intuition.
  }
  destruct H as [cdecl [FclsD FldsD]].
  assert  (exists fldsn, flds_overline P (JFClass D) = Some (fldsn ++ fldlst)) by
    (eapply flds_overline_find_class_decompose; try apply Sub; eauto 2;discriminate).
  destruct H.
  apply FldsD in H.
  assert (forall x, In x (x0 ++ fldlst) -> (field_correct_heap P o h x)) by
      (apply Forall_forall; auto 1).
  assert (In (rep, C', x) (x0 ++ fldlst)) by eauto 3 using in_or_app.
  apply H0 in H1.
  simpl in H1.
  destruct H1.
  destruct H1.
  exists x1.
  auto 1.
Qed.

Notation "Ctx [[ E ]]_ A" := (MkFrame Ctx E A) (at level 60).
Notation "Ctx _[ Ctxa _[[_ E _]]_ A ]_" := (MkFrame (Ctxa :: Ctx) E A) (at level 20).

Fixpoint well_formed_framestack_aux fs :=
  match fs with
  | [] => True
  | Ctx [[ (JFInvoke (JFVLoc (JFLoc n)) _ _) ]]_ None :: fstl => well_formed_framestack_aux fstl
  | _ => False
  end.

Definition well_formed_framestack fs :=
  match fs with
  | [] => False
  | _ :: fstl => well_formed_framestack_aux fstl
  end.


(* TODO: ujednolicić prezentację identyfikatorów l, l1... w kolejności występowania *)

Definition getInvokeBody CC D0 (n:nat) m vs (h:Heap) Ctx Cc :=
  match D0 with
    | None => None
    | Some D =>
      let mm := methodLookup CC D m in
      match mm with
        | None => None
        | Some mn =>
          let E := body_of_md mn in
          let frmls := map JFVar (params_of_md mn) in
          let Esub := substList frmls vs
                                (substExpr JFThis  (JFLoc n) E) in
          match Esub with
            | None => None
            | Some Es =>
              Some (h, (nil [[ Es ]]_ None) ::
                       (Ctx[[ (JFInvoke (JFVLoc (JFLoc n)) m vs) ]]_ None ) :: Cc)
          end
      end
  end.

Lemma getInvokeBody_Some:
  forall P D n m vs h h' Ctx Cc Cc',
    getInvokeBody P D n m vs h Ctx Cc = Some (h', Cc') ->
    exists hd1 hd2, Cc' = hd1 :: hd2 :: Cc /\ h = h'.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct D;try discriminate H.
  destruct (methodLookup P j m); try discriminate H.
  destruct (substList (map JFVar (params_of_md j0)) vs
                      (substExpr JFThis (JFLoc n) (body_of_md j0)));
    try discriminate H.
  injection H;intros.
  rewrite <- H0.
  eexists;eauto.
Qed.

Lemma getInvokeBody_Some_ClassName:
  forall P D n m vs h h' Ctx Cc Cc',
    getInvokeBody P D n m vs h Ctx Cc = Some (h', Cc') ->
    exists Dd, D = Some Dd.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct D; try discriminate H.
  eexists;eauto.
Qed.

Lemma getInvokeBody_Some_methodLookup:
  forall P Dd n m vs h h' Ctx Cc Cc',
    getInvokeBody P (Some Dd) n m vs h Ctx Cc = Some (h', Cc') ->
    exists md, methodLookup P Dd m = Some md.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct (methodLookup P Dd m); try discriminate H.
  eexists;eauto.
Qed.


Lemma getInvokeBody_Some_find_class:
  forall P Dd n m vs h h' Ctx Cc Cc',
    getInvokeBody P (Some Dd) n m vs h Ctx Cc = Some (h', Cc') ->
    exists ddecl, find_class P Dd = Some ddecl.
Proof.
  intros.
  unfold getInvokeBody in H.
  destruct (methodLookup P Dd m) eqn:MthdLkp; try discriminate H.
  eapply methodLookup_find_class.
  eauto.
Qed.



Definition loc_of_val v := match v with JFVLoc l => Some l | _ => None end.

Definition list_map_opt {A B} (f:A -> option B) l :=
  let F :=
      fix F l acc :=
        match l with
        | [] => Some (List.rev acc)
        | h::t =>
          match f h with
          | None => None
          | Some b => F t (b::acc)
          end
        end
  in
  F l [].

Definition red  (CC:JFProgram) (WfCC : Well_formed_program CC) : Heap * FrameStack -> option (Heap * FrameStack) :=
  fun hfst => let (h, st) := hfst in
    match st with
      | [] => None
      | (*newk*)
        Ctx[[JFNew mu C vs]]_ None :: Cc =>
          (*          let (l0, hp) := alloc CC h C *)
          match list_map_opt loc_of_val vs with
          | None => None
          | Some locs =>
            match alloc_init CC h C locs with
            | None => None
            | Some (l0, hp) => Some (hp, Ctx[[JFVal1 (JFVLoc l0)]]_ None :: Cc)
            end
          end
      | (* letin *)
        (Ctx[[ JFLet C x E1 E2 ]]_ None ) :: Cc =>
           Some (h, (Ctx _[ (JFCtxLet C x tt E2 ) _[[_ E1 _]]_ None ]_) :: Cc)
      | (*letgo*)
        (Ctx _[ (JFCtxLet C x _ E) _[[_ (JFVal1 (JFVLoc l)) _]]_ None ]_) :: Cc =>
           Some (h, Ctx[[ substExpr (JFVar x) l E ]]_ None :: Cc)
      | (*ifeq/ifneq*)
        (Ctx[[ JFIf (JFVLoc l1) (JFVLoc l2) E1 E2 ]]_ None ) :: Cc =>
          if Loc_dec l1 l2
          then Some (h, Ctx[[E1]]_ None :: Cc)
          else Some (h, Ctx[[E2]]_ None :: Cc)
      | (* mthdnpe *)
        (Ctx[[ (JFInvoke JFnull _ _) ]]_ None ) :: Cc =>
          Some (h, Ctx[[ JFVal1 NPE_val ]]_ NPE_mode :: Cc)
      | (* mthd *)
        (Ctx[[ (JFInvoke (JFVLoc (JFLoc n)) m vs) ]]_ None ) :: Cc =>
        let D0 := getClassName h n in  getInvokeBody CC D0 n m vs h Ctx Cc
      | (* mthdret   *)
        (nil [[JFVal1 (JFVLoc l) ]]_ None) :: (Ctx[[ (JFInvoke _ _ _) ]]_ None ) :: Cc =>
           Some (h, (Ctx[[ (JFVal1 (JFVLoc l)) ]]_ None ) :: Cc)
      | (* assignnpe *)
        (Ctx[[ (JFAssign (JFnull, id) (JFVLoc l)) ]]_ None ) :: Cc =>
           Some (h, (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode ) :: Cc)
      | (* assignev  *)
        (Ctx[[ (JFAssign (JFVLoc (JFLoc n), x) (JFVLoc l)) ]]_ None ) :: Cc =>
          let o := Heap.find n h
          in match o with
               | None => None
               | Some (ro, cid) =>
                 let modo := (JFXIdMap.add x l ro, cid) in
                 let h1 := Heap.add n modo h
                 in Some (h1, (Ctx[[ JFVal1 (JFVLoc l) ]]_ None ) :: Cc)
             end
      | (* varnpe   *)
        (Ctx[[ (JFVal2 (JFnull, x)) ]]_ None ) :: Cc =>
          Some (h, (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode ) :: Cc)
      | (* var      *)
        (Ctx[[ (JFVal2 (JFVLoc (JFLoc n), x)) ]]_ None ) :: Cc =>
          let o := Heap.find n h
          in match o with
               | None => None
               | Some (ro, cid) =>
                 let ol1 := JFXIdMap.find x ro
                 in match ol1 with
                      | None => None
                      | Some l1 => Some (h, (Ctx[[ JFVal1 (JFVLoc l1)  ]]_ None ) :: Cc)
                    end
          end
      | (* thrownull *)
        (Ctx[[ (JFThrow JFnull) ]]_ None ) :: Cc =>
          Some (h, (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode ) :: Cc)
      | (* throw *)
        (Ctx[[ (JFThrow (JFVLoc (JFLoc n))) ]]_ None ) :: Cc =>
          match class h n with
            | None => None
            | Some cname =>
              Some (h, (Ctx[[ JFVal1 (JFVLoc (JFLoc n)) ]]_ (Some cname)) :: Cc)
          end
      | (* ctchin *)
        (Ctx[[ (JFTry E1 mu C x E2) ]]_ None ) :: Cc =>
           Some (h, Ctx _[ (JFCtxTry tt mu C x E2)  _[[_ E1 _]]_ None ]_ :: Cc)

      | (* ctchnrml *)
        (Ctx _[ (JFCtxTry _ mu C x E2)  _[[_ JFVal1 (JFVLoc l) _]]_ None ]_ ) :: Cc =>
           Some (h, (Ctx[[ JFVal1 (JFVLoc l) ]]_ None ) :: Cc)


      | (* letex *)
        (Ctx _[ (JFCtxLet C x _ E) _[[_ (JFVal1 (JFVLoc l)) _]]_ (Some C') ]_) :: Cc =>
           Some (h, (Ctx[[ JFVal1 (JFVLoc l) ]]_ (Some C') ) :: Cc)

      | (* methodex *)
        (nil [[JFVal1 (JFVLoc l) ]]_ (Some C) ) :: (Ctx[[ (JFInvoke _ _ _) ]]_ None ) :: Cc =>
           Some (h, (Ctx[[ (JFVal1 (JFVLoc l)) ]]_ (Some C) ) :: Cc)

      | (* ctchexnok/ctchexok *)
        (Ctx _[ (JFCtxTry _ mu C x E2) _[[_ (JFVal1 (JFVLoc l)) _]]_ (Some C') ]_) :: Cc =>
           if subtype_bool CC (JFClass C') (JFClass C) then
             Some (h, Ctx[[ substExpr (JFVar x) l E2 ]]_ None :: Cc) (* ctchexok *)
           else
             Some (h, (Ctx[[ JFVal1 (JFVLoc l) ]]_ (Some C') ) :: Cc) (* ctchexnok *)
      | _ => None
end.


(** The same as [red] but cases are more carefully selected, so there
    are less similar cases in proofs over the reduction relation. *)

Definition red2  (CC:JFProgram) (WfCC : Well_formed_program CC)
  : Heap * FrameStack -> option (Heap * FrameStack) :=
  fun hfst => let (h, st) := hfst in
    match st with
    | (Ctx [[ E ]]_ Some C') :: Cc =>
        match E with
        | JFVal1 (JFVLoc l) =>
            match Ctx with
            (* methodex *)
            | [] =>
                match Cc with
                | (Ctx0 [[JFInvoke _ _ _ ]]_ None) :: Cc =>
                    Some (h, (Ctx0 [[JFVal1 (JFVLoc l) ]]_ Some C') :: Cc)
                | _ => None
                end
            (* letex *)
            | JFCtxLet C x _ E2 :: Ctx' =>
                Some (h, (Ctx' [[JFVal1 (JFVLoc l) ]]_ Some C') :: Cc)
            (* ctchexnok/ctchexok *)
            | JFCtxTry _ mu C x E2 :: Ctx' =>
                if subtype_class_bool CC C' C
                then (* ctchexok *)
                  Some (h, (Ctx' [[substExpr (JFVar x) l E2 ]]_ None) :: Cc)
                else (* ctchexnok *)
                  Some (h, (Ctx' [[JFVal1 (JFVLoc l) ]]_ Some C') :: Cc)
            end
        | _ => None
        end
    | (Ctx [[E ]]_ None) :: Cc =>
        match E with
        (* newk *)
        | JFNew _ C vs =>
            match list_map_opt loc_of_val vs with
            | Some locs =>
                match alloc_init CC h C locs with
                | Some (l0, hp) => Some (hp, (Ctx [[JFVal1 (JFVLoc l0) ]]_ None) :: Cc)
                | None => None
                end
            | None => None
            end
        (* letin *)
        | JFLet C x E1 E2 => Some (h, Ctx _[ JFCtxLet C x tt E2 _[[_ E1 _]]_ None ]_ :: Cc)
        (* ifeq/ifneq *)
        | JFIf (JFVLoc l1) (JFVLoc l2) E1 E2 =>
          Some (h, (Ctx [[ if Loc_dec l1 l2 then E1 else E2 ]]_ None) :: Cc)
        (* mthdnpe *)
        | JFInvoke JFnull _ _ => Some (h, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: Cc)
        (* mthd *)
        | JFInvoke (JFVLoc (JFLoc n)) m vs => getInvokeBody CC (getClassName h n) n m vs h Ctx Cc
        (* assignnpe *)
        | JFAssign (JFnull, id) (JFVLoc l) => Some (h, (Ctx[[ JFVal1 NPE_val ]]_ NPE_mode ) :: Cc)
        (* assignev  *)
        | JFAssign (JFVLoc (JFLoc n), x) (JFVLoc l) =>
            let o := Heap.find n h
            in match o with
               | None => None
               | Some (ro, cid) =>
                   let modo := (JFXIdMap.add x l ro, cid) in
                   let h1 := Heap.add n modo h
                   in Some (h1, (Ctx[[ JFVal1 (JFVLoc l) ]]_ None ) :: Cc)
               end
        | JFVal1 (JFVLoc l) =>
            match Ctx with
            (* mthdret *)
            | [] =>
              match Cc with
              | (Ctx0 [[JFInvoke _ _ _ ]]_ None) :: Cc =>
                  Some (h, (Ctx0 [[JFVal1 (JFVLoc l) ]]_ None) :: Cc)
              | _ => None
              end
            (* letgo *)
            | JFCtxLet _ x _ E :: Ctx => Some (h, (Ctx [[substExpr (JFVar x) l E ]]_ None) :: Cc)
            (* ctchnrml *)
            | JFCtxTry _ _ _ _ _ :: Ctx => Some (h, (Ctx [[JFVal1 (JFVLoc l) ]]_ None) :: Cc)
            end
        (* varnpe   *)
        | JFVal2 (JFnull, _) => Some (h, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: Cc)
        (* var *)
        | JFVal2 (JFVLoc (JFLoc n), x) =>
            match Heap.find (elt:=Obj) n h with
            | Some (ro, _) =>
                match JFXIdMap.find (elt:=Loc) x ro with
                | Some l1 => Some (h, (Ctx [[JFVal1 (JFVLoc l1) ]]_ None) :: Cc)
                | None => None
                end
            | None => None
            end
        | JFThrow JFnull => Some (h, (Ctx [[JFVal1 NPE_val ]]_ NPE_mode) :: Cc)
        | JFThrow (JFVLoc (JFLoc n)) =>
            match class h n with
            | Some cname => Some (h, (Ctx [[JFVal1 (JFVLoc (JFLoc n)) ]]_ Some cname) :: Cc)
            | None => None
            end
        | JFTry E1 mu C x E2 => Some (h, Ctx _[ JFCtxTry tt mu C x E2 _[[_ E1 _]]_ None ]_ :: Cc)
        | _ => None
        end
    | _ => None
    end.


Lemma red_is_red2 : forall CC WfCC hfs res, red CC WfCC hfs = res ->
                                       red2 CC WfCC hfs = res.
  intros until 0.
  intro Red.
  destruct hfs.
  destruct f.
  simpl; trivial.
  destruct f.
  destruct A.
  + (* A = Some j *)
    simpl in Red.
    auto_destr_discr Red; simpl; trivial.
  + (* A = None *)
    simpl.
    simpl in Red.
    repeat destr_discr Red; simpl; trivial.
Qed.


Lemma red_eq_red2 : forall CC WfCC hfs, red CC WfCC hfs = red2 CC WfCC hfs.
  intros.
  symmetry.
  apply red_is_red2.
  reflexivity.
Qed.

Lemma red2_is_red : forall CC WfCC hfs res, red2 CC WfCC hfs = res ->
                                       red CC WfCC hfs = res.
  intros.
  now rewrite red_eq_red2.
Qed.

End Jafun.
