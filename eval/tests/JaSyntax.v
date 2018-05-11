Require Import Omega.
Require Import String.
Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.

From Hammer Require Import Hammer Reconstr.


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
  +  try hammer_hook "JaSyntax" "JaSyntax.find_class_decompose_program.subgoal_1". 
     exists [], P; auto.
  +  try hammer_hook  "JaSyntax" "JaSyntax.find_class_decompose_program.subgoal_2". 
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
