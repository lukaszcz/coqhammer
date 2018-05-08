Require Import String.
Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Lists.List.
Import ListNotations.
Require Import JaSyntax.
Require Import JaProgram.
Open Scope list_scope.
Require Import NPeano.
Require Import PeanoNat.
Open Scope nat_scope.
Require Coq.Program.Equality.

From Hammer Require Import Hammer Reconstr.

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
  hammer_hook "JaSubtype" "JaSubtype.extends_neq". Undo.
  intros.
  destruct H0, H0.
  decompose [and] H0; clear H0.
  eapply extends_in_second_second  in H4; [idtac | reflexivity].
  hammer_hook "JaSubtype" "JaSubtype.extends_neq.subgoal_1". Undo.
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
    hammer_hook "JaSubtype" "JaSubtype.extends_neq_none.subgoal_1". Undo.
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
    hammer_hook "JaSubtype" "JaSubtype.extends_equals_first.subgoal_1". Undo.
    assert (forall x, In x P -> decl_once P x).
    assert (names_unique P).
    hammer_hook "JaSubtype" "JaSubtype.extends_equals_first.assert_1". Undo.
    Reconstr.hobvious (@Nuq)
                      (@JaProgram.names_unique_further)
                      (@JaSyntax.JFProgram).
    hammer_hook "JaSubtype" "JaSubtype.extends_equals_first.subgoal_1_1". Undo.
    Reconstr.hobvious (@H)
                      (@Coq.Lists.List.Forall_forall)
                      Reconstr.Empty.
    hammer_hook "JaSubtype" "JaSubtype.extends_equals_first.subgoal_1_2". Undo.
    pose extends_in_first; scrush.
Qed.

Lemma names_unique_extends_non_refl:
  forall P C D,
    names_unique P -> extends P C D -> C <> D.
Proof.
  intros P C D Nuq H.
  induction H.
  + hammer_hook "JaSubtype" "JaSubtype.names_unique_extends_non_refl.subgoal_1". Undo.
    Reconstr.hcrush Reconstr.AllHyps
                    (@JaProgram.names_unique_zero, @JaProgram.is_class_name_name,
                     @JaProgram.count_occ_zero_is_class_name_false)
                    Reconstr.Empty.
  + hammer_hook "JaSubtype" "JaSubtype.names_unique_extends_non_refl.subgoal_2". Undo.
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
  hammer_hook "JaSubtype" "JaSubtype.number_of_extends_decompose". Undo.
  intros.
  unfold number_of_extends in H.
  destruct (JFClassName_dec C C).
  + fold (number_of_extends P ex) in H.
    destruct (number_of_extends P ex).
    ++ hammer_hook "JaSubtype" "JaSubtype.number_of_extends_decompose.subgoal_1". Undo.
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
  * hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class_simple.subgoal_2". Undo.
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
  hammer_hook "JaSubtype" "JaSubtype.names_unique_number_of_extends_loop". Undo.
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
  + hammer_hook "JaSubtype" "JaSubtype.is_class_and_occ_zero.subgoal_2". Undo.
    intros.
    destruct a.
    assert ({C=D} + {C<>D}) by apply JFClassName_dec.
    destruct H2.
    * hammer_hook "JaSubtype" "JaSubtype.is_class_and_occ_zero.subgoal_2_1". Undo.
      rewrite e in *.
      rewrite map_cons in H1.
      unfold is_class_name in H1.
      destruct (JFClassName_dec D0 D).
      - scrush.
      - hammer_hook "JaSubtype" "JaSubtype.is_class_and_occ_zero.subgoal_2_1_1". Undo.
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
  hammer_hook "JaSubtype" "JaSubtype.names_unique_in_neq". Undo.
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
    * hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.subgoal_2". Undo.
      rewrite e in *. (* D = D0 *)
      assert (C<>D0) by scrush.
      unfold names_unique in H.
      assert (forall x, In x (JFCDecl C (Some D0) fields methods
         :: JFCDecl D0 ex fields0 methods0 :: P) ->  (decl_once
           (JFCDecl C (Some D0) fields methods
                    :: JFCDecl D0 ex fields0 methods0 :: P)) x).
      hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.assert_1". Undo.
      apply Forall_forall; auto.
      assert (decl_once
         (JFCDecl C (Some D0) fields methods
                  :: JFCDecl D0 ex fields0 methods0 :: P)
         (JFCDecl D0 ex fields0 methods0)).
      hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.assert_2". Undo.
      apply H2; sauto.
      exists (JFCDecl D0 ex fields0 methods0).
      scrush.
    * assert ({C=D} + {C<>D}) by apply JFClassName_dec.
      destruct H1.
      + scrush.
      + hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.subgoal_3_1". Undo.
        assert (exists CC0 : JFClassDeclaration,
                  find_class (JFCDecl C (Some D) fields methods :: P) D =
                  Some CC0).
        hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.assert_3". Undo.
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
        hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.assert_4". Undo.
        Reconstr.hobvious (@H0)
                (@Coq.Arith.PeanoNat.Nat.sub_1_r, @Coq.Arith.PeanoNat.Nat.succ_pred, @Coq.Arith.PeanoNat.Nat.neq_0_lt_0, @Coq.Arith.PeanoNat.Nat.add_1_r)
                Reconstr.Empty.
        scrush.
        hammer_hook "JaSubtype" "JaSubtype.number_of_extends_find_class.subgoal_3_2". Undo.
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
  - hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_further.subgoal_2". Undo.
    lapply (H0 C0 CC); intros.
    destruct H4.
    exists x.
    scrush.
    scrush.
  - hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_further.subgoal_3". Undo.
    assert ( exists n : nat,
               number_of_extends (JFCDecl D None fields methods :: P) C0 = Some n).
    hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_further.assert_1". Undo.
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
  + hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_decompose_program.subgoal_2". Undo.
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
  + hammer_hook "JaSubtype" "JaSubtype.subtype_get_superclass.subgoal_2". Undo.
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
    hammer_hook "JaSubtype" "JaSubtype.subtype_get_superclass.assert_1". Undo.
    Reconstr.hobvious (@H0)
                      (@JaSyntax.find_class_eq)
                      Reconstr.Empty.
    destruct H7.
    rewrite H5 in *.
    hammer_hook "JaSubtype" "JaSubtype.subtype_get_superclass.subgoal_2_1". Undo.
    Reconstr.hcrush (@H, @H7)
                    (@number_of_extends_find_class)
                    (@JaSyntax.JFProgram).
    scrush.
    simpl.
    destruct (JFClassName_dec D ex).
    exists (JFCDecl D ex0 fields0 methods0).
    auto.
    hammer_hook "JaSubtype" "JaSubtype.subtype_get_superclass.subgoal_2_2". Undo.
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
    ++ hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_superclass.subgoal_1". Undo.
       subst.
       unfold subtype_well_founded in H.
       simpl in H1.
       assert (exists n : nat, number_of_extends (JFCDecl C ex0 fields0 methods0 :: P) C = Some n).
       hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_superclass.assert_1". Undo.
       Reconstr.hobvious (@H)
                         (@JaSyntax.find_class_eq)
                         Reconstr.Empty.
       scrush.
    ++ hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_superclass.subgoal_2". Undo.
       eapply IHP; eauto.
       eapply subtype_well_founded_further.
       scrush.
       scrush.
       hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_superclass.subgoal_2_1". Undo.
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
      hammer_hook "JaSubtype" "JaSubtype.find_class_extends.subgoal_1". Undo.
      injection H;intros;clear H;subst.
      destruct D.
      assert (dname=D) by eauto using find_class_eq_name.
      subst.
      eapply find_class_in in H0.
      apply in_inv in H0.
      destruct H0.
      +++ scrush.
      +++ hammer_hook "JaSubtype" "JaSubtype.find_class_extends.subgoal_1_1". Undo.
          Reconstr.reasy (@base, @Coq.Init.Peano.f_equal_nat) Reconstr.Empty.
    ++ (* D0 <> cname *)
      apply ind.
      hammer_hook "JaSubtype" "JaSubtype.find_class_extends.subgoal_2". Undo.
      assert (exists P0 P1,
                 P = P0 ++ ((JFCDecl name (Some dname) fields methods) :: P1)).
      hammer_hook "JaSubtype" "JaSubtype.find_class_extends.assert_1". Undo.
      Reconstr.reasy (@JaSyntax.find_class_decompose_program) (@JaSyntax.JFProgram).
      destruct H4 as [P0 [P1 H4]].
      rewrite H4 in *.
      assert (exists D', find_class
                           (JFCDecl name (Some dname) fields methods ::P1)
                           dname = Some D').
      hammer_hook "JaSubtype" "JaSubtype.find_class_extends.assert_2". Undo.
      {
        rewrite app_comm_cons in H1.
        assert (subtype_well_founded
                  (JFCDecl name (Some dname) fields methods :: P1)).
        hammer_hook "JaSubtype" "JaSubtype.find_class_extends.assert_3". Undo.
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
      hammer_hook "JaSubtype" "JaSubtype.find_class_extends.assert_4". Undo.
      Reconstr.reasy (@JaSyntax.find_class_lift) (@JaSyntax.JFProgram).
      hammer_hook "JaSubtype" "JaSubtype.find_class_extends.subgoal_2_1". Undo.
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
    - hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1". Undo.
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
      hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.assert_1". Undo.
      apply H2.
      + hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_1". Undo.
        eapply subtype_well_founded_further.
        apply H.
        apply H0.
      + hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_2". Undo.
        Reconstr.reasy (@JaSyntax.find_class_eq) Reconstr.Empty.
      + hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_3". Undo.
        Reconstr.reasy (@JaSyntax.program_contains_further) (@JaSyntax.JFClassName, @JaSyntax.JFProgram).
      + hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_4". Undo.
        Reconstr.reasy (@JaProgram.names_unique_further) (@JaSyntax.JFProgram).
      + hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_5". Undo.
        assert (program_contains P JFObjectName = true).
        hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.assert_2". Undo.
        apply (IHP name cl).
        hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_5_1". Undo.
        Reconstr.reasy (@JaProgram.names_unique_further) (@JaSyntax.JFProgram).
        hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_5_2". Undo.
        Reconstr.reasy (@subtype_well_founded_further) Reconstr.Empty.
        scrush.
        hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_contains_object.subgoal_1_5_3". Undo.
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
  * hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_program_contains_further.subgoal_1". Undo.
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
       hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_program_contains_further.assert_1". Undo.
       eapply H1.
       eapply find_class_same;eauto 2.
       apply find_class_eq.
       unfold number_of_extends in H3.
       destruct ex.
       *** scrush.
       *** scrush.
    ** hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_program_contains_further.subgoal_1_1". Undo.
       eapply program_contains_further_neq; eauto.
  * hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_program_contains_further.subgoal_2". Undo.
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
  hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_neq.subgoal_0". Undo.
  lapply H0;intros.
  + hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_neq.subgoal_1". Undo.
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
  + hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_find_class_neq.subgoal_1". Undo.
    intros.
    destruct a.
    simpl in H1.
    destruct (JFClassName_dec D name).
    ++ hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_find_class_neq.subgoal_1_1". Undo.
       Reconstr.rcrush (@subtype_well_founded_neq) Reconstr.Empty.
    ++ hammer_hook "JaSubtype" "JaSubtype.subtype_well_founded_find_class_neq.subgoal_1_2". Undo.
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
  + hammer_hook "JaSubtype" "JaSubtype.extends_further_object.subgoal_1". Undo.
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
  * hammer_hook "JaSubtype" "JaSubtype.subtyping_further.subgoal_1". Undo.
    eapply (substep (E :: P) C D E0).
    + scrush.
    + scrush.
    + inversion H1.
      - destruct E.
        hammer_hook "JaSubtype" "JaSubtype.subtyping_further.subgoal_1_1". Undo.
        Reconstr.reasy (@ind) Reconstr.Empty.
      - destruct E.
        hammer_hook "JaSubtype" "JaSubtype.subtyping_further.subgoal_1_2". Undo.
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
    + hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.subgoal_1". Undo.
      Reconstr.reasy (@JaProgram.names_unique_further) (@object_not_extended, @JaSyntax.JFProgram).
    + scrush.
    + scrush.
    + inversion H2.
      - scrush.
      - scrush.
      - unfold object_is_not_extended in H0.
        hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.subgoal_2". Undo.
        { inversion H5.
          + hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.subgoal_2_1". Undo.
            rewrite H11 in *.
            apply Forall_inv in H0.
            rewrite <- H10 in *.
            unfold object_not_extended in H0.
            lapply H0; intros; clear H0.
            discriminate H15.
            unfold JFObject in H3.
            congruence.
          +  assert (exists ex0 fields' methods',  In (JFCDecl cname (Some ex0) fields' methods') P).
             hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.assert_1". Undo.
             Reconstr.reasy (@extends_in_first) (@JaSyntax.JFProgram).
             hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.subgoal_2_2". Undo.
             destruct H15, H15, H15.
             assert (forall x, In x (a :: P) -> object_not_extended x).
             hammer_hook "JaSubtype" "JaSubtype.object_is_not_subtype.assert_2". Undo.
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
  + intros.
    unfold program_contains in H.
    discriminate H.
  + induction 5.
    - auto.
    - intro.
      assert (E = JFObject).
      apply (object_is_not_subtype P0);auto.
      rewrite H4.
      auto with myhints.
    - auto with myhints.
    - intro.
      eauto 3 using (substep P0 C D E) with myhints.
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
  intros P C D.
  intro.
  induction H.
  * intros.
    congruence.
  * intros.
    injection H0;intros.
    rewrite H6 in *.
    contradiction.
  * intros.
    discriminate H.
  * intros.
    subst.
    injection H3;intros;clear H3;subst.
    destruct (JFClassName_dec dname dn).
    ** subst.
       destruct P.
       *** inversion H1.
       *** assert (exists
                      (ex : option JFClassName)
                      (fields : list JFFieldDeclaration)
                      (methods : list JFMethodDeclaration),
                      In (JFCDecl dn ex fields methods) P).
           eapply extends_in_second_second;eauto.
           do 3 destruct H.
           exists x, x0, x1.
           eauto using in_cons.
    ** eapply IHsubtyping;eauto.
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
  induction 1.
  - auto with myhints.
  - auto with myhints.
  - auto with myhints.
  - intros.
    eapply substep.
    + eauto with myhints.
    + apply H0.
    + eapply extends_narrower.
      rewrite H4 in H1.
      eauto with myhints.
      congruence.
    + assert (D <> JFClass C0).
      eapply extends_neq.
      rewrite H4 in H3.
      eauto with myhints.
      exists cname,dname.
      rewrite H4 in H1.
      eauto with myhints.
      eapply IHsubtyping.
      * eauto with myhints.
      * eauto with myhints.
      * auto with myhints.
Qed.

Lemma subtyping_not_bot:
  forall P C D,
    subtyping P C D -> D = JFBotClass  -> C = JFBotClass.
Proof.
  induction 1.
  + auto.
  + intros.
    discriminate H.
  + auto.
  + intros.
    lapply IHsubtyping.
    intros.
    subst D.
    discriminate H4.
    auto.
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
  inversion H3.
  + intuition.
  + rewrite H6 in *; tauto.
  + congruence.
  + assert (exists
               (ex0 : JFClassName) (fields' : list JFFieldDeclaration)
               (methods' : list JFMethodDeclaration),
               In (JFCDecl cname (Some ex0) fields' methods') P)
      by eauto using  extends_in_first.
    destruct H11, H11, H11.
    assert (cname=Cid) by congruence.
    subst cname.
    exists (JFCDecl Cid (Some x) x0 x1).
    eauto with myhints.
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
  + intros.
    simpl in H4.
    discriminate H4.
  + intros C D Did CDneq CJFB DidD Nuq Swf PctsObj Sub.
    inversion Sub.
    ++ contradiction.
    ++ subst.
       injection H1;intros.
       subst.
       apply program_contains_find_class;auto.
    ++ subst. contradiction.
    ++ subst.
       destruct a.
       unfold find_class.
       destruct (JFClassName_dec D Did).
       +++ eexists;eauto.
       +++ fold (find_class P Did).
           assert (exists
                      (ex0 : option JFClassName)
                      (fields' : list JFFieldDeclaration)
                      (methods' : list JFMethodDeclaration),
                      In (JFCDecl dname ex0 fields' methods') P)
             by eauto using extends_in_second_second.
           do 3 destruct H.
           destruct (JFClassName_dec D cname).
           * subst.
             destruct (JFClassName_dec cname dname).
             ** subst.
                assert (JFClass dname <> JFClass dname).
                eapply extends_neq;eauto.
                contradiction.
             ** assert (JFClass cname <> JFClass dname) by congruence.
                destruct (JFClassName_dec dname Did).
                *** subst; eauto with myhints.
                *** assert (subtyping P (JFClass dname) (JFClass Did)).
                    eapply subtyping_further_neq ;
                      try apply H2;eauto 2 with myhints.
                    eapply IHP;
                      try apply H3; try apply CDneq;
                        try apply CJFB;try congruence;eauto 2 with myhints.
                    {
                      destruct P.
                      * inversion H.
                      * eauto using subtype_well_founded_program_contains_further with myhints.
                    }
           * subst.
             assert (JFClass dname <> JFClass D).
             eapply extends_neq.
             eauto with myhints.
             exists cname, dname.
             repeat (split;try trivial).
             assert (JFClass D <> JFClass Did) by congruence.
             destruct (JFClassName_dec dname Did).
             ** subst; eauto with myhints.
             ** assert (JFClass dname <> JFClass Did) by congruence.
                eapply IHP; try eapply H4; eauto 2 with myhints.
                *** discriminate.
                *** destruct P.
                    **** inversion H.
                    **** eauto using subtype_well_founded_program_contains_further with myhints.
                *** eapply subtyping_further_neq; eauto.
Qed.

Lemma subtyping_neq_object:
  forall P dname D,
    object_is_not_extended P ->
    (JFClass dname) <> D  ->
    subtyping P (JFClass dname) D ->
    JFClass dname <> JFObject.
Proof.
  intros.
  inversion H1.
  + tauto.
  + congruence.
  + injection.
    eapply object_is_not_extended_extends_neq.
    eauto.
    assert (dname=cname) by congruence.
    rewrite H10 in *.
    eauto.
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
  intros P D E.
  intro.
  induction H.
  * intros.
    congruence.
  * intros.
    contradiction.
  * intros.
    congruence.
  * intros.
    subst.
    injection H5;intros;clear H5.
    subst.
    eapply extends_in_first in H1.
    destruct H1. destruct H.
    eapply in_inv in H.
    destruct H.
    ** congruence.
    ** eapply in_find_class_raw in H.
       do 3 destruct H.
       clear -H.
       firstorder.
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
  * intros.
    inversion H3.
    ** auto.
    ** auto.
    ** subst.
       inversion H6.
  * intros.
    apply IHP;eauto 2 with myhints.
    destruct a.
    destruct (JFCId_dec (JFClass D) JFObject).
    assert (C = JFObject).
    eapply object_is_not_subtype;
      try apply H;eauto with myhints.
    rewrite H4.
    apply subrefl.
    eauto 2 with myhints.
Qed.

Hint Resolve  subtyping_neq_object subtyping_object_supremum : myhints.

Lemma lookup_cons_neq:
  forall P cn dn ex fields methods m md,
    cn <> dn ->
    methodLookup (JFCDecl cn ex fields methods :: P) dn m = Some md ->
    methodLookup  P dn m = Some md.
Proof.
  intros.
  unfold methodLookup in H0.
  fold methodLookup in *.
  destruct (JFClassName_dec dn cn); try congruence.
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
  * intros Nuq Exts mthLkp.
    inversion Exts.
  * intros Nuq Exts mthLkp.
    unfold methodLookup in mthLkp.
    unfold methodLookup.
    fold methodLookup in *.
    destruct a.
    destruct (JFClassName_dec cname D).
    ** destruct (find_method methods m).
       *** exists j. auto.
       *** destruct ex.
           + subst.
             destruct (JFClassName_dec dname D).
             ++ firstorder.
             ++ assert (dname = j) by eauto using extends_equals_first.
                rewrite H in mthLkp.
                firstorder.
           + subst.
             inversion Exts.
             subst.
             assert (count_occ Bool.bool_dec (map (is_class_name D) P) true = 0) by eauto with myhints.
             assert (exists (ex0 : JFClassName) (fields' : list JFFieldDeclaration) (methods' : list JFMethodDeclaration),
                        In (JFCDecl D (Some ex0) fields' methods') P) by eauto using extends_in_first with myhints.
             destruct H0 as [ex0 [fields' [methods' H0]]].
             assert (names_unique P) by eauto 2 with myhints.
             unfold names_unique in H1.
             assert (forall x, In x P -> decl_once P x).
             apply Forall_forall;auto with myhints.
             apply H2 in H0.
             unfold decl_once in H0.
             unfold name_once in H0.
             congruence.
   ** destruct (JFClassName_dec dname D).
      *** subst. clear -Nuq Exts n.
          assert (exists (ex0 : option JFClassName) (fields' : list JFFieldDeclaration) (methods' : list JFMethodDeclaration),
                     In (JFCDecl D ex0 fields' methods') P).
          eapply extends_in_second_second.
          apply Exts.
          eauto with myhints.
          destruct H as [ex0 [fields' [methods' H]]].
          assert (names_unique P) by eauto with myhints.
          unfold names_unique in H0.
          assert (forall x, In x P -> decl_once P x).
          apply Forall_forall;auto with myhints.
          apply H1 in H.
          unfold decl_once in H.
          unfold name_once in H.
          assert (count_occ Bool.bool_dec (map (is_class_name D) P) true = 0) by eauto with myhints.
          congruence.
      *** inversion Exts.
           + subst. contradiction.
           + subst.
             eapply IHP;eauto 2 with myhints.
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
