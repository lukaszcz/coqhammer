Require Import String.
Require Import NPeano.
Require Import PeanoNat.
Require Import Coq.Strings.Ascii.
Require FMapWeakList.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Lists.List.
Import ListNotations.
Require Import JaSyntax.
Require Import JaProgram.
Require Import JaSubtype.
Require Import JaTactics.
Open Scope list_scope.
Open Scope nat_scope.

From Hammer Require Import Hammer Reconstr.

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

Require Import Coq.Structures.Equalities.

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

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

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
