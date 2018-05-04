Require Import JaSyntax.
Require Import String.
Require Import Lists.List.
Import ListNotations.
Open Scope list_scope.
Require Import NPeano.
Require Import PeanoNat.
Require Export Arith.
Open Scope nat_scope.

From Hammer Require Import Hammer Reconstr.

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
  * intros.
    destruct a.
    destruct (JFClassName_dec D D0).
    ** subst.
       rewrite map_cons.
       unfold is_class_name.
       destruct (JFClassName_dec D0 D0); try contradiction.
       rewrite count_occ_cons_eq; auto. 
       auto with zarith.
    ** rewrite map_cons.
       unfold is_class_name.
       destruct (JFClassName_dec D0 D); subst; try contradiction.
       rewrite count_occ_cons_neq; auto.
       fold (is_class_name D).
       apply IHP;eauto.
       eapply program_contains_further_neq;eauto.
Qed.

(** The property to check that class name [cname] occurs only once in the program [P]. *)
Definition name_once (P:JFProgram) (cname:JFClassName) :=
 count_occ Bool.bool_dec (map (is_class_name cname) P) true = 1%nat.

Lemma in_head_not_in_tail:
  forall (P:JFProgram) (cname:JFClassName) (cdecl:JFClassDeclaration),
    (is_class_name cname cdecl) = true ->
    name_once (cdecl :: P) cname -> ~ name_once P cname.
Proof.
  induction P.
  * intros.
    compute.
    intro.
    discriminate H1.
  * intros.
    unfold name_once in H0.
    rewrite map_cons in H0.
    rewrite H in H0.
    rewrite count_occ_cons_eq in H0.
    set (XX := (count_occ Bool.bool_dec (map (is_class_name cname) (a :: P)) true)) in H0.
    injection H0.
    intros.
    unfold XX in *.
    intro.
    unfold name_once in H2.
    rewrite H1 in H2.
    discriminate H2.
    auto.
Qed.

Lemma name_once_further:
  forall C D P ex fields methods,
  C<>D ->
  name_once (JFCDecl C ex fields methods :: P) D -> name_once P D.
Proof.
  intros.
  unfold name_once in H0.
  rewrite map_cons in H0.
  rewrite is_class_name_neq in H0.
  rewrite count_occ_cons_neq in H0.
  auto.
  auto.
  auto.
Qed.

Lemma name_once_further_neq:
  forall C D P ex ms fs,
    C <> D ->
    name_once P D ->
    name_once (JFCDecl C ex ms fs :: P) D.
Proof.
  intros.
  unfold name_once in *.
  rewrite map_cons.
  rewrite is_class_name_neq; auto.
Qed.

Lemma name_once_further_eq:
  forall C P ex fields methods,
    count_occ Bool.bool_dec (map (is_class_name C) P) true = 0%nat ->
    name_once (JFCDecl C ex fields methods :: P) C.
Proof.
  unfold name_once.
  intros.
  rewrite map_cons.
  rewrite is_class_name_name.
  rewrite count_occ_cons_eq; auto.
Qed.

Lemma count_occ_zero_is_class_name_false:
  forall P cname cdecl,
    count_occ Bool.bool_dec (map (is_class_name cname) P) true = 0%nat ->
    In cdecl P ->
    is_class_name cname cdecl = false.
Proof.
  induction P.
  * intros.
    unfold In in H0.
    tauto.
  * intros.
    apply in_inv in H0.
    destruct H0.
    - rewrite H0 in *.
      rewrite map_cons in H.
      apply <- count_occ_not_In in H.
      apply not_in_cons in H.
      destruct H.
      destruct (is_class_name cname cdecl).
      + tauto.
      + auto.
    - apply IHP.
      rewrite map_cons in H.
      assert (is_class_name cname a <> true).
      apply <- count_occ_not_In in H.
      apply not_in_cons in H.
      intuition.
      rewrite <- (count_occ_cons_neq  Bool.bool_dec (map (is_class_name cname) P) H1).
      auto.
      trivial.
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
  intros.
  unfold decl_once.
  apply name_once_further_eq.
  auto.
Qed.

Lemma decl_in_head_not_in_tail:
  forall (P:JFProgram) (cname:JFClassName) (cdecl:JFClassDeclaration),
    (is_class_name cname cdecl) = true ->
    (decl_once (cdecl :: P) cdecl) ->
    ~ (decl_once P cdecl).
Proof.
  intros.
  unfold decl_once in *.
  destruct cdecl.
  unfold is_class_name in H.
  destruct (JFClassName_dec D cname).
  rewrite e in *.
  apply (in_head_not_in_tail P cname (JFCDecl cname ex fields methods)).
  apply is_class_name_name.
  auto.
  discriminate H.
Qed.



Lemma decl_in_head_false_in_tail:
  forall (P:JFProgram) (cname:JFClassName) (cdecl:JFClassDeclaration),
    (is_class_name cname cdecl) = true ->
    (decl_once (cdecl :: P) cdecl) ->
    Forall (fun x0 => is_class_name cname x0 = false) P.
Proof.
  intros.
  unfold decl_once in *.
  destruct cdecl.
  apply is_class_name_equal in H.
  rewrite H in *.
  unfold name_once in H0.
  rewrite map_cons in H0.
  rewrite is_class_name_name in H0.
  rewrite count_occ_cons_eq in H0; auto.
  injection H0; intros.
  apply Forall_forall.
  intros.
  eapply count_occ_zero_is_class_name_false; try apply H1; auto.
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
  destruct cdecl.
  apply is_class_name_equal in H0.
  rewrite H0 in *.
  eapply name_once_further.
  apply is_class_name_nequal in H1.
  apply H1.
  apply H.
Qed.
  
(** The property that all class names occur in the program uniquely. *)
Definition names_unique (P:JFProgram) :=
  Forall (decl_once P) P.

Lemma names_unique_zero:
  forall P D ex fields methods,
    names_unique (JFCDecl D ex fields methods :: P) ->
    count_occ Bool.bool_dec (map (is_class_name D) P) true = 0%nat.
Proof.
  intros.
  unfold names_unique in H.
  apply Forall_inv in H.
  unfold decl_once in H.
  unfold name_once in H.
  rewrite map_cons in H.
  rewrite is_class_name_name in H.
  rewrite count_occ_cons_eq in H; auto.
Qed.

Lemma names_unique_compose:
  forall P C ex ms fs,
    count_occ Bool.bool_dec (map (is_class_name C) P) true = 0%nat ->
    names_unique P ->
    names_unique (JFCDecl C ex ms fs::P).
Proof.
  intros.
  unfold names_unique.
  apply Forall_cons.
  + apply count_occ_zero_decl_once.
    auto.
  + apply Forall_forall.
    intros.
    unfold names_unique in H0.
    assert (forall y, In y P -> (decl_once P) y).
    apply (Forall_forall (decl_once P) P).
    auto.
    destruct x.
    assert (is_class_name C (JFCDecl D ex0 fields methods) = false).
    eapply count_occ_zero_is_class_name_false.
    apply H.
    auto.
    apply (is_class_name_nequal) in H3.
    unfold decl_once.
    apply name_once_further_neq; auto.
    assert (decl_once P (JFCDecl D ex0 fields methods)).
    apply H2; auto.
    unfold decl_once in H4; auto.
Qed.

Lemma names_unique_further:
  forall (P:JFProgram) (cdecl:JFClassDeclaration),
    names_unique (cdecl::P) ->
    names_unique P.
Proof.
  intros.
  unfold names_unique in H.
  inversion H.
  unfold names_unique.
  assert (forall x, In x P -> (decl_once P) x).
  intros.
  assert (forall x, In x P -> (decl_once (cdecl :: P)) x).
  apply -> (Forall_forall (decl_once (cdecl :: P)) P).
  auto.
  assert (decl_once (cdecl :: P) x0).
  apply H5.
  auto.
  destruct cdecl.
  apply (decs_once_monotone P (JFCDecl D ex fields methods) x0 D).
  auto.
  unfold is_class_name.
  destruct (JFClassName_dec D D).
  auto.
  tauto.
  assert (Forall (fun x0 => is_class_name D x0 = false) P).
  apply (decl_in_head_false_in_tail P D (JFCDecl D ex fields methods)).
  unfold is_class_name.
  destruct (JFClassName_dec D D);auto.
  auto.
  assert (forall x, In x P -> (is_class_name D x = false)).
  apply Forall_forall.
  auto.
  apply H8.
  auto.
  apply Forall_forall.
  auto.
Qed.

Lemma names_unique_decompose_program:
  forall (P1 P2:JFProgram),
    names_unique (P1 ++ P2) ->
    names_unique P2.
Proof.
  induction P1.
  + intros.
    simpl in *.
    auto.
  + intros.
    simpl in H.
    unfold names_unique in H.
    apply IHP1.
    unfold names_unique.
    assert (forall x, In x (a :: P1 ++ P2) -> (decl_once (a :: P1 ++ P2)) x)
      by (apply -> Forall_forall;auto).
    apply <- Forall_forall.
    intros.
    destruct (JFClassName_dec (name_of_cd a) (name_of_cd x)).
    ++ subst.
       assert (decl_once (a :: P1 ++ P2) a) by eauto using in_eq.
       assert (decl_once (a :: P1 ++ P2) x).
       {
         unfold decl_once.
         unfold decl_once in H2.
         destruct x.
         destruct a.
         simpl in e.
         rewrite <- e.
         auto.
       }
       assert (decl_once (x :: P1 ++ P2) x).
       {
         unfold decl_once.
         unfold decl_once in H3.
         destruct x.
         destruct a.
         simpl in e.
         rewrite e in H3.
         unfold name_once.
         unfold name_once in H3.
         simpl in H3.
         simpl.
         auto.
       }
       assert (~ decl_once (P1 ++ P2) x).
       {
         apply (decl_in_head_not_in_tail (P1 ++ P2) (name_of_cd x)).
         apply is_class_name_name_cd; auto.
         auto.
       } 
       destruct x.
       assert (In (is_class_name D (JFCDecl D ex fields methods))
                  (map (is_class_name D) (P1 ++ P2))) by eauto using in_map.
       assert (count_occ Bool.bool_dec (map (is_class_name D) (P1 ++ P2))
                         (is_class_name D (JFCDecl D ex fields methods)) > 0)
         by (apply count_occ_In; eauto).
       unfold decl_once in H4.
       unfold name_once in H4.
       simpl in H4.
       simpl in H7.
       destruct (JFClassName_dec D D);try contradiction.
       destruct (Bool.bool_dec true true);try contradiction.
       injection H4;intros.
       rewrite H8 in H7.
       apply gt_irrefl in H7.
       contradiction.
    ++ eapply decs_once_monotone.
       apply H0.
       apply in_cons;auto.
       apply is_class_name_name_cd.
       unfold is_class_name.
       destruct x.
       destruct (JFClassName_dec D (name_of_cd a)).
       +++ rewrite <-  e in n.
           simpl in n.
           contradiction.
       +++ trivial.
Qed.

Lemma names_unique_further_further:
  forall (P:JFProgram) (cdecl ddecl:JFClassDeclaration),
    names_unique (cdecl::ddecl::P) ->
    names_unique (cdecl::P).
Proof.
  intros.
  destruct cdecl.
  apply  names_unique_compose.
  - apply (names_unique_zero P D ex fields methods).
    apply (names_unique_compose).
    assert (count_occ Bool.bool_dec (map (is_class_name D) (ddecl :: P)) true = 0).
    apply (names_unique_zero (ddecl :: P) D ex fields methods).
    auto.
    rewrite map_cons in H0.
    destruct (is_class_name D ddecl).
    rewrite count_occ_cons_eq in H0; discriminate H0; auto.
    rewrite count_occ_cons_neq in H0; auto.
    eauto using names_unique_further.
  - eauto using names_unique_further.
Qed.

Lemma count_zero_count_nzero:
  forall CC cname ex fields methods,
         count_occ JFClassDeclaration_dec CC
         (JFCDecl cname ex fields methods) > 0 ->
         count_occ Bool.bool_dec (map (is_class_name cname) CC) true = 0 ->
         False.
Proof.
  induction CC; intros.
  - rewrite count_occ_nil in H.
    assert (0<>0).
    apply Lt.lt_0_neq.
    auto.
    tauto.
  - destruct a.
    destruct (JFClassName_dec D cname).
    + rewrite e in *.
      rewrite map_cons in H0.
      rewrite is_class_name_name in H0.
      rewrite count_occ_cons_eq in H0.
      discriminate H0.
      auto.
    + rewrite map_cons in H0.
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
  induction P.
  + intros.
    simpl in H0.
    discriminate H0.
  + intros.
    destruct a.
    destruct (JFClassName_dec cname D).
    ++ subst.
       simpl in H1.
       simpl in H0.
       destruct (string_dec D D); try contradiction.
       rewrite H0 in *.
       injection H1.
       tauto.
    ++ apply find_class_further_neq in H0; auto.
       apply find_class_further_neq in H1; auto.
       eapply IHP;eauto using names_unique_further.
Qed.
  
Hint Resolve names_unique_zero names_unique_compose names_unique_further names_unique_further_further names_unique_decompose_program count_zero_count_nzero is_class_name_name is_class_name_name_cd names_unique_find_class_unique : myhints.
     
Lemma in_names_unique_eq:
  forall CC cname ex fields methods ex0 fields0 methods0,
    In (JFCDecl cname ex fields methods)
       (JFCDecl cname ex0 fields0 methods0 :: CC) ->
    names_unique  (JFCDecl cname ex0 fields0 methods0 :: CC) ->
    (ex = ex0 /\ fields = fields0 /\ methods = methods0).
Proof.
  intros.
  simpl in H.
  destruct H.
  - injection H; auto.
  - apply -> (count_occ_In JFClassDeclaration_dec) in H.
    apply names_unique_zero in H0.
    clear -H H0.
    auto with zarith.
    assert False by eauto with myhints.
    tauto.
Qed.

Hint Resolve  in_names_unique_eq : myhints.

Lemma in_find_class_raw:
  forall CC cname ex fields methods,
    In (JFCDecl cname ex fields methods) CC ->
    exists ex1 fields1 methods1,
    find_class CC cname = Some (JFCDecl cname ex1 fields1 methods1).
Proof.
  induction CC.
  * intros.
    inversion H.
  *  intros.
     destruct (JFClassDeclaration_dec (JFCDecl cname ex fields methods) a).
     ** rewrite <- e.
        simpl.
        destruct (JFClassName_dec cname cname); try contradiction.
        clear.
        do 3 eexists.
        auto.
     ** simpl.
        destruct a.
        destruct (JFClassName_dec D cname).
        *** subst.
            clear. do 3 eexists. auto.
        *** eapply IHCC.
            eapply in_inv in H.
            destruct H.
            + injection H;intros;clear H.
              contradiction.
            + eauto.
Qed.    

Lemma in_find_class:
  forall CC cname ex fields methods,
    names_unique CC ->
    In (JFCDecl cname ex fields methods) CC ->
    find_class CC cname = Some (JFCDecl cname ex fields methods).
Proof.
  induction CC;intros.
  - assert (~ In (JFCDecl cname ex fields methods) []) by  auto using in_nil.
    tauto.
  - destruct (JFClassDeclaration_dec (JFCDecl cname ex fields methods) a).
    + rewrite <- e. simpl.
      destruct (JFClassName_dec cname cname); eauto.
      tauto.
    + destruct a.
      simpl.
      destruct (JFClassName_dec D cname).
      rewrite e in *.
      assert (ex = ex0 /\ fields = fields0 /\ methods = methods0)
        by eauto with myhints.
      decompose [and] H1; clear H1.
      congruence.
      apply in_inv in H0.
      destruct H0.
      injection H0;intros.
      tauto.
      eapply IHCC; eauto with myhints.
Qed.


Lemma names_unique_neq_but_in:
  forall CC cdecl ddecl,
         In cdecl (cdecl :: CC) ->
         ddecl <> cdecl ->
         names_unique (cdecl :: CC) ->
         In ddecl CC -> name_of_cd ddecl <> name_of_cd cdecl.
Proof.
  intros.
  destruct cdecl.
  destruct ddecl.
  simpl.
  assert (count_occ Bool.bool_dec (map (is_class_name D) CC) true = 0) by eauto with myhints.
  assert (count_occ Bool.bool_dec (map (is_class_name D0) CC) true > 0).
  apply count_occ_In.
  assert (names_unique CC) by eauto using names_unique_further.
  unfold names_unique in H4.
  assert (forall x,In x CC -> decl_once CC x) by (apply Forall_forall; auto).
  assert (decl_once CC (JFCDecl D0 ex0 fields0 methods0)) by auto.
  unfold decl_once in H6.
  unfold name_once in H6.
  assert (count_occ Bool.bool_dec (map (is_class_name D0) CC) true >0) by
      try (rewrite H6; apply Gt.gt_Sn_O).
  apply <- count_occ_In; eauto.
  intro.
  rewrite H5 in *.
  rewrite H3 in H4.
  apply (Gt.gt_irrefl 0 H4).
Qed.
  

Lemma in_find_class_eq:
  forall CC cdecl cdecl',
    names_unique CC ->
    In cdecl CC ->
    find_class CC (name_of_cd cdecl) = Some cdecl' -> cdecl = cdecl'.
Proof.
  induction CC;intros.
  - assert (~ In cdecl []) by  auto using in_nil.
    tauto.
  - destruct (JFClassDeclaration_dec cdecl a).
    + simpl in H1. rewrite e in *.
      destruct a.
      simpl in H1.
      destruct (JFClassName_dec D D);
      try injection H1;
      tauto.
    + assert (names_unique CC) by eauto using names_unique_further.
      assert (a = cdecl \/ In cdecl CC) by eauto.
      destruct H3. symmetry in H3. contradiction.
      assert (name_of_cd cdecl <> name_of_cd a).
      apply (names_unique_neq_but_in CC a cdecl); auto.
      auto using in_eq.
      assert (find_class CC (name_of_cd cdecl) = Some cdecl').
      destruct a.
      eapply find_class_further_neq.
      simpl in H4.
      assert (D <> name_of_cd cdecl) by auto.
      eauto.
      eauto.
      apply IHCC; auto.
Qed.


Hint Resolve in_find_class : myhints.

