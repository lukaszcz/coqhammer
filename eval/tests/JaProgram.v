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
