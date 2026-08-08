(* Regression tests for the decoding of the premise names an ATP reports back.
   The names come from tptp_out, and recovering the Coq constant behind one is
   prefix and suffix surgery on hardcoded offsets, so a change to the emitted
   naming scheme silently mis-attributes premises rather than failing loudly.
   Checking it end-to-end would need the external provers installed; these cases
   pin the decoding itself, offline and per prover-independent. *)

let failures = ref 0

let report label expected actual =
  incr failures;
  Printf.eprintf "FAIL %s: expected [%s], got [%s]\n" label expected actual

let check_strings label expected actual =
  if expected <> actual then
    report label (String.concat "; " expected) (String.concat "; " actual)

let check_pairs label expected actual =
  let show l = String.concat "; " (List.map (fun (x, y) -> x ^ "/" ^ y) l) in
  if expected <> actual then report label (show expected) (show actual)

let check_string label expected actual =
  if expected <> actual then report label expected actual

(* The names a split axiom set produces: a definition split over its conjuncts,
   a case axiom split over its constructors and its linking axiom, and a lifted
   lambda.  Only the constant each one belongs to may survive the decoding. *)
let split_axiom_names =
  [ "$_def_$_lam_1$Corelib.Init.Datatypes.O";
    "$_def_$_case_Corelib.Init.Datatypes.nat$2$O";
    "$_def_Corelib.Init.Nat.add$S";
    "$_case_Corelib.Init.Datatypes.nat$2$O";
    "$_case_Corelib.Init.Datatypes.nat$2$link";
    "$_case_$_case_Corelib.Init.Datatypes.nat$3$O";
    "$_typeof_extraction_deptypes.h$conj";
    "$_typeof_extraction_deptypes.h";
    "$_def_extraction_deptypes.h$conj" ]

let () =
  check_strings "defs"
    [ "Corelib.Init.Nat.add"; "extraction_deptypes.h" ]
    (Atp_names.get_defs split_axiom_names);
  check_strings "typings"
    [ "extraction_deptypes.h" ]
    (Atp_names.get_typings split_axiom_names);
  check_strings "cases"
    [ "Corelib.Init.Datatypes.nat" ]
    (Atp_names.get_cases split_axiom_names);
  (* A lifted lambda and a case axiom are not premises the user can be shown,
     so nothing in the set counts as a plain dependency. *)
  check_strings "deps" [] (Atp_names.get_deps split_axiom_names)

(* A case axiom may nest: the subject is the innermost name, whatever the depth. *)
let () =
  check_strings "nested cases"
    [ "Corelib.Init.Datatypes.nat" ]
    (Atp_names.get_cases [ "$_case_$_case_Corelib.Init.Datatypes.nat$3$O" ]);
  check_string "nested case subject" "Corelib.Init.Datatypes.nat"
    (Atp_names.case_name_subject
       "$_case_$_case_Corelib.Init.Datatypes.nat$3$O");
  (* A name carrying no subject must not be mistaken for one. *)
  check_string "subjectless case" "$none" (Atp_names.case_name_subject "$2$O")

(* A definition axiom that was not split keeps its name whole, and one that was
   loses only the suffix -- never a leading segment of the constant. *)
let () =
  check_string "unsplit name" "Foo.bar" (Atp_names.strip_dollar_suffix "Foo.bar");
  check_string "split name" "Foo.bar"
    (Atp_names.strip_dollar_suffix "Foo.bar$conj");
  check_strings "unsplit def" [ "Foo.bar" ]
    (Atp_names.get_defs [ "$_def_Foo.bar" ])

(* The constructor-derived axioms carry their own prefixes. *)
let () =
  check_strings "inversions" [ "Foo.tree" ]
    (Atp_names.get_inversions [ "$_inversion_Foo.tree"; "$_def_Foo.bar" ]);
  check_strings "injections" [ "Foo.N" ]
    (Atp_names.get_injections [ "$_inj_Foo.N"; "$_case_Foo.tree$2$L" ]);
  check_pairs "discrims" [ ("Foo.L", "Foo.N") ]
    (Atp_names.get_discrims [ "$_discrim_Foo.L$Foo.N"; "$_def_Foo.bar" ])

(* Internal names the translation invents are not premises to report. *)
let () =
  check_strings "internal names dropped" []
    (Atp_names.get_defs [ "$_def__HAMMER_bogus"; "$_def_$anonymous" ]);
  check_strings "duplicates collapsed" [ "Foo.bar" ]
    (Atp_names.get_defs [ "$_def_Foo.bar$conj"; "$_def_Foo.bar$S" ])

let () =
  if !failures > 0 then
    begin
      Printf.eprintf "%d ATP premise-name check(s) failed\n" !failures;
      exit 1
    end
  else
    print_endline "ATP premise-name checks passed"
