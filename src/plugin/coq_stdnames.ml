(* Recognition of canonical Rocq stdlib constants under their historical
   root prefixes (Corelib / Coq / Stdlib). *)

let is_canonical_constant prefixes basename name =
  List.exists (fun prefix -> name = prefix ^ "." ^ basename) prefixes

let is_init_logic =
  is_canonical_constant
    [ "Corelib.Init.Logic"; "Coq.Init.Logic"; "Stdlib.Init.Logic" ]

let is_init_wf =
  is_canonical_constant
    [ "Corelib.Init.Wf"; "Coq.Init.Wf"; "Stdlib.Init.Wf" ]

let is_init_specif =
  is_canonical_constant
    [ "Corelib.Init.Specif"; "Coq.Init.Specif"; "Stdlib.Init.Specif" ]

let is_jmeq =
  is_canonical_constant
    [ "Corelib.Logic.JMeq"; "Coq.Logic.JMeq"; "Stdlib.Logic.JMeq" ]

let is_program_wf =
  is_canonical_constant
    [ "Corelib.Program.Wf"; "Coq.Program.Wf"; "Stdlib.Program.Wf" ]
