open Goptions

let predictions_num = ref 1024

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"Predictions"];
      optread=(fun ()->Some !predictions_num);
      optwrite=
   (function
        None -> predictions_num := 128
      |	Some i -> predictions_num := (max i 16))}
  in
  declare_int_option gdopt

let sauto_timelimit = ref 1

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"SAutoLimit"];
      optread=(fun ()->Some !sauto_timelimit);
      optwrite=
   (function
        None -> sauto_timelimit := 1
      |	Some i -> sauto_timelimit := (max i 0))}
  in
  declare_int_option gdopt

let atp_timelimit = ref 20

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"ATPLimit"];
      optread=(fun ()->Some !atp_timelimit);
      optwrite=
   (function
        None -> atp_timelimit := 10
      |	Some i -> atp_timelimit := (max i 0))}
  in
  declare_int_option gdopt

let reconstr_timelimit = ref 5

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"ReconstrLimit"];
      optread=(fun ()->Some !reconstr_timelimit);
      optwrite=
   (function
        None -> reconstr_timelimit := 10
      |	Some i -> reconstr_timelimit := (max i 0))}
  in
  declare_int_option gdopt

let minimize_threshold = ref 8

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"MinimizationThreshold"];
      optread=(fun ()->Some !minimize_threshold);
      optwrite=
   (function
        None -> minimize_threshold := 0
      |	Some i -> minimize_threshold := (max i 0))}
  in
  declare_int_option gdopt

let gs_mode = ref 8

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"GSMode"];
      optread=(fun ()->Some !gs_mode);
      optwrite=
   (function
        None -> gs_mode := 16
      |	Some i -> gs_mode := i)}
  in
  declare_int_option gdopt

let eprover_enabled = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"Eprover"];
      optread=(fun () -> !eprover_enabled);
      optwrite=(fun b -> eprover_enabled := b)}
  in
  declare_bool_option gdopt

let vampire_enabled = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"Vampire"];
      optread=(fun () -> !vampire_enabled);
      optwrite=(fun b -> vampire_enabled := b)}
  in
  declare_bool_option gdopt

let z3_enabled = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"Z3"];
      optread=(fun () -> !z3_enabled);
      optwrite=(fun b -> z3_enabled := b)}
  in
  declare_bool_option gdopt

let cvc4_enabled = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"CVC4"];
      optread=(fun () -> !cvc4_enabled);
      optwrite=(fun b -> cvc4_enabled := b)}
  in
  declare_bool_option gdopt

let predict_path = ref "predict"

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"PredictPath"];
      optread=(fun () -> !predict_path);
      optwrite=(fun s -> predict_path := s)}
  in
  declare_string_option gdopt

let predict_method = ref "knn"

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"PredictMethod"];
      optread=(fun () -> !predict_method);
      optwrite=
        begin fun s ->
          if s = "knn" || s = "nbayes" || s = "rforest" then
            predict_method := s
          else
            Msg.error "Invalid method. Available predict methods: knn, nbayes."
        end}
  in
  declare_string_option gdopt

let parallel_mode = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"Parallel"];
      optread=(fun () -> !parallel_mode);
      optwrite=(fun b -> parallel_mode := b)}
  in
  declare_bool_option gdopt

let debug_mode = ref false

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"Debug"];
      optread=(fun () -> !debug_mode);
      optwrite=(fun b -> debug_mode := b)}
  in
  declare_bool_option gdopt

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"ClosureGuards"];
      optread=(fun () -> !Coq_transl_opts.opt_closure_guards);
      optwrite=(fun b -> Coq_transl_opts.opt_closure_guards := b)}
  in
  declare_bool_option gdopt

let filter_program = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"FilterProgram"];
      optread=(fun () -> !filter_program);
      optwrite=(fun b -> filter_program := b)}
  in
  declare_bool_option gdopt

let filter_classes = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"FilterClasses"];
      optread=(fun () -> !filter_classes);
      optwrite=(fun b -> filter_classes := b)}
  in
  declare_bool_option gdopt

let filter_hurkens = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"FilterHurkens"];
      optread=(fun () -> !filter_hurkens);
      optwrite=(fun b -> filter_hurkens := b)}
  in
  declare_bool_option gdopt

let search_blacklist = ref true

let _ =
  let gdopt=
    { optdepr=false;
      optstage = Interp;
      optkey=["Hammer";"Blacklist"];
      optread=(fun () -> !search_blacklist);
      optwrite=(fun b -> search_blacklist := b)}
  in
  declare_bool_option gdopt

module FilterSet = Set.Make(Names.ModPath)

module HammerFilter = struct
  type t = Names.ModPath.t
  module Set = FilterSet
  let encode env = Nametab.locate_module
  let subst s m = m
  let printer m = Names.DirPath.print (Nametab.dirpath_of_module m)
  let key = ["Hammer"; "Filter"]
  let title = "Hammer Filter"
  let member_message m b =
    Pp.app (printer m)
      (if b then Pp.str " present" else Pp.str "absent")
end

module HammerFilterTable = MakeRefTable(HammerFilter)
