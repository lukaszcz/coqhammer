exception HammerError of string
exception HammerFailure of string
exception HammerTacticError of string

let msg_error s = Feedback.msg_notice (Pp.str s)

let catch_errors (f : unit -> 'a) (g : exn -> 'a) =
  try
    f ()
  with
  | Sys.Break ->
     raise Sys.Break
  | e ->
     g e

let try_bind_fun (x : 'a) (f : 'a -> 'b) (g : Pp.t -> 'b) =
  try
    f x
  with
  | HammerError(msg) ->
     g (Pp.str @@ "Hammer error: " ^ msg)
  | HammerFailure(msg) ->
     g (Pp.str @@ "Hammer failed: " ^ msg)
  | HammerTacticError(msg) ->
     g (Pp.str msg)
  | Failure s ->
     g (Pp.str @@ "CoqHammer bug: please report: " ^ s)
  | Sys.Break ->
     raise Sys.Break
  | CErrors.UserError(_, p) ->
     g p
  | e ->
     g (Pp.str @@ "CoqHammer bug: please report: " ^ Printexc.to_string e)

let try_fun f g = try_bind_fun () f g

let try_cmd (f : unit -> unit) =
  try_fun f (fun p -> Feedback.msg_notice p)

let try_bind_tactic (f : 'a -> unit Proofview.tactic) (x : 'a) : unit Proofview.tactic =
  try_bind_fun x f (fun p -> Tacticals.New.tclZEROMSG p)

let try_tactic (f : unit -> unit Proofview.tactic) : unit Proofview.tactic =
  try_fun f (fun p -> Tacticals.New.tclZEROMSG p)

let try_goal_tactic f =
  Proofview.Goal.enter
    begin fun gl ->
      try_tactic (fun () -> f gl)
    end

let try_goal_tactic_nofail f =
  Proofview.Goal.enter
    begin fun gl ->
      try_fun (fun () -> f gl)
        (fun p -> Feedback.msg_notice p; Proofview.tclUNIT ())
    end
