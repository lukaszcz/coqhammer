open Hammer_errors
open Sauto
open Tacopts

let trivial_tacs_batch lst =
  [ (usolve (interp_opts (default_s_opts ()) lst sfirstorder),
     "sfirstorder");
    (usolve (interp_opts (default_s_opts ()) lst scongruence),
     "scongruence")
  ]

let hbest_tacs lst =
  [ (usolve (interp_opts
               (set_quick_opts true
                  (set_eager_opts false (hauto_s_opts ())))
               lst sauto),
     "hauto lq: on");
    (usolve (interp_opts
               (set_quick_opts true (hauto_s_opts ()))
               lst sauto),
     "hauto q: on");
    (usolve (interp_opts
               (set_eager_opts false (hauto_s_opts ()))
               lst sauto),
     "hauto l: on");
    (usolve (interp_opts (hauto_s_opts ()) lst sauto),
     "hauto");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_quick_opts true
                     (set_eager_opts false (hauto_s_opts ()))))
               lst sauto),
     "hauto lqb: on");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_quick_opts true (hauto_s_opts ())))
               lst sauto),
     "hauto qb: on");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_eager_opts false (hauto_s_opts ())))
               lst sauto),
     "hauto lb: on");
    (usolve (interp_opts
               (set_brefl_opts true (hauto_s_opts ()))
               lst sauto),
     "hauto b: on")
  ]

let sbest_tacs lst =
  [ (usolve (interp_opts
               (set_quick_opts true
                  (set_eager_opts false (default_s_opts ())))
               lst sauto),
     "sauto lq: on");
    (usolve (interp_opts
               (set_quick_opts true (default_s_opts ()))
               lst sauto),
     "sauto q: on");
    (usolve (interp_opts
               (set_eager_opts false (default_s_opts ()))
               lst sauto),
     "sauto l: on");
    (usolve (interp_opts (default_s_opts ()) lst sauto),
     "sauto");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_quick_opts true
                     (set_eager_opts false (default_s_opts ()))))
               lst sauto),
     "sauto lqb: on");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_quick_opts true (default_s_opts ())))
               lst sauto),
     "sauto qb: on");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_eager_opts false (default_s_opts ())))
               lst sauto),
     "sauto lb: on");
    (usolve (interp_opts
               (set_brefl_opts true (default_s_opts ()))
               lst sauto),
     "sauto b: on")
  ]

let best_tacs_batch_a lst =
  [ (usolve (interp_opts (default_s_opts ()) lst sfirstorder),
     "sfirstorder");
    (usolve (interp_opts (default_s_opts ()) lst scongruence),
     "scongruence");
    (usolve (interp_opts
               (set_quick_opts true
                  (set_eager_opts false (hauto_s_opts ())))
               lst sauto),
     "hauto lq: on");
    (usolve (interp_opts
               (set_quick_opts true (hauto_s_opts ()))
               lst sauto),
     "hauto q: on");
    (usolve (interp_opts
               (set_eager_opts false (hauto_s_opts ()))
               lst sauto),
     "hauto l: on");
    (usolve (interp_opts
               (set_quick_opts true
                  (set_eager_opts false (default_s_opts ())))
               lst sauto),
     "sauto lq: on");
    (usolve (interp_opts
               (set_eager_opts false (qauto_s_opts ()))
               lst sauto),
     "qauto l: on");
    (usolve (interp_opts
               (set_rew_opts false
                  (set_quick_opts true
                     (set_eager_opts false (hauto_s_opts ()))))
               lst sauto),
     "hauto lq: on rew: off");
    (usolve (interp_opts
               (set_rew_opts false
                  (set_quick_opts true
                     (set_eager_opts false (default_s_opts ()))))
               lst sauto),
     "sauto lq: on rew: off")
  ]

let best_tacs_batch_b lst =
  [ (usolve (interp_opts
               ({ (set_quick_opts true
                     (set_eager_opts false (hauto_s_opts ()))) with
                  s_directed_rewriting = false
               })
               lst sauto),
     "hauto lq: on drew: off");
    (usolve (interp_opts
               { (set_quick_opts true (hauto_s_opts ())) with
                 s_directed_rewriting = false}
               lst sauto),
     "hauto q: on drew: off");
    (usolve (interp_opts
               ({ (set_eager_opts false (hauto_s_opts ())) with
                  s_directed_rewriting = false })
               lst sauto),
     "hauto l: on drew: off");
    (usolve (interp_opts
               (set_quick_opts true (hauto_s_opts ()))
               lst sauto),
     "hauto");
    (usolve (interp_opts
               (set_quick_opts true (default_s_opts ()))
               lst sauto),
     "sauto q: on");
    (usolve (interp_opts
               (set_eager_opts false (default_s_opts ()))
               lst sauto),
     "sauto l: on");
    (usolve (interp_opts (default_s_opts ()) lst sauto),
     "sauto");
    (usolve (interp_opts { (hauto_s_opts ()) with
                 s_directed_rewriting = false }
               lst sauto),
     "hauto drew: off")
  ]

let best_tacs_batch_c lst =
  [ (usolve (interp_opts
               (set_brefl_opts true
                  (set_quick_opts true
                     (set_eager_opts false (hauto_s_opts ()))))
               lst sauto),
     "hauto lqb: on");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_quick_opts true (hauto_s_opts ())))
               lst sauto),
     "hauto qb: on");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_eager_opts false (hauto_s_opts ())))
               lst sauto),
     "hauto lb: on");
    (usolve (interp_opts
               (set_brefl_opts true (hauto_s_opts ()))
               lst sauto),
     "hauto b: on");
    (usolve (interp_opts
               { (set_brefl_opts true
                    (set_quick_opts true
                       (set_eager_opts false (hauto_s_opts ())))) with
                 s_directed_rewriting = false }
               lst sauto),
     "hauto lqb: on drew: off");
    (usolve (interp_opts
               { (set_brefl_opts true
                    (set_quick_opts true (hauto_s_opts ()))) with
                 s_directed_rewriting = false }
               lst sauto),
     "hauto qb: on drew: off");
    (usolve (interp_opts
               { (set_brefl_opts true
                    (set_eager_opts false (hauto_s_opts ()))) with
                 s_directed_rewriting = false }
               lst sauto),
     "hauto lb: on drew: off");
    (usolve (interp_opts
               { (set_brefl_opts true (hauto_s_opts ())) with
                 s_directed_rewriting = false }
               lst sauto),
     "hauto b: on drew: off")
  ]

let best_tacs_batch_1 lst =
  [ (usolve (interp_opts
               (set_brefl_opts true
                  (set_quick_opts true
                     (set_eager_opts false (default_s_opts ()))))
               lst sauto),
     "sauto lqb: on");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_quick_opts true (default_s_opts ())))
               lst sauto),
     "sauto qb: on");
    (usolve (interp_opts
               (set_brefl_opts true
                  (set_eager_opts false (default_s_opts ())))
               lst sauto),
     "sauto lb: on");
    (usolve (interp_opts
               (set_brefl_opts true (default_s_opts ()))
               lst sauto),
     "sauto b: on");
    (usolve (interp_opts
               ({ (set_quick_opts true
                     (set_eager_opts false (default_s_opts ()))) with
                  s_directed_rewriting = false
               })
               lst sauto),
     "sauto lq: on drew: off");
    (usolve (interp_opts
               { (set_quick_opts true (default_s_opts ())) with
                 s_directed_rewriting = false}
               lst sauto),
     "sauto q: on drew: off");
    (usolve (interp_opts
               ({ (set_eager_opts false (default_s_opts ())) with
                  s_directed_rewriting = false })
               lst sauto),
     "sauto l: on drew: off");
    (usolve (interp_opts { (default_s_opts ()) with
                 s_directed_rewriting = false }
               lst sauto),
     "sauto drew: off")
  ]

let best_tacs_batch_2 lst =
  [ (usolve (interp_opts (qauto_s_opts ()) lst sauto), "qauto");
    (usolve (interp_opts (hauto_s_opts ()) lst fcrush), "hfcrush");
    (usolve (interp_opts (hauto_s_opts ()) lst ecrush), "hecrush");
    (usolve (interp_opts (default_s_opts ()) lst sblast), "qblast");
    (usolve (interp_opts (default_s_opts ()) lst sblast), "sblast");
    (usolve (interp_opts (default_s_opts ()) lst fcrush), "fcrush");
    (usolve (interp_opts (default_s_opts ()) lst ecrush), "ecrush");
    (usolve (interp_opts (default_s_opts ()) lst scrush), "scrush")
  ]

let best_tacs_batch_3 lst =
  [ (usolve (interp_opts
               { (qauto_s_opts ()) with s_directed_rewriting = false }
               lst sauto), "qauto drew: off");
    (usolve (interp_opts
               { (hauto_s_opts ()) with s_directed_rewriting = false }
               lst fcrush), "hfcrush drew: off");
    (usolve (interp_opts
               { (hauto_s_opts ()) with s_directed_rewriting = false }
               lst ecrush), "hecrush drew: off");
    (usolve (interp_opts
               { (default_s_opts ()) with s_directed_rewriting = false }
               lst sblast), "qblast drew: off");
    (usolve (interp_opts
               { (default_s_opts ()) with s_directed_rewriting = false }
               lst sblast), "sblast drew: off");
    (usolve (interp_opts
               { (default_s_opts ()) with s_directed_rewriting = false }
               lst fcrush), "fcrush drew: off");
    (usolve (interp_opts
               { (default_s_opts ()) with s_directed_rewriting = false }
               lst ecrush), "ecrush drew: off");
    (usolve (interp_opts
               { (default_s_opts ()) with s_directed_rewriting = false }
               lst scrush), "scrush drew: off")
  ]

let best_tacs_batch_4 lst =
  [ (usolve (interp_opts
               { (set_brefl_opts true
                    (set_quick_opts true
                       (set_eager_opts false (default_s_opts ())))) with
                 s_directed_rewriting = false }
               lst sauto),
     "sauto lqb: on drew: off");
    (usolve (interp_opts
               { (set_brefl_opts true
                    (set_quick_opts true (default_s_opts ()))) with
                 s_directed_rewriting = false }
               lst sauto),
     "sauto qb: on drew: off");
    (usolve (interp_opts
               { (set_brefl_opts true
                    (set_eager_opts false (default_s_opts ()))) with
                 s_directed_rewriting = false }
               lst sauto),
     "sauto lb: on drew: off");
    (usolve (interp_opts
               { (set_brefl_opts true (default_s_opts ())) with
                 s_directed_rewriting = false }
               lst sauto),
     "sauto b: on drew: off");
    (usolve (interp_opts
               (set_dep_opts true
                  (set_quick_opts true
                     (set_eager_opts false (hauto_s_opts ()))))
               lst sauto),
     "hauto lq: on dep: on");
    (usolve (interp_opts
               (set_dep_opts true
                  (set_quick_opts true (hauto_s_opts ())))
               lst sauto),
     "hauto q: on dep: on");
    (usolve (interp_opts
               (set_dep_opts true
                  (set_eager_opts false (hauto_s_opts ())))
               lst sauto),
     "hauto l: on dep: on");
    (usolve (interp_opts
               (set_dep_opts true (hauto_s_opts ()))
               lst sauto),
     "hauto dep: on")
  ]

let best_tacs_batch_5 lst =
  [ (usolve (interp_opts
               (set_dep_opts true
                  (set_quick_opts true
                     (set_eager_opts false (default_s_opts ()))))
               lst sauto),
     "sauto lq: on dep: on");
    (usolve (interp_opts
               (set_dep_opts true
                  (set_quick_opts true (default_s_opts ())))
               lst sauto),
     "sauto q: on dep: on");
    (usolve (interp_opts
               (set_dep_opts true
                  (set_eager_opts false (default_s_opts ())))
               lst sauto),
     "sauto l: on dep: on");
    (usolve (interp_opts
               (set_dep_opts true (default_s_opts ()))
               lst sauto),
     "sauto dep: on");
    (usolve (interp_opts
               (set_dep_opts true
                  (set_brefl_opts true
                     (set_quick_opts true
                        (set_eager_opts false (default_s_opts ())))))
               lst sauto),
     "sauto lqb: on dep: on");
    (usolve (interp_opts
               (set_dep_opts true
                  (set_brefl_opts true
                     (set_quick_opts true (default_s_opts ()))))
               lst sauto),
     "sauto qb: on dep: on");
    (usolve (interp_opts
               (set_dep_opts true
                  (set_brefl_opts true
                     (set_eager_opts false (default_s_opts ()))))
               lst sauto),
     "sauto lb: on dep: on");
    (usolve (interp_opts
               (set_dep_opts true
                  (set_brefl_opts true
                     (default_s_opts ())))
               lst sauto),
     "sauto b: on dep: on")
  ]

let best_tacs lst =
  [ (usolve (interp_opts (hauto_s_opts ()) lst sfirstorder),
     "sfirstorder");
    (usolve (interp_opts
               (set_quick_opts true
                  (set_eager_opts false (hauto_s_opts ())))
               lst sauto),
     "hauto lq: on");
    (usolve (interp_opts
               (set_quick_opts true (hauto_s_opts ()))
               lst sauto),
     "hauto");
    (usolve (interp_opts
               (set_quick_opts true
                  (set_eager_opts false (default_s_opts ())))
               lst sauto),
     "sauto lq: on");
    (usolve (interp_opts
               (set_quick_opts true (default_s_opts ()))
               lst sauto),
     "sauto q: on");
    (usolve (interp_opts (default_s_opts ()) lst sauto),
     "sauto");
    (usolve (interp_opts
               ({ (set_quick_opts true
                     (set_eager_opts false (hauto_s_opts ()))) with
                  s_directed_rewriting = false
               })
               lst sauto),
     "hauto lq: on drew: off");
    (usolve (interp_opts
               ({ (set_quick_opts true
                     (set_eager_opts false (default_s_opts ()))) with
                  s_directed_rewriting = false
               })
               lst sauto),
     "sauto lq: on drew: off");
    (usolve (interp_opts
               (set_brefl_opts true (hauto_s_opts ()))
               lst sauto),
     "hauto b: on");
    (usolve (interp_opts (default_s_opts ())
               lst fcrush),
     "fcrush")
  ]

let best_tactics lst =
  [best_tacs_batch_a lst; best_tacs_batch_b lst; best_tacs_batch_c lst;
   best_tacs_batch_1 lst; best_tacs_batch_2 lst; best_tacs_batch_3 lst;
   best_tacs_batch_4 lst; best_tacs_batch_5 lst]

let hbest_tactics lst =
  [trivial_tacs_batch lst @ hbest_tacs lst]

let sbest_tactics lst =
  [trivial_tacs_batch lst @ sbest_tacs lst]

let hammer_pretactics () =
  best_tacs []

let run_best limit tacs (lst : sopt_t list)
      (f_success : string -> unit Proofview.tactic -> unit Proofview.tactic)
      (f_failure : unit -> unit Proofview.tactic) : unit Proofview.tactic =
  try_tactic begin fun () ->
    Hhpartac.partac limit (List.map fst tacs)
      begin fun k tac ->
        if k >= 0 then
          let tacname = snd (List.nth tacs k) in
          Proofview.Goal.enter begin fun gl ->
            let evd = Proofview.Goal.sigma gl in
            f_success (tacname ^ " " ^ string_of_sopt_list evd lst) tac
          end
        else
          f_failure ()
      end
  end

let try_best batches limit lst msg_success msg_failure =
  let rec hlp tacs =
    match tacs with
    | h :: t ->
       run_best limit h lst
         begin fun str tac ->
           Feedback.msg_info (Pp.str (msg_success ^ str));
           tac
         end
         (fun () -> hlp t)
    | [] ->
       Tacticals.New.tclZEROMSG (Pp.str msg_failure)
  in
  hlp batches

let default_best_limit = 1

let find_best_tactic batches l name =
  let limit =
    List.fold_left (fun acc x -> match x with SOTimeout n -> n | _ -> acc)
      default_best_limit l
  in
  let lst =
    List.filter (fun x -> match x with SOTimeout _ -> false | _ -> true) l
  in
  try_tactic (fun () ->
      try_best batches limit lst
        ("Replace the `" ^ name ^ "` tactic with:\n\t")
        ("The `" ^ name ^ "` tactic failed. You may try increasing the time limit with the `time:` option (default: 1s), or setting the `depth:` option. See https://coqhammer.github.io for more information."))
