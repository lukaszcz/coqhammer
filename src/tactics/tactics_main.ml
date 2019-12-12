open Sauto

module Utils = Hhutils

let default_sauto_tree_limit = 1000
let default_sauto_depth_limit = 4

let get_opt opt def = match opt with Some x -> x | None -> def

let rec destruct_constr t =
  let open Constr in
  let open EConstr in
  match kind Evd.empty t with
  | App(i, args) ->
     begin
       match kind Evd.empty i with
       | Construct((ind, 1), _) when ind = Utils.get_inductive "Init.Datatypes.prod" ->
          begin
            match Array.to_list args with
            | [_; _; t1; t2] ->
               destruct_constr t1 @ destruct_constr t2
            | _ -> [t]
          end
       | _ -> [t]
     end
  | _ -> [t]

let to_const t =
  let open Constr in
  let open EConstr in
  match kind Evd.empty t with
  | Const(c, _) -> c
  | _ -> failwith "sauto: not a constant"

let to_inductive t =
  let open Constr in
  let open EConstr in
  match kind Evd.empty t with
  | Ind(ind, _) -> ind
  | _ -> failwith "sauto: not an inductive type"

let get_s_opts ropts bases unfoldings inverting ctrs =
  let cdefault = Utils.get_constr "Tactics.default" in
  let chints = Utils.get_constr "Tactics.hints" in
  let cnone = Utils.get_constr "Tactics.none" in
  let cnohints = Utils.get_constr "Tactics.nohints" in
  let clogic = Utils.get_constr "Tactics.logic" in
  let get_s_opts_field logic_lst conv opts lst default =
    match lst with
    | [h] when h = cdefault -> default
    | [h] when h = chints -> SSome []
    | [h] when h = cnone -> SNone
    | [h] when h = clogic -> SNoHints logic_lst
    | _ ->
       begin
         let b_nohints = List.mem cnohints lst in
         let b_hints = List.mem chints lst in
         let b_logic = List.mem clogic lst in
         let lst = List.filter (fun c -> c <> cnohints && c <> chints && c <> cdefault && c <> clogic) lst in
         let lst = List.map conv lst in
         let lst = if b_logic then logic_lst @ lst else lst in
         if b_nohints then
           SNoHints lst
         else if b_hints then
           SSome lst
         else
           match default with
           | SNoHints _ | SNone -> SNoHints lst
           | _ -> SSome lst
       end
  in
  let get_unfoldings opts =
    { opts with s_unfolding =
        get_s_opts_field logic_constants to_const opts
          (destruct_constr unfoldings) default_s_opts.s_unfolding }
  in
  let get_invertings opts =
    { opts with s_inversions =
        get_s_opts_field logic_inductives to_inductive opts
          (destruct_constr inverting) default_s_opts.s_inversions }
  in
  let get_ctrs opts =
    { opts with s_constructors =
        get_s_opts_field logic_inductives to_inductive opts
          (destruct_constr ctrs) default_s_opts.s_constructors }
  in
  let get_bases opts =
    { opts with s_rew_bases = bases }
  in
  let get_ropt opts ropt =
    match ropt with
    | "no_forward" -> { opts with s_forwarding = false }
    | "no_case_split" -> { opts with s_case_splits = SNone }
    | "no_simple_split" -> { opts with s_simple_splits = SNone }
    | "no_simple_invert" -> { opts with s_simple_inverting = false }
    | "no_eager_invert" -> { opts with s_eager_inverting = false }
    | "no_eager_reduction" -> { opts with s_eager_reducing = false }
    | "no_eager_rewrite" -> { opts with s_eager_rewriting = false }
    | "no_heuristic_rewrite" -> { opts with s_heuristic_rewriting = false }
    | "no_rewrite" ->
       { opts with s_rewriting = false; s_eager_rewriting = false; s_heuristic_rewriting = false }
    | "no_reflect" -> { opts with s_bnat_reflect = false }
    | "no_reduction" -> { opts with s_reducing = false; s_eager_reducing = false }
    | "presimplify" -> { opts with s_presimplify = true }
    | "depth_cost_model" -> { opts with s_depth_cost_model = true }
    | "tree_cost_model" -> { opts with s_depth_cost_model = false }
    | "exhaustive" -> { opts with s_exhaustive = true }
    | "default" -> opts
    | _ -> failwith ("sauto: unknown option `" ^ ropt ^ "'")
  in
  List.fold_left get_ropt (get_bases (get_unfoldings (get_invertings (get_ctrs default_s_opts)))) ropts
