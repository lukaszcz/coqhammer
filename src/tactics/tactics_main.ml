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
  | _ -> Utils.get_const "Tactics.default" (* a hack; may happen with Let's *)

let to_inductive t =
  let open Constr in
  let open EConstr in
  match kind Evd.empty t with
  | Ind(ind, _) -> ind
  | _ -> failwith "sauto: not an inductive type"

let filter_default =
  let cdefault = Utils.get_constr "Tactics.default" in
  List.filter (fun c -> c <> cdefault)

let filter_noninductive =
  let cdefault = Utils.get_constr "Tactics.default" in
  let chints = Utils.get_constr "Tactics.hints" in
  let cnone = Utils.get_constr "Tactics.none" in
  let cnohints = Utils.get_constr "Tactics.nohints" in
  let clogic = Utils.get_constr "Tactics.logic" in
  List.filter
    begin fun t ->
      let open Constr in
      let open EConstr in
      match kind Evd.empty t with
      | Ind(ind, _) -> true
      | _ -> t = cdefault || t = chints || t = cnone || t = cnohints || t = clogic
    end

let get_s_opts ropts bases unfoldings inverting splits ctrs =
  let cdefault = Utils.get_constr "Tactics.default" in
  let chints = Utils.get_constr "Tactics.hints" in
  let cnone = Utils.get_constr "Tactics.none" in
  let cnohints = Utils.get_constr "Tactics.nohints" in
  let clogic = Utils.get_constr "Tactics.logic" in
  let get_s_opts_field logic_lst conv opts lst default =
    match lst with
    | [] -> default
    | [h] when h = cdefault -> default
    | [h] when h = chints -> SSome []
    | [h] when h = cnone -> SNone
    | [h] when h = clogic -> SNoHints logic_lst
    | _ ->
       if List.mem cnone lst then
         SNone
       else
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
    match unfoldings with
    | None -> opts
    | Some t ->
       { opts with s_unfolding =
           get_s_opts_field logic_constants to_const opts
             (destruct_constr t) default_s_opts.s_unfolding }
  in
  let get_invertings opts =
    match inverting with
    | None -> opts
    | Some t ->
       { opts with s_inversions =
           get_s_opts_field logic_inductives to_inductive opts
             (destruct_constr t) default_s_opts.s_inversions }
  in
  let get_splittings opts =
    match splits with
    | None -> opts
    | Some t ->
       { opts with s_case_splits =
           get_s_opts_field logic_inductives to_inductive opts
             (destruct_constr t) default_s_opts.s_case_splits }
  in
  let get_ctrs opts =
    match ctrs with
    | None -> opts
    | Some t ->
       { opts with s_constructors =
           get_s_opts_field logic_inductives to_inductive opts
             (filter_noninductive (destruct_constr t)) default_s_opts.s_constructors }
  in
  let get_bases opts =
    match bases with
    | None -> opts
    | Some b -> { opts with s_rew_bases = b }
  in
  let get_ropt opts ropt =
    match ropt with
    | "no_forward" -> { opts with s_forwarding = false }
    | "no_eager_case_split" -> { opts with s_eager_case_splitting = false }
    | "no_simple_split" -> { opts with s_simple_splits = SNone }
    | "no_simple_invert" -> { opts with s_simple_inverting = false }
    | "no_eager_invert" -> { opts with s_eager_inverting = false }
    | "no_eager_reduction" -> { opts with s_eager_reducing = false }
    | "no_eager_rewrite" -> { opts with s_eager_rewriting = false }
    | "no_heuristic_rewrite" -> { opts with s_heuristic_rewriting = false }
    | "no_rewrite" ->
       { opts with s_rewriting = false; s_eager_rewriting = false; s_heuristic_rewriting = false }
    | "no_bnat_reflection" -> { opts with s_bnat_reflect = false }
    | "no_reduction" -> { opts with s_reducing = false; s_eager_reducing = false }
    | "presimplify" -> { opts with s_presimplify = true }
    | "no_sapply" -> { opts with s_sapply = false }
    | "depth_cost_model" -> { opts with s_depth_cost_model = true }
    | "tree_cost_model" -> { opts with s_depth_cost_model = false }
    | "exhaustive" -> { opts with s_exhaustive = true }
    | "default" -> opts
    | _ -> failwith ("sauto: unknown option `" ^ ropt ^ "'")
  in
  List.fold_left
    get_ropt
    (get_bases (get_unfoldings (get_invertings (get_splittings (get_ctrs default_s_opts)))))
    ropts
