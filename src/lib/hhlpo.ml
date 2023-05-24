(* Lexicographic path order on terms -- implementation *)

open Environ

module Utils = Hhutils

let gt cgt evd =
  let env = Global.env () in
  let rec gt t1 t2 =
    let open Constr in
    let open EConstr in
    let ge t1 t2 = eq_constr evd t1 t2 || gt t1 t2 in
    let (h1, args1) = Utils.destruct_app evd t1 in
    let (h2, args2) = Utils.destruct_app evd t2 in
    match kind evd h1, kind evd h2 with
    | Const (c1, _), Const(c2, _) when QConstant.equal env c1 c2 ->
       let rec go args1 args2 =
         match args1, args2 with
         | a1 :: args1', a2 :: args2' when eq_constr evd a1 a2 ->
            go args1' args2'
         | a1 :: args1', a2 :: args2' when gt a1 a2 ->
            List.for_all (gt t1) args2'
         | _ ->
            false
       in
       go (Array.to_list args1) (Array.to_list args2)
    | Const (c1, _), Const(c2, _) when cgt c1 c2 ->
       Array.for_all (gt t1) args2
    | Const(c1, _), Construct _ | Const(c1, _), Ind _ ->
       Array.for_all (gt t1) args2
    | _ ->
       Array.exists (fun x -> ge x t2) args1
  in
  gt

let lpo_cache = Hashtbl.create 128

let rec const_gt c1 c2 =
  try
    Hashtbl.find lpo_cache (c1, c2)
  with Not_found ->
    begin
      let b =
        if Declareops.is_opaque (Global.lookup_constant c1) then
          false
        else
          match Global.body_of_constant Library.indirect_accessor c1 with
          | Some (b, _, _) ->
             let env = Global.env () in
             let consts =
               Utils.fold_constr_ker
                 begin fun _ acc t ->
                 let open Constr in
                 match kind t with
                 | Const(c, _) when not (QConstant.equal env c c1) -> c :: acc
                 | _ -> acc
                 end
                 []
                 b
             in
             let rec go lst =
               match lst with
               | c :: lst' ->
                  if QConstant.equal env c c2 || const_gt c c2 then
                    true
                  else
                    go lst'
               | [] ->
                  false
             in
             go consts
          | None ->
             false
      in
      Hashtbl.add lpo_cache (c1, c2) b;
      b
    end

let lpo = gt const_gt

let clear_cache () = Hashtbl.clear lpo_cache
