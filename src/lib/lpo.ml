(* Lexicographic path order on terms -- implementation *)

module Utils = Hhutils

let gt cgt evd =
  let rec gt t1 t2 =
    let ge t1 t2 = t1 = t2 || gt t1 t2 in
    let (prods1, h1, args1) = Utils.destruct_prod evd t1 in
    let (prods2, h2, args2) = Utils.destruct_prod evd t2 in
    if prods1 <> [] || prods2 <> [] then
      false
    else
      let open Constr in
      let open EConstr in
      match kind evd h1, kind evd h2 with
      | Const (c1, _), Const(c2, _) when c1 = c2 ->
         let rec go args1 args2 =
           match args1, args2 with
           | a1 :: args1', a2 :: args2' when a1 = a2 ->
              go args1' args2'
           | a1 :: args1', a2 :: args2' when gt a1 a2 ->
              List.for_all (gt t1) args2'
           | _ ->
              false
         in
         go args1 args2
      | Const (c1, _), Const(c2, _) when cgt c1 c2 ->
         List.for_all (gt t1) args2
      | Const(c1, _), Construct _ | Const(c1, _), Ind _ ->
         List.for_all (gt t1) args2
      | _ ->
         List.exists (fun x -> ge x t2) args1
  in
  gt

let const_gt =
  let cache = Hashtbl.create 128 in
  let rec go c1 c2 =
    if not (Hashtbl.mem cache (c1, c2)) then
      begin
        let b =
          match Global.body_of_constant c1 with
          | Some b ->
             let consts =
               Utils.fold_constr_ker
                 begin fun _ acc t ->
                   let open Constr in
                   match kind t with
                   | Const(c, _) when c <> c1 -> c :: acc
                   | _ -> acc
                 end
                 []
                 (fst b)
             in
             let rec go2 lst =
               match lst with
               | c :: lst' ->
                  if c = c2 || go c c2 then
                    true
                  else
                    go2 lst'
               | [] ->
                  false
             in
             go2 consts
          | None ->
             false
        in
        Hashtbl.add cache (c1, c2) b
      end;
    Hashtbl.find cache (c1, c2)
  in
  go

let lpo = gt const_gt
