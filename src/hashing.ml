open Coqterms

(***************************************************************************************)
(* Coqterm hashing *)

(* numbers from m up to but not including n *)
let range m n =
  let rec go acc i j =
    if i >= j then acc else go (i :: acc) (i+1) j
  in List.rev (go [] m n)

let var i =
  "v" ^ (string_of_int i)

(* creates a list of m fresh vars starting at n *)
let vars n m =
  List.map var (range n (n+m))

let rec zip xs ys = 
  match xs with
  | []    -> []
  | x::vs -> match ys with
             | []    -> []
             | y::ws -> (x,y)::(zip vs ws)

(* substitutes all occ. of the name oldn with the name newn in term t; TODO: variable capture *)
let rec sub newn oldn t = 
  let f = sub newn oldn in
  match t with
  | Var x                 -> Var (if x = oldn then newn else x)
  | Const x               -> Const x
  | App(t1,t2)            -> App(f t1, f t2)
  | Lam(x,t1,t2)          -> Lam (x, f t1, f t2)
  | Case(indt,t1,t2,n,cs) -> Case(indt, f t1, f t2, n, List.map (fun (m,x) -> (m,f x)) cs)
  | Cast(t1,t2)           -> Cast(f t1, f t2)
  | Fix(t,n,xs,ts1,ts2)   -> Fix(t,n,xs, List.map f ts1, List.map f ts2)
  | Let(t1,(x,t2,t3))     -> Let(f t1, (x,f t2, f t3))
  | Prod(x,t1,t2)         -> Prod(x, f t1, f t2)
  | IndType(indt,xs,n)    -> IndType(indt,xs,n)
  | SortProp              -> SortProp
  | SortSet               -> SortSet
  | SortType              -> SortType
  | Quant(q,(x,t1,t2))    -> Quant(q,(x,f t1,f t2))
  | Equal(t1,t2)          -> Equal(f t1, f t2)

let rec subs pairs t =
  match pairs with
  | []                -> t
  | (newn,oldn) :: qs -> sub newn oldn (subs qs t)

(* canonical representation using var. renaming starting at n along with variable substitutions; TODO: check this *)
let rec can_aux n t =
  let f = can_aux n in
    match t with
    | Var x                 -> Var x
    | Const x               -> Const x
    | App(t1,t2)            -> App (f t1, f t2)
    | Lam(x,t1,t2)          -> let v = var n in Lam(v, f t1, can_aux (n+1) (sub v x t2))
    | Case(indt,t1,t2,m,cs) -> Case(indt, f t1, f t2, m, List.map (fun (p,u) -> (p, f u)) cs)
    | Cast(t1,t2)           -> Cast(f t1, f t2)
    | Fix(t,i,xs,ts1,ts2)   -> let m = List.length xs in
                                 let newvars = vars n m in 
                                   let newbodies = List.map (fun b -> can_aux (n+m) (subs (zip (vars n m) xs) b)) ts2
                                     in Fix(t,i,newvars, List.map f ts1, newbodies)
    | Let(t1,(x,t2,t3))     -> let v = var n in Let(f t1, (v,f t2, can_aux (n+1) (sub v x t2)))
    | Prod(x,t1,t2)         -> let v = var n in Prod(v, f t1, can_aux (n+1) (sub v x t2))
    | IndType(indt,xs,n)    -> IndType(indt,xs,n)
    | SortProp              -> SortProp
    | SortSet               -> SortSet
    | SortType              -> SortType
    | Quant(q,(x,t1,t2))    -> let v = var n in Quant(q,(v,f t1,can_aux (n+1) (sub v x t2)))
    | Equal(t1,t2)          -> Equal(f t1,f t2)

(* takes a context and term and returns them in canonical form, along with a list of free variable substitutions made. *)
let canonical ctx0 =
  let rec can_ctx_aux acc subacc n ctx t =
    match ctx with
    | []            -> (acc, subacc, can_aux n t)
    | (x,t) :: rest -> can_ctx_aux ((var n,t) :: acc) ((x,var n) :: subacc) (n+1) (List.map (fun (y,t1) -> (y,sub (var n) x t1)) rest) (sub (var n) x t)
  in can_ctx_aux [] [] 0 (List.rev ctx0)

let funcs_hash : ((string * coqterm) list * coqterm , coqterm) Hashtbl.t = Hashtbl.create 10

(* hashing function for term in context which respects alpha equivalence *)
let alphahash ctx t =
  let (ctx', _, t') = canonical (get_fvars ctx t) t
  in
  Hashtbl.hash (ctx', t')
