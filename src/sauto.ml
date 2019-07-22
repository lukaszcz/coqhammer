(* sauto -- implementation *)

type sauto_opts = {
  inversions : string list;
}

let rec search opts gl = search opts gl

let sauto opts =
  Proofview.Goal.nf_enter (search opts)
