(* sauto tactic options - interface *)

open Ltac_plugin
open Sauto

type sopt_t =
  SONop
| SOUse of Constrexpr.constr_expr list
| SOGen of Constrexpr.constr_expr list
| SOUnfold of Libnames.qualid list
| SOUnfoldAll
| SOUnfoldNone
| SOAlwaysUnfold of Libnames.qualid list
| SOAlwaysUnfoldAll
| SOAlwaysUnfoldNone
| SOInv of Libnames.qualid list
| SOInvAll
| SOInvNone
| SOCtrs of Libnames.qualid list
| SOCtrsAll
| SOCtrsNone
| SOCaseSplit of Libnames.qualid list
| SOCaseSplitAll
| SOCaseSplitNone
| SOSimpleSplit of Libnames.qualid list
| SOSimpleSplitAll
| SOSimpleSplitNone
| SOBases of string list
| SOBasesAdd of string list
| SOBasesAll
| SORewBases of string list
| SORewBasesAdd of string list
| SOHintBases of string list
| SOHintBasesAdd of string list
| SOHintBasesAll
| SOFinish of Tacexpr.raw_tactic_expr
| SOFinal of Tacexpr.raw_tactic_expr
| SOSolve of Tacexpr.raw_tactic_expr
| SOSimp of Tacexpr.raw_tactic_expr
| SOSSimp of Tacexpr.raw_tactic_expr
| SOSolveAdd of Tacexpr.raw_tactic_expr
| SOSimpAdd of Tacexpr.raw_tactic_expr
| SOSSimpAdd of Tacexpr.raw_tactic_expr
| SOForward of bool
| SOEagerCaseSplit of bool
| SOSimpleInvert of bool
| SOEagerInvert of bool
| SOEagerReduce of bool
| SOEagerRewrite of bool
| SODirectedRewrite of bool
| SOUndirectedRewrite of bool
| SORewrite of bool
| SOReflect of bool
| SOReflectRaw of bool
| SOReduce of bool
| SOSapply of bool
| SOLimit of int
| SODepth of int
| SOTimeout of int
| SOExhaustive of bool
| SOLia of bool
| SOSig of bool
| SOPrf of bool
| SODep of bool
| SODepRaw of bool
| SOEager of bool
| SOQuick of bool

val string_of_sopt : Evd.evar_map -> sopt_t -> string
val string_of_sopt_list : Evd.evar_map -> sopt_t list -> string

val interp_opts : s_opts -> sopt_t list ->
                  (s_opts -> unit Proofview.tactic) (* continuation *)
                  -> unit Proofview.tactic
