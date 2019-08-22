DECLARE PLUGIN "hammer_lib"

open Ltac_plugin
open Stdarg
open Tacarg
open Extraargs

module Utils = Hhutils

TACTIC EXTEND Hammer_isAtom
  | [ "isAtom" lconstr(t) ] -> [
    if Utils.is_atom Evd.empty t then
      Tacticals.New.tclIDTAC
    else
      Proofview.tclZERO (Failure "not an atom")
  ]
END

TACTIC EXTEND Hammer_isIndAtom
  | [ "isIndAtom" lconstr(t) ] -> [
    if Utils.is_ind_atom Evd.empty t then
      Tacticals.New.tclIDTAC
    else
      Proofview.tclZERO (Failure "not an inductive atom")
  ]
END
