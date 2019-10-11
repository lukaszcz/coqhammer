DECLARE PLUGIN "hammer_lib"

open Ltac_plugin
open Extraargs

module Utils = Hhutils

TACTIC EXTEND Hammer_isAtom
  | [ "isAtom" lconstr(t) ] -> [
    if Utils.is_atom Evd.empty t then
      Tacticals.New.tclIDTAC
    else
      Tacticals.New.tclFAIL 0 Pp.(str "not an atom")
  ]
END

TACTIC EXTEND Hammer_isIndAtom
  | [ "isIndAtom" lconstr(t) ] -> [
    if Utils.is_ind_atom Evd.empty t then
      Tacticals.New.tclIDTAC
    else
      Tacticals.New.tclFAIL 0 Pp.(str "not an inductive atom")
  ]
END
