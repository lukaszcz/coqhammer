DECLARE PLUGIN "hammer_tactics"

open Ltac_plugin
open Stdarg
open Tacarg
open Sauto

module Utils = Hhutils

TACTIC EXTEND Hammer_sauto_gen
| [ "sauto_gen" ] -> [ sauto default_s_opts 5 ]
END

TACTIC EXTEND Hammer_ssimpl_gen
| [ "ssimpl_gen" ] -> [
  ssimpl { default_s_opts with s_simpl_tac = Utils.ltac_apply "Tactics.ssolve" [] }
]
END
