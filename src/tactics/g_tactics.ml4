DECLARE PLUGIN "hammer_tactics"

open Ltac_plugin
open Stdarg
open Tacarg
open Sauto

TACTIC EXTEND Hammer_sauto
| [ "sauto" ] -> [ sauto default_s_opts 6 ]
END
