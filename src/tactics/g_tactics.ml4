DECLARE PLUGIN "hammer_tactics"

open Ltac_plugin
open Stdarg
open Tacarg
open Sauto

TACTIC EXTEND Hammer_ssauto
| [ "ssauto" ] -> [ sauto default_sauto_opts 6 ]
END
