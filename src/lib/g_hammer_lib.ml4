DECLARE PLUGIN "hammer_lib"

open Ltac_plugin
open Stdarg
open Tacarg

TACTIC EXTEND Hammer_test_tac
| [ "myintros" ] -> [ Tactics.intros ]
END
