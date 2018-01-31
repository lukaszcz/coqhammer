
open Pp
open Feedback

let error s = msg_error (Pp.str s)
let notice s = msg_notice (Pp.str s)
let info s = msg_info (Pp.str s)
let warn s = msg_warning (Pp.str s)
