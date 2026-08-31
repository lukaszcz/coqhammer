#!/bin/bash

DIR=`dirname "$0"`

"$DIR/rmcomments.sh"
# COQHAMMER_HOOK_PREAMBLE may contain one or more lines of vernacular.  It is
# inherited unchanged by coqnames, which inserts it after the HammerHook import.
"$DIR/coqnames"
