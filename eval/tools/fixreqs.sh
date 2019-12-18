#!/bin/bash

DIR=`dirname "$0"`

"$DIR/rmcomments.sh"
"$DIR/fixreqs" "$1"
