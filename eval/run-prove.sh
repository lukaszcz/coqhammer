#!/bin/bash

make clean-vo
echo "prove" > coqhammer.opt
make -k -j "$1" prove
if [ -n "$2" ]; then
    echo "" | mail -s "Coq proving finished" "$2"
fi
