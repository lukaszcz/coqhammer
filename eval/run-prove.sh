#!/bin/bash

make clean-vo
echo "prove" > coqhammer.opt
make -k -j "$1" prove

echo -n "Total problems: "
ls out/*.out | wc -l
echo -n "Successes: "
grep "^Success " out/*.out | wc -l

if [ -n "$2" ]; then
    echo "" | mail -s "Coq proving finished" "$2"
fi
