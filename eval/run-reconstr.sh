#!/bin/bash

make clean-vo
echo "reconstr" > coqhammer.opt
make -k -j `echo "$1/7" | bc` reconstr
if [ -n "$2" ]; then
    echo "" | mail -s "Reconstruction finished" "$2"
fi
