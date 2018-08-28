#!/bin/bash

for d in atp/o/*; do
    s=`basename $d`
    make clean-vo
    echo "$s" > coqhammer.opt
    make -k -j "$1" reconstr
    mv logs/reconstr logs/reconstr-$s
    if [ -n "$2" ]; then
        echo "" | mail -s "reconstr $p finished" "$2"
    fi
done
if [ -n "$2" ]; then
    echo "" | mail -s "Reconstruction finished" "$2"
fi
