#!/bin/bash

for d in atp/o/*; do
    s=`basename $d`
    make clean-vo
    echo "$s" > coqhammer.opt
    make -k -j "$1" reconstr
    mv logs/reconstr logs/reconstr-$s
done
