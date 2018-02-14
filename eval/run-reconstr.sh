#!/bin/bash

for d in atp/o/*; do
    s=`basename $d`
    echo "$s" > coqhammer.opt
    make -k -j "$1" reconstr
    mv logs/reconstr logs/reconstr-$s
done
