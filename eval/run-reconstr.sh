#!/bin/bash

for d in atp/o/*; do
    s=`basename $d`
    echo "$s" > coqhammer.opt
    coqc "$1" >> "$2" 2>&1
done
