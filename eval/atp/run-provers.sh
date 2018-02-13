#!/bin/bash

for d in problems/*
do
    echo "***************"
    echo $d
    rm i/f
    ln -s ../$d i/f
    make -k -j 45 e-19 vam-40 z3-40q
    p=`basename $d`
    mv o/e-19 o/eprover-$p
    mv o/vam-40 o/vampire-$p
    mv o/z3-40q o/z3-$p
    if [ -n "$1" ]; then
        echo "" | mail -s "$p finished" $1
    fi
done
if [ -n "$1" ]; then
    echo "" | mail -s "Provers finished" $1
fi
