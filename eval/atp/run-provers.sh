#!/bin/bash

for d in atp-problems/*
do
    echo "***************"
    echo $d
    rm i/f
    ln -s ../$d i/f
    make -k -j 45 e-19 vam-40 z3-40q
    p=`basename $d`
    mv logs/atp/e-19 logs/atp/eprover-$p
    mv logs/atp/vam-40 logs/atp/vampire-$p
    mv logs/atp/z3-40q logs/atp/z3-$p
    if [ -n "$1" ]; then
        echo "" | mail -s "$p finished" $1
    fi
done
if [ -n "$1" ]; then
    echo "" | mail -s "Provers finished" $1
fi
