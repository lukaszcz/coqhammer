#!/bin/bash

VERBOSE=""
if [ "$1" = "-v" ]; then
    VERBOSE="-v"
    shift
fi
./gen-atp.sh $1 $2
cd atp
if [ "$VERBOSE" = "-v" ]; then
    ./run-provers.sh $1 $2
else
    ./run-provers.sh $1
    if [ -n "$2" ]; then
        echo "" | mail -s "Provers finished" "$2"
    fi
fi
cd ..
./run-reconstr.sh $1 $2
./gen-stats.sh
if [ -n "$2" ]; then
    echo "" | mail -s "Evaluation finished" "$2"
fi
