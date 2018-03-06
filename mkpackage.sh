#!/bin/bash

VERSION="1.0.?-coq8.7"

rm -rf coqhammer-$VERSION
mkdir coqhammer-$VERSION
cp LICENSE README TODO _CoqProject Makefile Makefile.coq.local mkpackage.sh coqhammer-$VERSION
mkdir coqhammer-$VERSION/examples
cp examples/*.v coqhammer-$VERSION/examples
mkdir coqhammer-$VERSION/theories
cp theories/*.v coqhammer-$VERSION/theories
mkdir coqhammer-$VERSION/src
cp src/*.ml coqhammer-$VERSION/src
cp src/*.ml4 coqhammer-$VERSION/src
cp src/*.mllib coqhammer-$VERSION/src
mkdir coqhammer-$VERSION/src/predict
cp src/predict/*.cpp coqhammer-$VERSION/src/predict
mkdir coqhammer-$VERSION/src/htimeout
cp src/htimeout/*.c coqhammer-$VERSION/src/htimeout
tar czf coqhammer-$VERSION.tar.gz coqhammer-$VERSION
rm -rf coqhammer-$VERSION
