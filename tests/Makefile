COQC=coqc

all: basic.vo hashing.vo arith.vo zarith.vo lists.vo

basic.vo : basic.v
	$(COQC) basic.v

hashing.vo : hashing.v
	$(COQC) hashing.v

arith.vo : arith.v
	$(COQC) arith.v

zarith.vo : zarith.v
	$(COQC) zarith.v

lists.vo : lists.v
	$(COQC) lists.v

clean:
	-rm -f *.vo *.glob .*.aux
