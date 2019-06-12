COQC=coqc

all: plugin_test.vo tactics_test.vo basic.vo hashing.vo arith.vo zarith.vo lists.vo

plugin_test.vo : plugin_test.v
	$(COQC) plugin_test.v

tactics_test.vo : tactics_test.v
	$(COQC) tactics_test.v

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
