COQC ?= rocq c

all: tactics_test.vo

# The legacy Reconstr tactics are deprecated, so their test is kept out of all
# and thus out of `make tests`.  Run it explicitly when working on them.
legacy-tests: legacy_tactics_test.vo

tactics_test.vo: tactics_test.v
	$(COQC) tactics_test.v

legacy_tactics_test.vo: legacy_tactics_test.v
	$(COQC) legacy_tactics_test.v

clean:
	-rm -f *.vo *.glob .*.aux

.PHONY: all clean legacy-tests
