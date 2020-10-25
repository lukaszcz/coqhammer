COQC=coqc

all: tactics_test.vo legacy_tactics_test.vo

tactics_test.vo: tactics_test.v
	$(COQC) tactics_test.v

legacy_tactics_test.vo: legacy_tactics_test.v
	$(COQC) legacy_tactics_test.v

clean:
	-rm -f *.vo *.glob .*.aux *.vos *.vok .*.cache

.PHONY: all clean
