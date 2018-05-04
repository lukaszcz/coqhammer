COQC=coqc

all: JaSyntax.vo JaTactics.vo JaProgram.vo Jafun.vo

JaSyntax.vo : JaSyntax.v
	$(COQC) JaSyntax.v

JaTactics.vo : JaTactics.v JaSyntax.vo
	$(COQC) JaTactics.v

JaProgram.vo : JaProgram.v JaSyntax.vo
	$(COQC) JaProgram.v

JaSubtype.vo : JaSubtype.v JaProgram.vo
	$(COQC) JaSubtype.v

Jafun.vo: Jafun.v JaTactics.vo JaSubtype.vo JaProgram.vo JaSyntax.vo
	$(COQC) Jafun.v

clean:
	-rm -f *.vo *.glob .*.aux
