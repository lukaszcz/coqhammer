
all: stat coqnames
	rm -f *.cm* *.o

stat: utils.ml stat.ml
	ocamlopt -inline 100 -unsafe unix.cmxa str.cmxa $^ -o $@

coqnames: utils.ml coqnames.ml
	ocamlopt -inline 100 -unsafe unix.cmxa str.cmxa $^ -o $@

clean:
	-rm coqnames stat *.cmo *.cmi *.cmx *.o
