
all: stat coqnames coqnames_qed rmcomments
	rm -f *.cm* *.o

stat: utils.ml stat.ml
	ocamlopt -inline 100 -unsafe unix.cmxa str.cmxa $^ -o $@

coqnames: utils.ml coqnames.ml
	ocamlopt -inline 100 -unsafe unix.cmxa str.cmxa $^ -o $@

coqnames_qed: utils.ml coqnames_qed.ml
	ocamlopt -inline 100 -unsafe unix.cmxa str.cmxa $^ -o $@

rmcomments: rmcomments.c
	gcc $^ -o $@

clean:
	-rm -f rmcomments coqnames coqnames_qed stat *.cmo *.cmi *.cmx *.o
