# The unix and str libraries left the default search path in OCaml 5, so build
# through ocamlfind rather than naming the .cmxa files directly.
OCAMLOPT=ocamlfind ocamlopt -package unix,str -linkpkg -inline 100 -unsafe

all: stat coqnames rmcomments fixreqs
	rm -f *.cm* *.o

stat: utils.ml stat.ml
	$(OCAMLOPT) $^ -o $@

coqnames: utils.ml coqnames.ml
	$(OCAMLOPT) $^ -o $@

fixreqs: utils.ml fixreqs.ml
	$(OCAMLOPT) $^ -o $@

rmcomments: rmcomments.c
	gcc $^ -o $@

clean:
	-rm -f rmcomments coqnames fixreqs stat *.cmo *.cmi *.cmx *.o
