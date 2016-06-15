OCAMLBUILDFLAGS=-cflags "-w +a-e-9-44-48" -use-menhir -menhir "menhir -v" -classic-display -use-ocamlfind -quiet -ocamlc ocamlc -ocamlopt ocamlopt
COREFLAGS=-pkg core_kernel \
    -tag short_paths \
    -cflags -strict-sequence

.PHONY: install test_abe.native abe_relic.native

all: abe_relic.native

abe_relic.native:
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) ./abe_relic.native

test:
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) ./test_abe.native && ./test_abe.native

OCAMLDEP= ocamlfind ocamldep -package core_kernel \
            -I src one-line

dev:
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) Parser.cmx

%.deps :
	$(OCAMLDEP) src/$(basename $@).ml> .depend
	ocamldot .depend > deps.dot
	dot -Tsvg deps.dot >deps.svg

depgraph :
	$(OCAMLDEP) src/*.ml src/*.mli \
        | grep -v Test | grep -v Extract > .depend
	ocamldot .depend > deps.dot
	dot -Tsvg deps.dot >deps.svg
