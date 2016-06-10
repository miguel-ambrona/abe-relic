OCAMLBUILDFLAGS=-cflags "-w +a-e-9-44-48" -classic-display -use-ocamlfind -quiet -ocamlc ocamlc -ocamlopt ocamlopt
COREFLAGS=-pkg core_kernel \
    -tag short_paths \
    -cflags -strict-sequence

.PHONY: install abe.native

all: abe.native

abe.native:
	ocamlbuild $(COREFLAGS) $(OCAMLBUILDFLAGS) ./abe.native

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
