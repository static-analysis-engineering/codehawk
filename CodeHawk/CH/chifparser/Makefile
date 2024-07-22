CHLIB = ../chlib
CHUTIL = ../chutil
ZARITHLIB = $(shell ocamlfind query zarith)

OCAMLC := ocamlopt -I $(ZARITHLIB) -I $(CHLIB)/cmi -I $(CHLIB)/cmx -I $(CHUTIL)/cmi
CAMLLINK := ocamlopt \
	-I $(ZARITHLIB) \
	$(ZARITHLIB)/zarith.cmxa \
	$(CHLIB)/chlib.cmxa

OCAMLCLINK := ocamlopt

MLLS = lexer.mll
MLYS = parser.mly 
LIBMODULES = parseError parser lexer chifparser

parsechif: $(LIBMODULES:%=%.cmx) main.cmx
	$(CAMLLINK) -o parsechif  $(LIBMODULES:%=%.cmx) main.cmx

chifparser.cmxa: $(LIBMODULES:%=%.cmx)
	$(OCAMLCLINK) -a -o chifparser.cmxa  $(LIBMODULES:%=%.cmx)

lib: $(LIBMODULES:%=%.cmx)
	$(CAMLLINK) -o chifparser unix.cmxa -I $(ZARITHLIB) $(ZARITHLIB)/zarith.cmxa $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(LIBMODULES:%=%.cmx)

lexer.ml: lexer.mll
	ocamllex lexer.mll

parser.ml parser.mli: parser.mly 
	ocamlyacc -v parser.mly

parser.cmx: parser.ml parser.cmi
	$(OCAMLC) -c $<

%.cmx: %.ml
	$(OCAMLC) -c $<

%.cmi: %.mli
	$(OCAMLC) -c $<

doc: $(LIBMODULES:%=%.cmx)
	rm -rf doc
	mkdir doc
	$(CAMLDOC) -html -d doc -v -stars -html -I . -I $(ZARITHLIB) -I $(CHUTIL)/cmi $(LIBMODULES:%=%.ml)

.PHONY : clean
clean: 
	rm -f *.cmi 
	rm -f *.cmx 
	rm -f *.mli 
	rm -f *.o
	rm -f chifparser
	rm -f *.cmxa
	rm -f Makefile~
	rm -f lexer.ml
	rm -f parser.ml
	rm -rf doc

.PHONY : run
run:
	./parsechif -file sample.chif

.PHONY : debug
debug:
	OCAMLRUNPARAM=p ./parsechif -file sample.chif
