CODEHAWK = ../..
ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil

CAMLC := ocamlopt -I cmx -I cmi \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(ZARITHLIB) \

CAMLLINK := ocamlopt
CAMLDOC := ocamldoc
OCAMLDEP := ocamldep

MLIS := \
	xprTypes \
	xSumTypeSerializer \
	xprDictionary \
	xprt \
	xprToPretty \
	xprXml \
	xsimplify \
	xprUtil \
	xrewrite \
	xconsequence \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	xprt \
	xSumTypeSerializer \
	xprDictionary \
	xprToPretty \
	xprXml \
	xsimplify \
	xprUtil \
	xrewrite \
	xconsequence \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: xpr.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

xpr.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL.cmxa) $(ZARITHLIB)/zarith.cmxa
	$(CAMLLINK) -a -o $@ $(OBJECTS)

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

doc: $(OBJECTS)
	rm -rf doc
	mkdir doc
	$(CAMLDOC) -html -d doc -v -stars -html -I . -I $(CHUTIL) $(OBJECTS)

clean:
	rm -f .depend
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~
	rm -rf doc

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
