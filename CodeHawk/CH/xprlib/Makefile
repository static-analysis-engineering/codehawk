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

all: make_dirs xpr

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

xpr: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL.cmxa) $(ZARITHLIB)/zarith.cmxa
	$(CAMLLINK) -a -o xpr.cmxa  $(OBJECTS)

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml
	$(CAMLC) -o $@ -c $<

doc: $(OBJECTS)
	rm -rf doc
	mkdir doc
	$(CAMLDOC) -html -d doc -v -stars -html -I . -I $(CHUTIL) $(OBJECTS)

clean:
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~
	rm -rf doc


