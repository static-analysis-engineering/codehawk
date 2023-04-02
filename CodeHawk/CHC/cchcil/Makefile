CODEHAWK = ../..
CIL = $(shell ocamlfind query goblint-cil)
ZARITHLIB = $(shell ocamlfind query zarith)
EXTLIB = $(shell ocamlfind query extlib)

CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(ZARITHLIB) \
	-I $(CIL) \
	-I $(EXTLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \

CAMLLINK := ocamlopt  \
	-I $(ZARITHLIB) \
	$(EXTLIB)/extlib.cmxa \
	$(ZARITHLIB)/zarith.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \

CAMLLINKLIB := ocamlopt  \

MLIS := \
	cHCilFileUtil \
	cHCilTypes \
	cHCilSumTypeSerializer \
	cHCilDictionary \
	cHCilDeclarations \
	cHCilFunDeclarations \
	cHCilWriteXml \
	cCHXParseFile \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	cHCilFileUtil \
	cHCilSumTypeSerializer \
	cHCilDictionary \
	cHCilDeclarations \
	cHCilFunDeclarations \
	cHCilWriteXml \
	cCHXParseFile \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs parse cchcil

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

parse: 	$(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CIL)/goblintCil.cmxa $(EXTLIB) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa
	$(CAMLLINK) -I $(ZARITHLIB) -o parseFile str.cmxa unix.cmxa $(ZARITHLIB)/zarith.cmxa $(CIL)/goblintCil.cmxa $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(OBJECTS)

cchcil: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CIL)/goblintCil.cmxa $(EXTLIB) $(CHUTIL)/chutil.cmxa
	$(CAMLLINKLIB) -a -o cchcil.cmxa $(OBJECTS)


cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c $<

cmx/%.cmx: %.ml
	$(CAMLC) -o $@ -c $<

clean:
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~
	rm -f parseFile
