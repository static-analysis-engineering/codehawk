CODEHAWK = ../..
CIL = $(shell ocamlfind query goblint-cil)
ZARITHLIB = $(shell ocamlfind query zarith)


CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(shell ocamlfind query extlib)

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(ZARITHLIB) \
	-I $(CIL) \
	-I $(EXTLIB)

CAMLLINK := ocamlopt  \
	$(EXTLIB)/extLib.cmxa \

CAMLLINKLIB := ocamlopt  \

MLIS := \
	cHPrettyPrint \
	cHUtilities \
	cHFileUtil \
	cHCMaps \
	cHXml \
	cHCIndexTable \
	cHCStringIndexTable \
	cHSumTypeSerializer \
	cHCilTypes \
	cHDictionary \
	cHDeclarations \
	cHFunDeclarations \
	cHWriteXml

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	cHPrettyPrint \
	cHUtilities \
	cHFileUtil \
	cHCMaps \
	cHXml \
	cHCIndexTable \
	cHCStringIndexTable \
	cHSumTypeSerializer \
	cHDictionary \
	cHDeclarations \
	cHFunDeclarations \
	cHWriteXml \
	cCHXParseFile \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs parse cchcil

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

parse: 	$(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CIL)/cil.cmxa $(EXTLIB)
	$(CAMLLINK) -I $(ZARITHLIB) -o parseFile str.cmxa unix.cmxa $(ZARITHLIB)/zarith.cmxa $(CIL)/cil.cmxa $(CHLIB)/chlib.cmxa $(OBJECTS)

cchcil: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CIL)/cil.cmxa $(EXTLIB)
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
