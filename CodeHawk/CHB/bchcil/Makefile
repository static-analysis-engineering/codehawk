CODEHAWK = ../..
CIL = $(shell ocamlfind query goblint-cil)
ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(ZARITHLIB) \
	-I $(CIL) \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \

CAMLLINK := ocamlopt str.cmxa unix.cmxa \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CIL) \
	$(ZARITHLIB)/zarith.cmxa \
	$(EXTLIB)/extLib.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CIL)/cil.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \

CAMLLINKL := ocamlopt

MLIS := \
	bCHCBasicTypes \
	bCHCilTypes \
	bCHCilToCBasic \
	bCHBCSumTypeSerializer \
	bCHBCDictionary \
	bCHBCFunDeclarations \
	bCHBCWriteXml \
	bCHBCUtil \
	bCHBCFiles \
	bCHCTypeUtil \
	bCHParseCilFile \


CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHCilToCBasic \
	bCHBCSumTypeSerializer \
	bCHBCDictionary \
	bCHBCFunDeclarations \
	bCHBCWriteXml \
	bCHBCUtil \
	bCHBCFiles \
	bCHCTypeUtil \
	bCHParseCilFile \


OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs bchcil

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

bchcil: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CIL)/cil.cmxa $(EXTLIB)
	$(CAMLLINKL) -a -o bchcil.cmxa $(OBJECTS)

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

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
	rm -f bchcil.cmxa
