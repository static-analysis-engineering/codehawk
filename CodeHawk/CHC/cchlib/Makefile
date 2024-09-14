CODEHAWK = ../..
CCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib

CAMLC := ocamlopt -I +str -I +unix -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \

CAMLLINK := ocamlopt  \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(CHLIB) \
	-I $(CHUTIL) \
	-I $(XPRLIB) \

OCAMLDEP = ocamldep

MLIS := \
	cCHBasicTypes \
	cCHLibTypes \
	cCHIndexedCollections \
	cCHUtilities \
	cCHSettings \
	cCHMachineSizes \
	cCHFileEnvironment \
	cCHBasicUtil \
	cCHContext \
	cCHSumTypeSerializer \
	cCHDictionary \
	cCHDeclarations \
	cCHFunDeclarations \
	cCHTypesCompare \
	cCHTypesToPretty \
	cCHTypesTransformer \
	cCHCodewalker \
	cCHTypesSize \
	cCHTypesUtil \
	cCHBasicTypesXml \
	cCHInterfaceDictionary \
	cCHExternalPredicate \
	cCHFunctionSummary \
	cCHCAttributes \
	cCHFileContract \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	cCHUtilities \
	cCHIndexedCollections \
	cCHSettings \
	cCHMachineSizes \
	cCHFileEnvironment \
	cCHBasicUtil \
	cCHContext \
	cCHSumTypeSerializer \
	cCHDictionary \
	cCHDeclarations \
	cCHFunDeclarations \
	cCHTypesCompare \
	cCHTypesToPretty \
	cCHTypesTransformer \
	cCHCodewalker \
	cCHTypesSize \
	cCHTypesUtil \
	cCHBasicTypesXml \
	cCHInterfaceDictionary \
	cCHExternalPredicate \
	cCHFunctionSummary \
	cCHCAttributes \
	cCHFileContract \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: cchlib.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

cchlib.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(XPRLIB)/xpr.cmxa
	$(CAMLLINK) -a -o $@ $(OBJECTS)


cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

clean:
	rm -f .depend
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~	

.depend:
	$(OCAMLDEP) *.mli *.ml | sed "s|[^\t ]\+\.cmx|cmx/\0|" | sed "s|[^\t ]\+\.cmi|cmi/\0|" > .depend

include .depend

.PHONY: all make_dirs doc clean
