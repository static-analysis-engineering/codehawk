CODEHAWK = ../..
CCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib

CAMLC := ocamlopt -I str -I cmi -I cmx \
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
	cCHFileContract \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
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
	cCHFileContract \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs cchlib

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

cchlib: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(XPRLIB)/xpr.cmxa
	$(CAMLLINK) -a -o cchlib.cmxa $(OBJECTS)


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
