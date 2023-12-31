CODEHAWK = ../..
JCH = ..

ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil

CAMLC := ocamlopt -I +str -I +unix -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \

OCAMLDEP := ocamldep

MLIS := \
	jCHIFUtil \
	jCHBasicTypesAPI \
	jCHSumTypeSerializer \
	jCHBasicTypes \
	jCHSignature \
	jCHDictionary \
	jCHBcDictionary \
	jCHBytecode \
	jCHMethod \
	jCHClass \
	jCHRawBasicTypes \
	jCHRawClass \
	jCHParseCode \
	jCHInstruction \
	jCHParseUTF8Signature \
	jCHUnparseSignature \
	jCHDumpBasicTypes \
	jCHUnparse \
	jCHRaw2IF \
	jCHParse \
	jCHXmlUtil \
	jCHJTDictionary \
	jCHJTerm \
	jCHCopyPropagationNoArrays \
	jCHSimplify \
	jCHArrayInstantiation\
	jCHTransform \
	jCHTranslateToCHIF \
	jCHStackLayout \
	jCHFile

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	jCHIFUtil \
	jCHBasicTypes \
	jCHSumTypeSerializer \
	jCHSignature \
	jCHDictionary \
	jCHBytecode \
	jCHMethod \
	jCHClass \
	jCHRawBasicTypes \
	jCHParseCode \
	jCHInstruction \
	jCHParseUTF8Signature \
	jCHUnparseSignature \
	jCHDumpBasicTypes \
	jCHUnparse \
	jCHRaw2IF \
	jCHParse \
	jCHXmlUtil \
	jCHJTDictionary \
	jCHJTerm \
	jCHBcDictionary \
	jCHCopyPropagationNoArrays \
	jCHSimplify \
	jCHArrayInstantiation\
	jCHTransform \
	jCHTranslateToCHIF \
	jCHStackLayout \
	jCHFile

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: jchlib.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

jchlib.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa
	$(CAMLC) -a -o $@ $(OBJECTS)

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<

clean:
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
