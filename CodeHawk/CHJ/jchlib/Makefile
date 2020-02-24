CODEHAWK = ../..
JCH = ..

ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \

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

all: make_dirs jchlib

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

jchlib: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa
	$(CAMLC) -a -o jchlib.cmxa $(OBJECTS)

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
