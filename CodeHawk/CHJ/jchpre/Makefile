CODEHAWK = ../..
JCH = ..

EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
JCHLIB = $(JCH)/jchlib

CAMLC := ocamlopt -I +str -I +unix -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \

MLIS = \
	jCHPreAPI \
	jCHUserData \
	jCHPreSumTypeSerializer \
	jCHIFSemantics \
	jCHSignatureBindings \
	jCHCodegraph \
	jCHSystemSettings \
	jCHClassSummary \
	jCHBytecodeLocation \
	jCHBcPattern \
	jCHInvariant \
	jCHFieldInfo \
	jCHClassInfo \
	jCHFunctionSummary \
	jCHMethodInfo \
	jCHBCFunction \
	jCHStackSlotValue \
	jCHBytecodeData \
	jCHInstructionInfo \
	jCHFunctionSummaryXmlDecoder \
	jCHFunctionSummaryLibrary \
	jCHApplication \
	jCHBcPatternSummary \
	jCHClassUserTemplate \
	jCHTaintOrigin \
	jCHCGDictionary \
	jCHMethodImplementations \
	jCHCallgraphBase \
	jCHTemplateUtil \
	jCHClassSummaryTemplate \
	jCHAPISummaryTemplate \
	jCHProfileSummaryTemplate \
	jCHSupplementSummary \
	jCHIntegrateSummaries \
	jCHPreFileIO \
	jCHCHAUtil \
	jCHMethodAssumptions \
	jCHIFSystem \
	jCHLoops \
	jCHTypeSets \
	jCHTypeSetsDomainNoArrays \
	jCHStringSets \
	jCHStringSetsDomainNoArrays \
	jCHAnalysisResults \
	jCHClassAnalysis \
	jCHClassLoader \
	jCHAnnotationsPre \
	jCHNativeMethods \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES = \
	jCHPreSumTypeSerializer \
	jCHIFSemantics \
	jCHSignatureBindings \
	jCHCodegraph \
	jCHSystemSettings \
	jCHClassSummary \
	jCHBytecodeLocation \
	jCHInvariant \
	jCHFieldInfo \
	jCHMethodInfo \
	jCHClassInfo \
	jCHBCFunction \
	jCHStackSlotValue \
	jCHFunctionSummary \
	jCHInstructionInfo \
	jCHFunctionSummaryXmlDecoder \
	jCHFunctionSummaryLibrary \
	jCHApplication \
	jCHBcPattern \
	jCHBcPatternSummary \
	jCHClassUserTemplate \
	jCHTaintOrigin \
	jCHCGDictionary \
	jCHMethodImplementations \
	jCHBytecodeData \
	jCHUserData \
	jCHCallgraphBase \
	jCHPreFileIO \
	jCHCHAUtil \
	jCHIFSystem \
	jCHLoops \
	jCHTemplateUtil \
	jCHClassSummaryTemplate \
	jCHAPISummaryTemplate \
	jCHProfileSummaryTemplate \
	jCHSupplementSummary \
	jCHIntegrateSummaries \
	jCHMethodAssumptions \
	jCHTypeSets \
	jCHTypeSetsDomainNoArrays \
	jCHStringSets \
	jCHStringSetsDomainNoArrays \
	jCHClassAnalysis \
	jCHClassLoader \
	jCHAnnotationsPre \
	jCHAnalysisResults \
	jCHNativeMethods \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs jchpre

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

jchpre: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa
	$(CAMLC) -a -o jchpre.cmxa $(OBJECTS)

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

