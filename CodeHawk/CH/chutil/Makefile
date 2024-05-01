CHLIB = ../chlib
EXTLIB = $(shell ocamlfind query extlib)
ZARITHLIB = $(shell ocamlfind query zarith)

CAMLC := ocamlopt -I +unix -I cmi -I cmx \
	-I $(CHLIB)/cmi \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \

CAMLLINK := ocamlopt 
CAMLDOC := ocamldoc
OCAMLDEP := ocamldep

MLIS := \
	cHTraceResult \
	cHTimingLog \
	cHPrettyUtil \
	cHSumTypeSerializer \
	cHTiming \
	cHGc \
	cHMemoryRecorder \
	cHNestedCommands \
	cHMaps \
	cHUtil \
	cHLogger \
	cHXmlDocument \
	cHXmlReader \
	cHIndexTable \
	cHNumRecordTable \
	cHStringIndexTable \
	cHInvAccess \
	cHInvStore \
	cHAnalysisSetup \
	cHReportUtil \
	cHStats \
	cHDot \
	cHFileIO \
	cHCHIFXml \
	cHLoopStructure \
	cHNumConstraintPrinter \
	cHFormatStringParser \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	cHTraceResult \
	cHTimingLog \
	cHPrettyUtil \
	cHSumTypeSerializer \
	cHTiming \
	cHGc \
	cHMemoryRecorder \
	cHNestedCommands \
	cHMaps \
	cHUtil \
	cHLogger \
	cHXmlDocument \
	cHXmlReader \
	cHIndexTable \
	cHNumRecordTable \
	cHStringIndexTable \
	cHInvAccess \
	cHInvStore \
	cHAnalysisSetup \
	cHStats \
	cHDot \
	cHFileIO \
	cHCHIFXml \
	cHReportUtil \
	cHLoopStructure \
	cHNumConstraintPrinter \
	cHFormatStringParser \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: chutil.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

chutil.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa  $(EXTLIB)/extlib.cmxa $(ZARITHLIB)/zarith.cmxa
	$(CAMLLINK) -a -o $@ $(OBJECTS)

cmi/%.cmi: %.mli make_dirs
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml make_dirs
	$(CAMLC) -o $@ -c $<


xmlreader: chutil.cmxa mainXmlReader.cmx
	$(CAMLLINK) -o xmlreader unix.cmxa $(EXTLIB)/extlib.cmxa $(CHLIB)/chlib.cmxa chutil.cmxa mainXmlReader.cmx

doc: $(OBJECTS)
	rm -rf doc
	mkdir doc
	$(CAMLDOC) -html -d doc -v -stars -html -I . -I ../chlib $(OBJECTS)

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
