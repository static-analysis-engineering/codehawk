CHLIB = ../chlib
EXTLIB = $(shell ocamlfind query extlib)
ZARITHLIB = $(shell ocamlfind query zarith)

CAMLC := ocamlopt -I cmi -I cmx \
	-I $(CHLIB)/cmi \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \

CAMLLINK := ocamlopt 
CAMLDOC := ocamldoc

MLIS := \
	cHTraceResult \
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

all: make_dirs chutil.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

chutil.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa  $(EXTLIB)/extlib.cmxa $(ZARITHLIB)/zarith.cmxa
	$(CAMLLINK) -a -o chutil.cmxa  $(OBJECTS)

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c -opaque $<

cmx/%.cmx: %.ml
	$(CAMLC) -o $@ -c $<


xmlreader: chutil.cmxa mainXmlReader.cmx
	$(CAMLLINK) -o xmlreader unix.cmxa $(EXTLIB)/extlib.cmxa $(CHLIB)/chlib.cmxa chutil.cmxa mainXmlReader.cmx

doc: $(OBJECTS)
	rm -rf doc
	mkdir doc
	$(CAMLDOC) -html -d doc -v -stars -html -I . -I ../chlib $(OBJECTS)

clean:
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f Makefile~
	rm -rf doc

