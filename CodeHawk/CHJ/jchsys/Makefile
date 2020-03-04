CODEHAWK = ../..
JCH = ..

ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
JCHLIB = $(JCH)/jchlib
JCHPRE = $(JCH)/jchpre

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \


MLIS := \
        jCHGlobals \
	jCHSplitArray \
        jCHPrintUtils \
	jCHSystemUtils \
	jCHCodeTransformers \
	jCHVarInfoCollectors \
        jCHTransformUtils \
        jCHCallGraph \
	jCHDominance \
        jCHSSA \
	jCHVarRepresentative \
	jCHLoopUtils \
	jCHRevDominance \
	jCHTypeUtils \
	jCHVarInfo \
        jCHAnalysisSetUp \
	jCHProcInfo \
	jCHSystem \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
        jCHGlobals \
	jCHSplitArray \
        jCHPrintUtils \
	jCHSystemUtils \
	jCHCodeTransformers \
	jCHVarInfoCollectors \
        jCHTransformUtils \
        jCHCallGraph \
	jCHDominance \
        jCHSSA \
	jCHVarRepresentative \
	jCHLoopUtils \
	jCHRevDominance \
	jCHTypeUtils \
	jCHVarInfo \
        jCHAnalysisSetUp \
	jCHProcInfo \
	jCHSystem \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs jchsys

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi


jchsys: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(ZIPLIB)/zip.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLC) -a -o jchsys.cmxa $(OBJECTS)

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
