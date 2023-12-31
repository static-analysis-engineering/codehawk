CODEHAWK = ../..
JCH = ..

ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(shell ocamlfind query extlib)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
JCHLIB = $(JCH)/jchlib
JCHPRE = $(JCH)/jchpre

CAMLC := ocamlopt -I +str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \

OCAMLDEP := ocamldep

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

all: jchsys.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi


jchsys.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa
	$(CAMLC) -a -o $@ $(OBJECTS)

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
