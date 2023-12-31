CODEHAWK = ../..
JCH = ..

ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(shell ocamlfind query extlib)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
JCHLIB = $(JCH)/jchlib
JCHPRE = $(JCH)/jchpre
JCHSYS = $(JCH)/jchsys

CAMLC := ocamlopt -I +str -I +unix -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \
	-I $(JCHSYS)/cmi \

OCAMLDEP := ocamldep


MLIS := \
        jCHAnalysisUtils \
	jCHFields \
	jCHCollectors \
	jCHNumericInfo \
	jCHIntervalArray \
	jCHArrayUtils \
	jCHNumericUtils \
	jCHLinearConstraint \
	jCHPoly \
	jCHPolyIntervalArray \
	jCHIntStubs \
	jCHPolyIntDomainNoArrays \
	jCHNumericAnalysis \
	jCHTaintLoopUtils \
	jCHTNode \
	jCHTGraph \
	jCHTGraphStubs \
	jCHTGraphTransformers \
	jCHTGraphAnalysis \
	jCHTOriginGraphs \
	jCHAnalysis \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
        jCHAnalysisUtils \
	jCHFields \
	jCHCollectors \
	jCHNumericInfo \
	jCHIntervalArray \
	jCHArrayUtils \
	jCHNumericUtils \
	jCHLinearConstraint \
	jCHPoly \
	jCHPolyIntervalArray \
	jCHIntStubs \
	jCHPolyIntDomainNoArrays \
	jCHNumericAnalysis \
	jCHTaintLoopUtils \
	jCHTNode \
	jCHTGraph \
	jCHTGraphStubs \
	jCHTGraphTransformers \
	jCHTGraphAnalysis \
	jCHTOriginGraphs \
	jCHAnalysis \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: jchpoly.cmxa

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi


jchpoly.cmxa: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa $(JCHSYS)/jchsys.cmxa
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
