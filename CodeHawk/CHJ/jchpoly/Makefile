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

all: make_dirs jchpoly

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi


jchpoly: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa $(JCHSYS)/jchsys.cmxa
	$(CAMLC) -a -o jchpoly.cmxa $(OBJECTS)

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
