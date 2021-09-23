CODEHAWK = ../..
JCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

EXTLIB = $(shell ocamlfind query extlib)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
JCHLIB = $(JCH)/jchlib
JCHPRE = $(JCH)/jchpre
JCHSYS = $(JCH)/jchsys
JCHPOLY = $(JCH)/jchpoly

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \
	-I $(JCHSYS)/cmi \
	-I $(JCHPOLY)/cmi \

MLIS = \
	jCHCostAPI \
	jCHOpcodeCosts \
	jCHCostModelUtil \
	jCHCostUtils \
	jCHCostBound \
	jCHCostBounds \
	jCHCostBoundsModel \
	jCHLoopCostAbstractor \
	jCHMethodCostBoundsAbstractor \
	jCHCostBoundsDomainNoArrays \
	jCHCostBoundsAnalysis

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES = \
	jCHOpcodeCosts \
	jCHCostModelUtil \
	jCHCostUtils \
	jCHCostBound \
	jCHCostBounds \
	jCHCostBoundsModel \
	jCHLoopCostAbstractor \
	jCHMethodCostBoundsAbstractor \
	jCHCostBoundsDomainNoArrays \
	jCHCostBoundsAnalysis

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs jchcost

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

jchcost: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa $(JCHSYS)/jchsys.cmxa $(JCHPOLY)/jchpoly.cmxa
	$(CAMLC) -a -o jchcost.cmxa $(OBJECTS)

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
