CODEHAWK := ../..
JCH = ..

EXTLIB = $(shell ocamlfind query extlib)
ZIPLIB = $(shell ocamlfind query zip)
CHLIB  = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
CHGUI  = $(CODEHAWK)/CH_gui
JCHLIB = $(JCH)/jchlib
JCHPRE = $(JCH)/jchpre
JCHSYS = $(JCH)/jchsys
JCHPOLY= $(JCH)/jchpoly
JCHCOST= $(JCH)/jchcost

GTKLIB = $(shell ocamlfind query lablgtk2)
ZARITHLIB = $(shell ocamlfind query zarith)

DEP_INCLUDES := -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(CHGUI) \
	-I $(JCHLIB)/cmi \
	-I $(JCHPRE)/cmi \
	-I $(JCHSYS)/cmi \
	-I $(JCHPOLY)/cmi \
	-I $(JCHCOST)/cmi \

INCLUDES := $(DEP_INCLUDES)

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I +lablgtk2 lablgtx.cmxa \
	-I +lablgnomecanvas $(GTKLIB)/lablgnomecanvas.cmxa gtkInit.cmx \
	-I $(GTKLIB)

CAMLBUILD := ocamlopt str.cmxa unix.cmxa \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(GTKLIB) \
	$(ZARITHLIB)/zarith.cmxa \
        $(GTKLIB)/lablgtk.cmxa \
        $(GTKLIB)/gtkInit.cmx \
        $(GTKLIB)/lablgnomecanvas.cmxa \
	$(EXTLIB)/extLib.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CHGUI)/canvaslib.cmxa \
	$(JCHLIB)/jchlib.cmxa \
	$(JCHPRE)/jchpre.cmxa \

MLIS := \
	jCHGuiUtil \
	jCHCostValues \
	jCHBCFunctions \
	jCHControlFlowGraph \
	jCHSystemDisplay  \
	jCHCanvasCallgraph \
	jCHCanvasUtil \
	jCHDialogWindow \
	jCHMethodsDisplay \
	jCHGui \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	jCHGuiUtil \
	jCHCostValues \
	jCHBCFunctions \
	jCHControlFlowGraph \
	jCHSystemDisplay \
	jCHCanvasCallgraph \
	jCHCanvasUtil \
	jCHDialogWindow \
	jCHMethodsDisplay \
	jCHGui \

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))


CAMLDOC := ocamldoc
JAVAC = javac

all: make_dirs jch_gui

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi


jch_gui: $(CMIS) $(OBJECTS) cmi/jCHXStacGui.cmi cmx/jCHXStacGui.cmx $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(JCHLIB)/jchlib.cmxa $(JCHPRE)/jchpre.cmxa $(JCHCOST)/jchcost.cmxa
	$(CAMLBUILD) -o chj_gui $(OBJECTS) cmx/jCHXStacGui.cmx

cmi/%.cmi: %.mli
	$(CAMLC) $(INCLUDES) -o $@ -c $<

cmx/%.cmx: %.ml
	$(CAMLC) $(INCLUDES) -o $@ -c $<

cleanjava:
	rm -f *.class

clean:
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f */*.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.exe
	rm -f *.ml~
	rm -f Makefile~
	rm -f chj_gui
