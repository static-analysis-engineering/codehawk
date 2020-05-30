CODEHAWK = ../..
CHB = $(CODEHAWK)/CHB

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHUTIL = $(CODEHAWK)/CH/chutil
CHGUI  = $(CODEHAWK)/CH_gui
XPRLIB = $(CODEHAWK)/CH/xprlib
BCHLIB = $(CHB)/bchlib
PELIB  = $(CHB)/bchlibpe
ELFLIB = $(CHB)/bchlibelf
X86LIB = $(CHB)/bchlibx86
MIPS32LIB = $(CHB)/bchlibmips32
ANALYZ = $(CHB)/bchanalyze

CAMLDOC := ocamldoc

GTKLIB = $(shell ocamlfind query lablgtk2)
ZARITHLIB = $(shell ocamlfind query zarith)

DEP_INCLUDES := -I cmi -I cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(CHGUI) \
	-I $(BCHLIB)/cmi \
	-I $(PELIB)/cmi \
	-I $(ELFLIB)/cmi \
	-I $(X86LIB)/cmi \
	-I $(ANALYZ)/cmi \

INCLUDES := $(DEP_INCLUDES)

CAMLC := ocamlopt -I str -I cmi -I cmx \
	-I +lablgtk2 lablgtx.cmxa \
	-I +lablgnomecanvas $(GTKLIB)/lablgnomecanvas.cmxa gtkInit.cmx \
	-I $(GTKLIB)

CAMLBUILD := ocamlopt str.cmxa unix.cmxa \
	-I $(ZARITHLIB) \
	-I $(ZIPLIB) \
	-I $(GTKLIB) \
	$(ZARITHLIB)/zarith.cmxa \
	$(GTKLIB)/lablgtk.cmxa \
	$(GTKLIB)/gtkInit.cmx \
	$(GTKLIB)/lablgnomecanvas.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(EXTLIB)/extLib.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(CHGUI)/canvaslib.cmxa \
	$(BCHLIB)/bchlib.cmxa \
	$(PELIB)/bchlibpe.cmxa \
	$(ELFLIB)/bchlibelf.cmxa \
	$(X86LIB)/bchlibx86.cmxa \
	$(MIPS32LIB)/bchlibmips32.cmxa \
	$(ANALYZ)/bchanalyze.cmxa \

MLIS := \
	bCHCanvasItems \
	bCHGuiUtil \
	bCHControlFlowGraph \
	bCHSystemDisplay \
	bCHCanvasCallgraph \
	bCHOrphanCode \
	bCHCanvasUtil \
	bCHStackFrame  \
	bCHDllFunctionsDisplay \
	bCHStateDialogs \
	bCHFunctionsDisplay \
	bCHGui \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	bCHCanvasItems \
	bCHGuiUtil \
	bCHControlFlowGraph \
	bCHSystemDisplay \
	bCHCanvasCallgraph \
	bCHOrphanCode \
	bCHCanvasUtil \
	bCHStackFrame \
	bCHDllFunctionsDisplay \
	bCHStateDialogs \
	bCHFunctionsDisplay \
	bCHGui

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs gui

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

gui: $(OBJECTS) $(CMIS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(X86LIB)/bchlibx86.cmxa $(MIPS32LIB)/bchlibmips32.cmxa $(ANALYZ)/bchanalyze.cmxa cmx/bch_maingui.cmx
	$(CAMLBUILD) -o chx86_gui $(OBJECTS) cmx/bch_maingui.cmx

cmi/%.cmi: %.mli
	$(CAMLC) $(INCLUDES) -o $@ -c $<

cmx/%.cmx: %.ml $(CMIS)
	$(CAMLC) $(INCLUDES) -o $@ -c $<

doc: $(MODULES:%=%.cmx)
	rm -rf doc
	mkdir doc
	$(CAMLDOC) -html -d doc -v -stars -html -I . \
	-I $(EXTLIB) \
	-I $(CHLIB) \
	-I $(CHUTIL) \
	-I $(XPRLIB) \
	-I $(CHGUI) \
	-I $(X86LIB) \
	-I $(ELFLIB) \
	-I $(ANALYSISLIB) \
	-I $(GTKLIB) \
        $(MODULES:%=%.ml)

clean:
	rm -f cmx/*.cmx
	rm -f cmx/*.cmi
	rm -f cmi/*.cmi
	rm -f cmx/*.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.ml~
	rm -f *.mli~
	rm -f Makefile~ 
	rm -rf chx86_gui
	rm -rf doc

