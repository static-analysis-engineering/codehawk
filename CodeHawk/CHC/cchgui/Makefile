CODEHAWK = ../..
CCH = ..
ZARITHLIB = $(shell ocamlfind query zarith)

CHLIB  = $(CODEHAWK)/CH/chlib
EXTLIB = $(CODEHAWK)/CH_extern/extlib
ZIPLIB = $(CODEHAWK)/CH_extern/camlzip
CHUTIL = $(CODEHAWK)/CH/chutil
XPRLIB = $(CODEHAWK)/CH/xprlib
CCHLIB = $(CCH)/cchlib
CCHPRE = $(CCH)/cchpre
CCHANALYZE = $(CCH)/cchanalyze
CHGUI  = $(CODEHAWK)/CH_gui
GTKLIB = $(shell ocamlfind query lablgtk2)

CAMLC := ocamlopt -I str \
	-I +lablgtk2 lablgtx.cmxa \
	-I +lablgtk2 lablgtksourceview2.cmxa \
	-I +lablgnomecanvas $(GTKLIB)/lablgnomecanvas.cmxa gtkInit.cmx \
	-I $(EXTLIB) \
	-I $(ZIPLIB) \
	-I $(ZARITHLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(XPRLIB)/cmi \
	-I $(CHGUI) \
	-I $(CCHLIB)/cmi \
	-I $(CCHPRE)/cmi \
	-I $(GTKLIB) \

CAMLLINK := ocamlopt str.cmxa unix.cmxa \
	-I $(ZARITHLIB) \
	-I $(GTKLIB) \
	-I $(ZIPLIB) \
	$(ZARITHLIB)/zarith.cmxa \
	$(GTKLIB)/lablgtk.cmxa \
	$(GTKLIB)/lablgtksourceview2.cmxa \
	$(GTKLIB)/gtkInit.cmx \
	$(GTKLIB)/lablgnomecanvas.cmxa \
	$(CHLIB)/chlib.cmxa \
	$(EXTLIB)/extLib.cmxa \
	$(ZIPLIB)/zip.cmxa \
	$(CHUTIL)/chutil.cmxa \
	$(XPRLIB)/xpr.cmxa \
	$(CCHLIB)/cchlib.cmxa \
	$(CCHPRE)/cchpre.cmxa \
	$(CHGUI)/canvaslib.cmxa \

MLIS := \
	cCHInterrupt \
	cCHGtkUtils \
	cCHGuiUtils \
	cCHSystemDisplay \
	cCHGuiRequests \
	cCHGuiStats \
	cCHApiDialog \
	cCHPpoDialog \
	cCHFunctionsDisplay \
	cCHGui \

CMIS := $(addprefix cmi/,$(MLIS:%=%.cmi))

SOURCES := \
	cCHInterrupt \
	cCHGtkUtils \
	cCHGuiUtils \
	cCHSystemDisplay \
	cCHGuiRequests \
	cCHGuiStats \
	cCHApiDialog \
	cCHPpoDialog \
	cCHFunctionsDisplay \
	cCHGui

OBJECTS := $(addprefix cmx/,$(SOURCES:%=%.cmx))

all: make_dirs chc_gui

make_dirs:
	@mkdir -p cmx
	@mkdir -p cmi

chc_gui: $(CMIS) $(OBJECTS) $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa $(CCHPRE)/cchpre.cmxa cmx/chc_maingui.cmx
	$(CAMLLINK) -o chc_gui $(OBJECTS) cmx/chc_maingui.cmx

cmi/%.cmi: %.mli
	$(CAMLC) -o $@ -c $<

cmx/%.cmx: %.ml
	$(CAMLC) -I $(CCH)/cchgui/cmi -I $(CCH)/cchgui/cmx -o $@ -c $<

clean:
	rm -f *.cmx
	rm -f *.cmi
	rm -f */*.cmx
	rm -f */*.cmi
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.ml~
	rm -f *.mli~
	rm -f Makefile~
	rm -f chc_gui 
