CODEHAWK = ..

CHLIB = $(CODEHAWK)/CH/chlib
CHUTIL = $(CODEHAWK)/CH/chutil
EXTLIB = $(CODEHAWK)/CH_extern/extlib

# ----------------------------------------------------------------------------
# Note for Mac installation:
# if using macports to install lablgtk2 it may be necessary to revert
# to an older version of camlp4 because of an inconsistency with lablgtk2
# in the latest version:
# $ svn checkout -r 131008 https://svn.macports.org/repository/macports/trunk/dports/lang/ocaml-camlp4
# $ cd ocaml-camlp4 ; sudo port install ; cd ..
# and install lablgtk2 with sources:
# sudo port install -s lablgtk2
# -----------------------------------------------------------------------------
GTKLIB = $(shell ocamlfind query lablgtk2)

CAMLDOC := ocamldoc

CAMLC := ocamlopt \
	-p \
	-I nums \
	-I $(EXTLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \

CAMLCG := ocamlopt \
	-p \
	-I $(EXTLIB) \
	-I $(CHLIB)/cmi \
	-I $(CHUTIL)/cmi \
	-I $(GTKLIB) \
	-I +lablgtk2 lablgtk.cmxa

CAMLLINK := ocamlopt unix.cmxa str.cmxa nums.cmxa \
	$(EXTLIB)/extLib.cmxa $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa \

CAMLLINKGMAIN := ocamlopt unix.cmxa str.cmxa nums.cmxa \
	$(EXTLIB)/extLib.cmxa $(CHLIB)/chlib.cmxa $(CHUTIL)/chutil.cmxa \
	-I +lablgtk2 lablgtk.cmxa lablgnomecanvas.cmxa gtkInit.cmx

CAMLLINKG := ocamlopt -I $(EXTLIB) -I $(CHLIB) \
	-I +lablgtk2 -I +lablgnomecanvas

GUILIBMLIS := \
	cHCanvasBase

GUILIBMODULES := \
	cHCanvasBase

GUIMLIS := \
	cHCanvas

GUIMODULES := \
	cHCanvas 

all: canvaslib.cmxa 

canvaslib.cmxa: $(GUILIBMLIS:%=%.cmi) $(GUILIBMODULES:%=%.cmx)
	$(CAMLLINKG) -a -o canvaslib.cmxa $(GUILIBMODULES:%=%.cmx) 

jch_gui.cmxa: $(GUIMLIS:%=%.cmi) $(GUIMODULES:%=%.cmx)
	$(CAMLLINKG) -a -o jch_gui.cmxa $(GUIMODULES:%=%.cmx)

%.cmx: %.ml
	$(CAMLCG) -c $<

%.cmi: %.mli
	$(CAMLCG) -c $<

doc: $(GUILIBMODULES:%=%.cmx) $(GUIMODULES:%=%.cmx)
	rm -rf doc
	mkdir doc
	$(CAMLDOC) -html -d doc -v -stars -html -I . -I $(EXTLIB) \
	-I $(CHLIB) \
	-I $(CHUTIL) $(GUILIBMODULES:%=%.ml) $(GUIMODULES:%=%.ml)

clean:
	rm -f *.cmx
	rm -f *.cmi
	rm -f *.o
	rm -f *.a
	rm -f *.cmxa
	rm -f *.exe
	rm -f *.ml~
	rm -f *.mli~
	rm -f Makefile~
	rm -f jch_gui
	rm -rf doc

