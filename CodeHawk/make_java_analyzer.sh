#!/bin/bash
set -e
make -C CH_extern/extlib
make -C CH_extern/camlzip
make -C CH/chlib
make -C CH/chutil
make -C CH/xprlib
make -C CH_gui
make -C CHJ/jchlib
make -C CHJ/jchpre
make -C CHJ/jchsys
make -C CHJ/jchpoly
make -C CHJ/jchfeatures
make -C CHJ/jchmuse
make -C CHJ/jchcost
make -C CHJ/jchcmdline
make -C CHJ/jchstac
make -C CHJ/jchstacgui
