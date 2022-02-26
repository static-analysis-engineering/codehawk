#!/bin/bash
set -e
make -C CH/chlib
make -C CH/chutil
make -C CH/xprlib
make -C CHC/cchcil
make -C CHC/cchlib
make -C CHC/cchpre
make -C CHC/cchanalyze
make -C CHC/cchcmdline

