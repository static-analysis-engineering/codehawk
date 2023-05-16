#!/bin/bash
set -e
make -C cchcil
make -C cchlib
make -C cchpre
make -C cchanalyze
make -C cchcmdline
