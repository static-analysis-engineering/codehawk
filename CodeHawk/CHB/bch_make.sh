#!/bin/bash
set -e
make -C bchcil
make -C bchlib
make -C bchlibpe
make -C bchlibelf
make -C bchlibx86
make -C bchlibmips32
make -C bchlibarm32
make -C bchanalyze
make -C bchcmdline
