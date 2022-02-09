#!/bin/bash
set -e
make -C bchcil clean
make -C bchlib clean
make -C bchlibpe clean
make -C bchlibelf clean
make -C bchlibx86 clean
make -C bchlibmips32 clean
make -C bchlibarm32 clean
make -C bchanalyze clean
make -C bchcmdline clean
