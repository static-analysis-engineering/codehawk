#!/bin/bash
set -e
make -C CH_extern/extlib clean
make -C CH_extern/camlzip clean
make -C CH/chlib clean
make -C CH/chutil clean
make -C CH/xprlib clean
make -C CHC/cil-1.7.3-develop clean
make -C CHC/cchcil clean
make -C CHC/cchlib clean
make -C CHC/cchpre clean
make -C CHC/cchanalyze clean
make -C CHC/cchcmdline clean
make -C CHB/bchlib clean
make -C CHB/bchlibpe clean
make -C CHB/bchlibelf clean
make -C CHB/bchlibx86 clean
make -C CHB/bchlibmips32 clean
make -C CHB/bchanalyze clean
make -C CHB/bchcmdline clean
