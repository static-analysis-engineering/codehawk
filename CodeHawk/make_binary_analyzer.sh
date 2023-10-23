#!/bin/bash
set -e
make -C CH/chlib
make -C CH/chutil
make -C CH/xprlib
make -C CHB/bchlib
make -C CHB/bchcil
make -C CHB/bchlibpe
make -C CHB/bchlibelf
make -C CHB/bchlibx86
make -C CHB/bchlibmips32
make -C CHB/bchlibarm32
make -C CHB/bchlibpower32
make -C CHB/bchanalyze
make -C CHB/bchcmdline
