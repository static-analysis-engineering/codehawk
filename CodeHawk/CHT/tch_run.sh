#!/bin/bash
set -e
make -C tchlib
make -C CH_tests/xprlib_tests/txprlib
make -C CH_tests/xprlib_tests/txxprlib run
make -C CHB_tests/bchlib_tests/tbchlib
make -C CHB_tests/bchlib_tests/txbchlib run
make -C CHB_tests/bchlibarm32_tests/tbchlibarm32
make -C CHB_tests/bchlibarm32_tests/txbchlibarm32 run
make -C CHB_tests/bchlibpower32_tests/txbchlibpower32 run
