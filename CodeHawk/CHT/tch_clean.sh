#!/bin/bash
set -e
make -C tchlib clean
make -C CH_tests/xprlib_tests/txprlib clean
make -C CH_tests/xprlib_tests/xprlib clean
make -C CHB_tests/bchlib_tests/tbchlib clean
make -C CHB_tests/bchlib_tests/bchlib clean
make -C CHB_tests/bchlibarm32_tests/tbchlibarm32 clean
make -C CHB_tests/bchlibarm32_tests/bchlibarm32 clean
make -C CHB_tests/bchlibpower32_tests/bchlibpower32 clean
