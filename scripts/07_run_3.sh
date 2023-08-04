#!/bin/sh

set -x
set -e

. finalexps/expenvs

exec python run_sat.py \
    -I${DATA_FOLDER}/eval \
    -Orun/cpsparrow_o \
    '-SCPSparrow/bin/CPSparrow.sh "{problem}" 1982 run/cpsparrow_o_tmp/{filename}' \
    -N12 \
    -T1000
