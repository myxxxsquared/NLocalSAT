#!/bin/sh

set -x
set -e

. finalexps/expenvs

LD_LIBRARY_PATH=${CONDA_PREFIX}/lib exec python run_sat.py \
    -I${DATA_FOLDER}/eval \
    -Orun/cpsparrow_p \
    '-SCPSparrow/bin/CPSparrowp.sh "{problem}" 1982 run/cpsparrow_p_tmp/{filename} train_finalexp/debug-189172' \
    -N12 \
    -T1000

