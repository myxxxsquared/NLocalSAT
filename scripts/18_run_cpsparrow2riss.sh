#!/bin/sh

set -x
set -e

. finalexps/expenvs

LD_LIBRARY_PATH=${CONDA_PREFIX}/lib exec python run_sat.py \
    -I${DATA_FOLDER}/eval \
    -Orun/sparrow2riss \
    '-S/home/zwj/new-solvers/Sparrow2Riss-2018/bin/starexec_run_default "{problem}" run/sparrow2riss_tmp/{filename}' \
    -N12 \
    -T1000

