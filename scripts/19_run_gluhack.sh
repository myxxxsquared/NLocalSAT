#!/bin/sh

set -x
set -e

. finalexps/expenvs

LD_LIBRARY_PATH=${CONDA_PREFIX}/lib exec python run_sat.py \
    -I${DATA_FOLDER}/eval \
    -Orun/gluhack \
    '-S/home/zwj/new-solvers/gluHack/bin/starexec_run_default "{problem}"' \
    -N12 \
    -T1000

