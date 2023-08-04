#!/bin/sh

set -x
set -e

. finalexps/expenvs

LD_LIBRARY_PATH=${CONDA_PREFIX}/lib exec python run_sat.py \
    -I/home/zwj/satsource_random/jupyter/tmps \
    -Orun/cpsparrow_p_more \
    '-SCPSparrow/bin/sparrowp -a -l -k -r1 {problem} 1982' \
    -N12 \
    -T1000

