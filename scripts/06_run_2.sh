#!/bin/sh

set -x
set -e

. finalexps/expenvs

exec python run_sat.py \
    -I${DATA_FOLDER}/eval \
    -Orun/final_o \
    '-SCCAnrWithPredict/build/withoutpredict/CCAnrWithPredict --inst "{problem}"' \
    -N12 \
    -T1000
