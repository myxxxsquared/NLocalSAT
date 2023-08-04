#!/bin/sh

set -x
set -e

. finalexps/expenvs

# python gen_predict.py \
#     -i ${DATA_FOLDER}/eval \
#     -o ${DATA_FOLDER}/eval-direct \
#     -l train_origin_finalexp/debug-83616 \
#     -g 1

LD_LIBRARY_PATH=${CONDA_PREFIX}/lib \
exec python run_sat.py \
    -I${DATA_FOLDER}/eval \
    -Orun/final_direct \
    '-SCCAnrWithPredict/build/withpredict/CCAnrWithPredict --inst "{problem}" --predict_file "{predict}" --gpu "0" --load_model "train_main/debug-180480"' \
    -N12 \
    -T1000 \
    -p ${DATA_FOLDER}/eval-direct
