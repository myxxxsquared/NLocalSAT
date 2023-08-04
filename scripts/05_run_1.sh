#!/bin/sh

set -x
set -e

. finalexps/expenvs

python gen_predict.py \
    -i ${DATA_FOLDER}/eval \
    -l train_finalexp/debug-189172 \
    -g 1

LD_LIBRARY_PATH=${CONDA_PREFIX}/lib \
exec python run_sat.py \
    -I${DATA_FOLDER}/eval \
    -Orun/final_p_more \
    '-SCCAnrWithPredict/build/withpredict/CCAnrWithPredict --inst "{problem}" --predict_file "{predict}" --gpu "0" --load_model "train_main/debug-180480"' \
    -N12 \
    -T1000 \
    -p ${DATA_FOLDER}/eval-predict
