#!/bin/sh

set -x
set -e

. finalexps/expenvs



exec python sat.py \
    --logdir=train_origin_finalexp \
    --gpu_list=1 \
    --train_steps=10000000 \
    --save_data_path= \
    --train_data=${DATA_FOLDER}/train-data \
    --eval_data=${DATA_FOLDER}/vaildation-data \
    --eval_data_size=42 \
    --train_length=134
