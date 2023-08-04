#!/bin/sh

set -x
set -e

. finalexps/expenvs

mkdir -p "${DATA_FOLDER}"

python gen_rename.py \
    -i "${RANDOM_TRAIN}" \
    -o "${DATA_FOLDER}" \
    -p0.1 \
    -l "${DATA_FOLDER}/copyinfo_train.csv" \
    -N1 \
    -Evaildation

mkdir -p "${DATA_FOLDER}/eval"

python gen_rename.py \
    -i "${RANDOM_EVAL}" \
    -o "${DATA_FOLDER}/eval" \
    -p0 \
    -l "${DATA_FOLDER}/copyinfo_eval.csv" \
    -N1 \
    -Teval

