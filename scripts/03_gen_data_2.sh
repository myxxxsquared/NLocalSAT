#!/bin/sh

set -x
set -e

. finalexps/expenvs


python gen_solve.py \
    -i "${DATA_FOLDER}/train" \
    -b "/home/zwj/new-solvers" \
    -s CCAnr \
    -t 600 \
    -N 16

python gen_solve.py \
    -i "${DATA_FOLDER}/vaildation" \
    -b "/home/zwj/new-solvers" \
    -s MapleLCMDistChronoBT gluHack CCAnr \
    -t 600 \
    -N 8

python gen_gather_solution.py \
    -i "${DATA_FOLDER}/train" #\
    -S 10000

python gen_gather_solution.py \
    -i "${DATA_FOLDER}/vaildation" #\
    -S 10000
