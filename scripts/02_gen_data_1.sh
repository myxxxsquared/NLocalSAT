

set -x
set -e

. finalexps/expenvs

python gen_split.py \
    -i "${DATA_FOLDER}/train" \
    -o "${DATA_FOLDER}/train-split" \
    -l "${DATA_FOLDER}/train-split.csv" \
    -e 10000 \
    -m 3.0

python gen_split.py \
    -i "${DATA_FOLDER}/vaildation" \
    -o "${DATA_FOLDER}/vaildation-split" \
    -l "${DATA_FOLDER}/vaildation-split.csv" \
    -e 10000 \
    -m 3.0


python gen_rename.py \
    -i "${DATA_FOLDER}/train-split" \
    -o "${DATA_FOLDER}/train-refine" \
    -e "./minisatsimplifier/build/minisatsimplifier" \
    -l "${DATA_FOLDER}/train-refine.csv" \
    -N 16 \
    -p 0

python gen_rename.py \
    -i "${DATA_FOLDER}/vaildation-split" \
    -o "${DATA_FOLDER}/vaildation-refine" \
    -e "./minisatsimplifier/build/minisatsimplifier" \
    -l "${DATA_FOLDER}/vaildation-refine.csv" \
    -N 16 \
    -p 0

python gen_solve.py \
    -i "${DATA_FOLDER}/train-refine" \
    -b "/home/zwj/new-solvers" \
    -s MapleLCMDistChronoBT gluHack \
    -t 600

python gen_solve.py \
    -i "${DATA_FOLDER}/vaildation-refine" \
    -b "/home/zwj/new-solvers" \
    -s MapleLCMDistChronoBT gluHack \
    -t 600
