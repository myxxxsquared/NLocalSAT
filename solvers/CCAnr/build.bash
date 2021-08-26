#!/bin/bash

set -x
set -e

rm -rf build/

mkdir -p build build/withpredict build/withoutpredict

pushd build/withpredict
cmake ../../ -DCMAKE_PREFIX_PATH=$CONDA_PREFIX -DCMAKE_BUILD_TYPE=Release -DPython_FIND_STRATEGY=LOCATION
make
popd

pushd build/withoutpredict
cmake ../../ -DUSE_PREDICT=OFF -DCMAKE_PREFIX_PATH=$CONDA_PREFIX -DCMAKE_BUILD_TYPE=Release -DPython_FIND_STRATEGY=LOCATION
make
popd
