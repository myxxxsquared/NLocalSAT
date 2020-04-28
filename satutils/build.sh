#!/bin/sh

mkdir -p build
cd build
cmake .. -DCMAKE_PREFIX_PATH=$CONDA_PREFIX -DCMAKE_BUILD_TYPE=Release
make -j4
cp satutils.so ../../
