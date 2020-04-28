#!/bin/sh

# remove binary directory
rm -rf binary

#clean Coprocessor
cd code/Coprocessor;
make clean

# clean Sparrow
cd ../Sparrow
make clean

# return to calling directory
cd ..
