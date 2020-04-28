#!/bin/sh
#unzip ../archives/yalsat*
mv yalsat* yalsat
cd yalsat
./configure.sh
make yalsat
install -s yalsat ../../bin/
