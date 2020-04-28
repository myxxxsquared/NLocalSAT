#!/bin/sh

mv yalsat* yalsat
cd yalsat
./configure.sh
make yalsat
install -s yalsat ../../bin/
