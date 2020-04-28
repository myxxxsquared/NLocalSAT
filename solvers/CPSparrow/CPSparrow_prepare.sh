#!/bin/bash
# CPSparrow.sh, Adrian Balint, 2014
#
# solve CNF formula $1 by simplifying first with coprocessor, then run the SAT solver Sparrow, and finally, reconstruct the model
#

#
# usage
#
if [ "x$1" = "x" -o "x$2" = "x"  -o "x$3" = "x" ]; then
  echo "USAGE: CPSparrow.sh <input CNF> <seed> <tempdir>"
  exit 1
fi

#
# variables for the script
#

file=$1 #instance
shift
seed=$1 #seed
shift
tmpDir=$1 #tempdir

mkdir -p $tmpDir

# binary of the used SAT solver
satsolver=sparrow						# name of the binary (if not in this directory, give relative path as well)

# default parameters for preprocessor
cp3params="-enabled_cp3 -cp3_stats -up -subsimp -bve -no-bve_gates -no-bve_strength -bve_red_lits=1 -cp3_bve_heap=1 -bve_heap_updates=1 -bve_totalG -bve_cgrow_t=1000 -bve_cgrow=10  -probe -no-pr-vivi -pr-bins -pr-lhbr -no-pr-nce"

# some temporary files 
undo=$tmpDir/cp_undo_$$				# path to temporary file that stores cp3 undo information
tmpCNF=$tmpDir/cp_tmpCNF_$$		# path to temporary file that stores cp3 simplified formula
model=$tmpDir/cp_model_$$			# path to temporary file that model of the preprocessor (stdout)
realModel=$tmpDir/model_$$			# path to temporary file that model of the SAT solver (stdout)
echo "c undo: $undo tmpCNF: $tmpCNF model: $model realModel: $realModel"

ppStart=0
ppEnd=0
solveStart=0
solveEnd=0

#
# run coprocessor with parameters added to this script
# and output to stdout of the preprocessor is redirected to stderr
#
ppStart=`date +%s`
CPSparrow/bin/coprocessor $file $realModel -enabled_cp3 -undo=$undo -dimacs=$tmpCNF $cp3params 1>&2
