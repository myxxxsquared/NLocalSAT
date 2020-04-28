#!/bin/bash
# pcasso.sh, Norbert Manthey, 2014
#
# solve CNF formula $1 by simplifying first with coprocessor, then run a SAT solver, and finally, reconstruct the model
# $2 points to the temporary directory (no trailing /)
#

# binary of the used SAT solver
satsolver=./pcasso						# name of the binary (if not in this directory, give full path)

#
# usage
#
if [ "x$1" = "x" ]; then
  echo "USAGE: cp.sh <input CNF> [arguments for cp3]"
  exit 1
fi

#
# variables for the script
#

file=$1											# first argument is CNF instance to be solved
shift												# reduce the parameters, removed the very first one. remaining $@ parameters are arguments
tmpDir=$1										# directory to write the temporary files to
shift												# reduce the parameters, removed the very first one. remaining $@ parameters are arguments

# default parameters for preprocessor
cpParams="-enabled_cp3 -cp3_stats -bve -bve_red_lits=1 -fm -no-cp3_fm_vMulAMO -unhide -cp3_uhdIters=5 -cp3_uhdEE -cp3_uhdTrans -bce -bce-cle -no-bce-bce -dense"

# some temporary files 
undo=$tmpDir/undo_$$						# path to temporary file that stores cp3 undo information
tmpCNF=$tmpDir/tmpCNF_$$				# path to temporary file that stores cp3 simplified formula
model=$tmpDir/model_$$					# path to temporary file that model of the preprocessor (stdout)
realModel=$tmpDir/realmodel_$$	# path to temporary file that model of the SAT solver (stdout)
echo "c undo: $undo tmpCNF: $tmpCNF model: $model realModel: $realModel"  1>&2

ppStart=0
ppEnd=0
solveStart=0
solveEnd=0

#
# run coprocessor with parameters added to this script
# and output to stdout of the preprocessor is redirected to stderr
#
ppStart=`date +%s`
#echo "call: ./coprocessor $file $realModel -enabled_cp3 -undo=$undo -dimacs=$tmpCNF $cpParams $@"
./coprocessor $file $realModel -enabled_cp3 -undo=$undo -dimacs=$tmpCNF $cpParams $@  1>&2
exitCode=$?
ppEnd=`date +%s`
echo "c preprocessed $(( $ppEnd - $ppStart)) seconds with exit code $exitCode" 1>&2
echo "c preprocessed $(( $ppEnd - $ppStart)) seconds with exit code $exitCode"

# solved by preprocessing
if [ "$exitCode" -eq "10" -o "$exitCode" -eq "20" ]
then 
	echo "c solved by preprocessor" 1>&2
else
	echo "c not solved by preprocessor -- do search" 1>&2
	if [ "$exitCode" -eq "0" ]
	then
		#
		# exit code == 0 -> could not solve the instance
		# dimacs file will be printed always
		# exit code could be 10 or 20, depending on whether coprocessor could solve the instance already
		#
	
		#
		# run your favorite solver (output is expected to look like in the SAT competition, s line and v line(s) )
		# and output to stdout of the sat solver is redirected to stderr
		#
		solveStart=`date +%s`
		$satsolver $tmpCNF $model -model -work-conflicts=-1 -work-timeout=-1 -split-mode=2 -split-timeout=1024 -presel-fac=0.1 -presel-min=64 -presel-max=1024 -fail-lit=2 -nec-assign=2 -num-iterat=3 -double-la -double-decay=0.95 -con-resolv=1 -bin-const -la-heur=4 -presel-heur=2 -clause-learn=2 -dir-prior=3 -child-count=7 -shrk-clause -var-eq=3 -split-method=1 -split-depth=0 -dseq -h-acc=3 -h-maxcl=7 -h-cl-wg=5 -h-upper=10900 -h-lower=0.1 -addcl-falserem=1 -shpool-size=15000 -shclause-size=2 -lbd-lt=2 -dyn-lbdsh -dyn-lbdshfac=0.5 -every-shpool -sh-delay=16 -receiver-filter=0 -stop-children -adp-presel -adp-preselL=50 -adp-preselS=7 -upd-actpol=2 -sort-split -tabu -pure-lit=2 -no-split-diver -spdiver-lim=4096 -satunsat-restart -learnt-worsening -learnt-unaryres -clean-delay=2 -sim-port -c-killing -load-split -threads=11  1>&2
		exitCode=$?
		solveEnd=`date +%s`
		echo "c solved $(( $solveEnd - $solveStart )) seconds, exit code: $exitCode" 1>&2
		echo "c first solution line: `cat $model | head -n 1`"
	
		#
		# undo the model
		# coprocessor can also handle "s UNSATISFIABLE"
		#
		echo "c post-process with cp3" 1>&2
		./coprocessor -post -undo=$undo -model=$model $cpParams > $realModel
	
		#
		# verify final output if SAT?
		#
		if [ "$exitCode" -eq "10" ]
		then
			echo "c verify model ..." 1>&2
#			./verify SAT $realModel $file
		fi
	else
		#
		# preprocessor returned some unwanted exit code
		#
		echo "c preprocessor has been unable to solve the instance" 1>&2
		#
		# run sat solver on initial instance
		# and output to stdout of the sat solver is redirected to stderr
		#
		solveStart=`date +%s`
		$satsolver $file $realModel -model -work-conflicts=-1 -work-timeout=-1 -split-mode=2 -split-timeout=1024 -presel-fac=0.1 -presel-min=64 -presel-max=1024 -fail-lit=2 -nec-assign=2 -num-iterat=3 -double-la -double-decay=0.95 -con-resolv=1 -bin-const -la-heur=4 -presel-heur=2 -clause-learn=2 -dir-prior=3 -child-count=7 -shrk-clause -var-eq=3 -split-method=1 -split-depth=0 -dseq -h-acc=3 -h-maxcl=7 -h-cl-wg=5 -h-upper=10900 -h-lower=0.1 -addcl-falserem=1 -shpool-size=15000 -shclause-size=2 -lbd-lt=2 -dyn-lbdsh -dyn-lbdshfac=0.5 -every-shpool -sh-delay=16 -receiver-filter=0 -stop-children -adp-presel -adp-preselL=50 -adp-preselS=7 -upd-actpol=2 -sort-split -tabu -pure-lit=2 -no-split-diver -spdiver-lim=4096 -satunsat-restart -learnt-worsening -learnt-unaryres -clean-delay=2 -sim-port -c-killing -load-split -threads=12 1>&2
		exitCode=$?
		solveEnd=`date +%s`
		echo "c solved $(( $solveEnd - $solveStart )) seconds" 1>&2
	fi
fi

#
# print times
#

echo "c pp-time: $(( $ppEnd - $ppStart)) solve-time: $(( $solveEnd - $solveStart ))" 1>&2

#
# print solution
#
cat $realModel;

#
# remove tmp files
#
rm -f $undo $undo.map $tmpCNF $model $realModel;

#
# return with correct exit code
#
echo "c exit with $exitCode"
exit $exitCode
