/*****************************************************************************************[Main.cc]
 Glucose -- Copyright (c) 2009, Gilles Audemard, Laurent Simon
				CRIL - Univ. Artois, France
				LRI  - Univ. Paris Sud, France
 
Glucose sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
Glucose are exactly the same as Minisat on which it is based on. (see below).

---------------
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson
Copyright (c) 2013, Norbert Manthey, All rights reserved.

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <errno.h>

#include <signal.h>
#include <zlib.h>
#include <sys/resource.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "simp/SimpSolver.h"

#include "coprocessor-src/Coprocessor.h"

#include <iostream>

#include "VERSION" // include the file that defines the solver version

using namespace Minisat;

//=================================================================================================


void printStats(Solver& solver)
{
    double cpu_time = cpuTime();
    double mem_used = memUsedPeak();
    printf("c restarts              : %"PRIu64" (%"PRIu64" conflicts in avg)\n", solver.starts, solver.starts == 0 ? 0 : solver.conflicts/solver.starts );
    printf("c blocked restarts      : %"PRIu64" (multiple: %"PRIu64") \n", solver.nbstopsrestarts,solver.nbstopsrestartssame);
    printf("c last block at restart : %"PRIu64"\n",solver.lastblockatrestart);
    printf("c nb ReduceDB           : %"PRIu64"\n", solver.nbReduceDB);
    printf("c nb removed Clauses    : %"PRIu64"\n",solver.nbRemovedClauses);
    printf("c nb learnts DL2        : %"PRIu64"\n", solver.nbDL2);
    printf("c nb learnts size 2     : %"PRIu64"\n", solver.nbBin);
    printf("c nb learnts size 1     : %"PRIu64"\n", solver.nbUn);

    printf("c conflicts             : %-12"PRIu64"   (%.0f /sec)\n", solver.conflicts   , cpu_time == 0 ? 0 : solver.conflicts / cpu_time);
    printf("c decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", solver.decisions, solver.decisions == 0 ? 0 : (float)solver.rnd_decisions*100 / (float)solver.decisions, cpu_time == 0 ? 0 : solver.decisions / cpu_time );
    printf("c propagations          : %-12"PRIu64"   (%.0f /sec)\n", solver.propagations, cpu_time == 0 ? 0 : solver.propagations/cpu_time);
    printf("c conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", solver.tot_literals, solver.max_literals == 0 ? 0 : (solver.max_literals - solver.tot_literals)*100 / (double)solver.max_literals);
    printf("c nb reduced Clauses    : %"PRIu64"\n",solver.nbReducedClauses);
    printf("c Memory used           : %.2f MB\n", mem_used);
    printf("c CPU time              : %g s\n", cpu_time);
}


static Solver* solver;
static bool receivedInterupt = false;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) { solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("c *** INTERRUPTED ***\n");
//     if (solver->verbosity > 0){
//         printStats(*solver);
//         printf("\n"); printf("c *** INTERRUPTED ***\n"); }
    solver->interrupt();
    if( receivedInterupt ) _exit(1);
    else receivedInterupt = true;
}


//=================================================================================================
// Main:

int main(int argc, char** argv)
{
      setUsageHelp("c USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
        
#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
        IntOption    vv  ("MAIN", "vv",   "Verbosity every vv conflicts", 10000, IntRange(1,INT32_MAX));
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);
        StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));

  StringOption drupFile         ("PROOF", "drup", "Write a proof trace into the given file",0);
  StringOption opt_proofFormat  ("PROOF", "proofFormat", "Do print the proof format (print o line with the given format, should be DRUP)","DRUP");

  BoolOption   opt_checkModel ("MAIN", "checkModel", "verify model inside the solver before printing (if input is a file)", false);
        BoolOption   opt_modelStyle ("MAIN", "oldModel", "present model on screen in old format", false);
        BoolOption   opt_quiet      ("MAIN", "quiet", "Do not print the model", false);
	BoolOption   opt_parseOnly  ("MAIN", "parseOnly", "abort after parsing", false);
	BoolOption   opt_cmdLine    ("MAIN", "cmd", "print the relevant options", false);
  
  try {
        CoreConfig coreConfig;
	Coprocessor::CP3Config cp3config;
        coreConfig.parseOptions(argc, argv);
	cp3config.parseOptions(argc, argv);
	
	if( opt_cmdLine ) { // print the command line options
	  std::stringstream s;
	  coreConfig.configCall(s);
	  cp3config.configCall(s);
	  configCall(argc, argv, s);
	  cerr << "c tool-parameters: " << s.str() << endl;
	  exit(0);
	}
	
        SimpSolver S(coreConfig);
	S.setPreprocessor(&cp3config); // tell solver about preprocessor
	
        double initial_time = cpuTime();

        S.verbosity = verb;
        S.verbEveryConflicts = vv;

        parseOptions(argc, argv, true);

        // tell solver that it is parsing - no need to add clauses to proof twice
        S.parsing = 1;

        if (!pre) S.eliminate(true);

        S.verbosity = verb;
        
        S.verbEveryConflicts = vv;
        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);

    
        if (S.verbosity > 0){
	    printf("c ===========================[   riss (simp) %5.2f   ]=====================================================\n", solverVersion);
	    printf("c | Norbert Manthey. The use of the tool is limited to research only!                                     |\n");
	    printf("c | Based on Minisat 2.2 and Glucose 2.1  -- thanks!                                                      |\n");
	    printf("c | Contributors:                                                                                         |\n");
	    printf("c |      Kilian Gebhardt (BVE Implementation,parallel preprocessor)                                       |\n");
            printf("c ============================[ Problem Statistics ]=======================================================\n");
            printf("c |                                                                                                       |\n"); }
	
        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: CPU-time.\n");
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1)
                    printf("c WARNING! Could not set resource limit: Virtual memory.\n");
            } }
        
        if (argc == 1)
            printf("c Reading from standard input... Use '--help' for help.\n");

        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);

        // open file for proof
        S.drupProofFile = (drupFile) ? fopen( (const char*) drupFile , "wb") : NULL;
	if( opt_proofFormat && strlen(opt_proofFormat) > 0 && S.drupProofFile != NULL ) fprintf( S.drupProofFile, "o proof %s\n", (const char*)opt_proofFormat ); // we are writing proofs of the given format!
	
        parse_DIMACS(in, S);
        gzclose(in);
        FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;

        double parsed_time = cpuTime();
	if (S.verbosity > 0){
            printf("c |  Number of variables:       %12d                                                              |\n", S.nVars());
            printf("c |  Number of clauses:         %12d                                                              |\n", S.nClauses());
            printf("c |  Number of total literals:  %12d                                                              |\n", S.nTotLits());
            printf("c |  Parse time:                %12.2f s                                                            |\n", parsed_time - initial_time);
            printf("c |                                                                                                       |\n"); }

        if( opt_parseOnly ) exit(0); // simply stop here!
            
        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        //signal(SIGINT, SIGINT_interrupt);
        //signal(SIGXCPU,SIGINT_interrupt);

        // finished parsing -- any clauses added now needs to be added to proof
        S.parsing = 0;
        S.eliminate(true);
        double simplified_time = cpuTime();
        if (S.verbosity > 0){
            printf("c |  Simplification time:  %12.2f s                                                                 |\n", simplified_time - parsed_time);
            printf("c |                                                                                                       |\n"); }

        if (!S.okay()){
         if (res != NULL) {
	       if( opt_modelStyle ) fprintf(res, "UNSAT\n"), fclose(res);
	       else fprintf(res, "s UNSATISFIABLE\n"), fclose(res);
	     }
         // add the empty clause to the proof, close proof file
         if (S.drupProofFile != NULL) fprintf(S.drupProofFile, "0\n"), fclose(S.drupProofFile);

            if (S.verbosity > 0){
 	        printf("c =========================================================================================================\n");
                printf("c Solved by simplification\n");
                printStats(S);
                printf("\n"); }
            
                // choose among output formats!
                if( opt_modelStyle ) printf("UNSAT");
		                else printf("s UNSATISFIABLE\n");
	    cout.flush(); cerr.flush();
            exit(20);
        }

        if (dimacs){
            if (S.verbosity > 0)
                printf("c =======================================[ Writing DIMACS ]===============================================\n");
            S.toDimacs((const char*)dimacs);
            if (S.verbosity > 0)
                printStats(S);
            exit(0);
        }

        vec<Lit> dummy;
        lbool ret = S.solveLimited(dummy);
        
        if (S.verbosity > 0){
            printStats(S);
        }

	// check model of the formula
	if( ret == l_True && opt_checkModel && argc != 1 ) { // check the model if the formla was given via a file!
	  if( check_DIMACS(in, S.model) ) {
	    printf("c verified model\n");
	  } else {
	    printf("c model invalid -- turn answer into UNKNOWN\n");
	    ret = l_Undef; // turn result into unknown, because the model is not correct
	  }
	}

        // print solution to screen
            if( opt_modelStyle ) printf(ret == l_True ? "SAT\n" : ret == l_False ? "UNSAT\n" : "UNKNOWN\n");
	    else printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s UNKNOWN\n");

        // put empty clause on proof
        if(ret == l_False && S.drupProofFile != NULL ) fprintf(S.drupProofFile, "0\n");

        // print solution into file
        if (res != NULL){
            if (ret == l_True){
		if( opt_modelStyle ) fprintf(res, "SAT\n");
                else fprintf(res, "s SATISFIABLE\nv ");
                for (int i = 0; i < S.model.size(); i++)
                  //  if (S.model[i] != l_Undef) // treat undef simply as falsified (does not matter anyways)
                        fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
                fprintf(res, " 0\n");
            }else if (ret == l_False) {
                if( opt_modelStyle ) fprintf(res, "UNSAT\n");
                else fprintf(res, "s UNSATISFIABLE\n");
	    }else
		if( opt_modelStyle ) fprintf(res, "UNKNOWN\n");
                else fprintf(res, "s UNKNOWN\n");
            fclose(res);
        }

        // print model to screen
        if(! opt_quiet && ret == l_True && res == NULL ) {
	  if( !opt_modelStyle ) printf ("v ");
          for (int i = 0; i < S.model.size(); i++)
            //  if (S.model[i] != l_Undef) // treat undef simply as falsified (does not matter anyways)
              printf( "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
	  printf(" 0\n");
	}
        
        cout.flush(); cerr.flush();
        
#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
	    // printf("c ===============================================================================\n");
	    printf("c Warning: caught an exception\n");
            if( opt_modelStyle ) printf("UNKNOWN\n"); 
	    else printf("s UNKNOWN\n");
        exit(0);
    }
}
