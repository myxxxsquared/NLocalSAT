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

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "utils/AutoDelete.h"
#include "core/Dimacs.h"
#include "core/Solver.h"

#include "coprocessor-src/Coprocessor.h"

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
  
  setUsageHelp("USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");
  // Extra options:
  //
  IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 1, IntRange(0, 2));
  IntOption    vv  ("MAIN", "vv",   "Verbosity every vv conflicts", 10000, IntRange(1,INT32_MAX));
  IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
  IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));

  StringOption drupFile         ("PROOF", "drup", "Write a proof trace into the given file",0);
  StringOption opt_proofFormat  ("PROOF", "proofFormat", "Do print the proof format (print o line with the given format, should be DRUP)","DRUP");
  
  
  StringOption opt_config     ("MAIN", "config", "Use a preset configuration",0);
  BoolOption   opt_checkModel ("MAIN", "checkModel", "verify model inside the solver before printing (if input is a file)", false);
  BoolOption   opt_modelStyle ("MAIN", "oldModel",   "present model on screen in old format", false);
  BoolOption   opt_quiet      ("MAIN", "quiet",      "Do not print the model", false);
  BoolOption   opt_parseOnly  ("MAIN", "parseOnly", "abort after parsing", false);
  BoolOption   opt_cmdLine    ("MAIN", "cmd", "print the relevant options", false);
  
    try {
      
	// for having a schedule
	vector<int> scheduleConflicts;
	vector<string> scheduleArguments;
	
	// check the very first option for being a schedule that starts with "//\\"
	if( argc > 2 ) {
	  cerr << "c argv[1]: " << argv[1] << endl;
	  string firstParam = string(argv[1]);
	  string nextConfig, nextConflicts, nextOptions;
	  //
	  // FORMAT FOR THE SCHEDULE, as one parameter:
	  // "SCHED: <x|configureation1 parameters> <y|configuretion2 parameters> <z|configuration3 parameters> <*|final parameters>
	  // x,y and z are the number of conflicts to run the given configuration, * executes a configuration until a solution is found (or interrupt).
	  // 
	  // Or
	  // "SCHED:DEFAULT"
	  // Use a default configuration that has been valuable before
	  //
	  if( firstParam.find("SCHED:") == 0 ) { // consider the first parameter as the schedule, handle the schedule!"
	    firstParam=firstParam.substr(6);
	    cerr << "c schedule: " << firstParam << endl;
	    
	    if( firstParam == "DEFAULT" ) { // handle the default schedule here!
	      cerr << "c setup default schedule" << endl;
	    } else {	// parse the schedule
	      while( firstParam.find("<") != string::npos ) // there is another parameter
	      {
		firstParam = firstParam.substr( firstParam.find("<") + 1 );
		cerr << "c next remainder: " << firstParam << endl;
		nextConfig = firstParam.substr( 0, firstParam.find(">") );
		cerr << "c add the conflicts|params pair: " << nextConfig << endl;
		nextConflicts = nextConfig.substr( 0, nextConfig.find("|") );
		nextOptions = nextConfig.substr(  nextConfig.find("|") + 1);
		cerr << "c pair: " << nextConflicts << " for " << nextOptions << endl;
		int nr = -1; // in case no number is given, or a star is given, run the configuration for ever!
		if( nextConflicts.size() != 0 &&  nextConflicts != "*" ) { // found final configuration that should run until a solution is found
		  nr = atoi( nextConflicts.c_str() ); // convert to number
		  assert( nr >= 0 && "do not run this configuration for ever" );
		}
		scheduleConflicts.push_back(nr);
		scheduleArguments.push_back(nextOptions);
	      }
	    }

	    cerr << "c schedule:" << endl;
	    for( int i = 0 ; i < scheduleArguments.size(); ++ i )
	    {
	      cerr << "c [" << i << "] " << scheduleConflicts[i] << " for " << scheduleArguments[i] << endl;
	    }

	    cerr << "c initial argc: " << argc << " and argv: " << endl;
	    for( int i = 0 ; i < argc; ++i ) cerr << "c [" << i << "] " << argv[i] << endl;
	    
	    // set argc and argv right ...
	    for( int i = 1 ; i + 1 < argc; ++i ) argv[i] = argv[i+1];
	    argc --;
	    
	    cerr << "c modified argc: " << argc << " and argv: " << endl;
	    for( int i = 0 ; i  < argc; ++i ) cerr << "c [" << i << "] " << argv[i] << endl;


	  }
	}
        
        // memorize pointer to argv of
        char** originalArgv = argv;
	int originalArgc = argc;
        char** scheduleArgv = 0; // array to which argv could point to
        std::vector<std::string> optionList; // global option list, so that memory fields are accessible
        MethodFree mf( (void*&)scheduleArgv ); // delete the field if its not used any more
	// run all the iterations, and one iteration if scheduleArguments.size() == 0
        for( int solverIteration = 0 ; solverIteration < scheduleArguments.size() || (solverIteration == 0 && scheduleArguments.size() == 0); ++ solverIteration ) 
	{
	  // setup the actual argv by adding the specified configuration to the current argv ...
	  if( scheduleArguments.size() > 0 ) { // modify argv and argc only if necessary!
	    // split string into sub strings, separated by ':'
	    cerr << "c handle schedule arguments: " << scheduleArguments[solverIteration] << endl;
	    
	    int lastStart = 0;
	    int findP = 0;
	    optionList.clear();
	    while ( findP < scheduleArguments[solverIteration].size() ) { // tokenize string
		findP = scheduleArguments[solverIteration].find(" ", lastStart);
		if( findP == std::string::npos ) { findP = scheduleArguments[solverIteration].size(); }
		
		if( findP - lastStart - 1 >= 0 ) {
		  optionList.push_back( scheduleArguments[solverIteration].substr(lastStart ,findP - lastStart) );
		}
		lastStart = findP + 1;
	    }
	  //  std::cerr << "c work on option string " << options << std::endl;
	    // create argc - argv combination
	    if( scheduleArgv != 0 ) free( scheduleArgv ); // free the resources again
	    scheduleArgv = (char**) malloc( sizeof(char*) * (optionList.size() +  originalArgc) ); // and all the other
	    
	    for( int i = 0; i < originalArgc; ++ i ) scheduleArgv[i] = originalArgv[i]; // copy the global parameters
	    for( int i = 0; i < optionList.size(); ++ i ) scheduleArgv[i+originalArgc] = (char*)optionList[i].c_str(); // copy the global parameters
	    
	    argc = optionList.size() + originalArgc;
	    argv = scheduleArgv;
  
	    cerr << "c SCHEDULE[" << solverIteration << "] argc: " << argc << " and argv: " << endl;
	    for( int i = 0 ; i  < argc; ++i ) cerr << "c [" << i << "] " << argv[i] << endl;
	    
// 	    exit(40);
	  }
	  
	  //
	  // here the solver starts with its actual work ...
	  //	  
	  ::parseOptions (argc, argv ); // parse all global options
	  CoreConfig coreConfig(string(opt_config == 0 ? "" : opt_config));
	  Coprocessor::CP3Config cp3config(string(opt_config == 0 ? "" : opt_config));
	  bool foundHelp = coreConfig.parseOptions(argc, argv);
	  foundHelp = cp3config.parseOptions(argc, argv) || foundHelp;
	  if( foundHelp ) exit(0); // stop after printing the help information
	  
	  if( opt_cmdLine ) { // print the command line options
	    std::stringstream s;
	    coreConfig.configCall(s);
	    cp3config.configCall(s);
	    configCall(argc, argv, s);
	    cerr << "c tool-parameters: " << s.str() << endl;
	    exit(0);
	  }
	  
	  Solver S(coreConfig);
	  S.setPreprocessor(&cp3config); // tell solver about preprocessor
	  
	  double initial_time = cpuTime();

	  S.verbosity = verb;
	  S.verbEveryConflicts = vv;

  #if defined(__linux__)
	  fpu_control_t oldcw, newcw;
	  _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
	  if( verb > 0 ) printf("c WARNING: for repeatability, setting FPU to use double precision\n");
  #endif

	  solver = &S;
	  // Use signal handlers that forcibly quit until the solver will be able to respond to
	  // interrupts:
	  signal(SIGINT, SIGINT_exit);
	  signal(SIGXCPU,SIGINT_exit);

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
	      printf("c ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
	  
	  if (S.verbosity > 0 && (scheduleArguments.size() == 0 || solverIteration == 0 ) ){ // print only once!
	      printf("c ============================[     riss %5.2f     ]=======================================================\n", solverVersion);
	      printf("c | Norbert Manthey. The use of the tool is limited to research only!                                     |\n");
	      printf("c | Based on Minisat 2.2 and Glucose 2.1  -- thanks!                                                      |\n");
	      printf("c | Contributors:                                                                                         |\n");
	      printf("c |      Kilian Gebhardt (BVE Implementation,parallel preprocessor)                                       |\n");
	      printf("c ============================[ Problem Statistics ]=======================================================\n");
	      printf("c |                                                                                                       |\n"); }

	  
	  // open file for proof
	  S.drupProofFile = (drupFile) ? fopen( (const char*) drupFile , "wb") : NULL;
	  if( opt_proofFormat && strlen(opt_proofFormat) > 0 && S.drupProofFile != NULL ) fprintf( S.drupProofFile, "o proof %s\n", (const char*)opt_proofFormat ); // we are writing proofs of the given format!

	  parse_DIMACS(in, S);
	  gzclose(in);
	  FILE* res = (argc >= 3) ? fopen(argv[2], "wb") : NULL;
	  
	  double parsed_time = cpuTime();
	  if (S.verbosity > 0 && (scheduleArguments.size() == 0 || solverIteration == 0 ) ){
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
	
	  if (!S.simplify()){
	      if (res != NULL) {
		if( opt_modelStyle ) fprintf(res, "UNSAT\n"), fclose(res);
		else fprintf(res, "s UNSATISFIABLE\n"), fclose(res);
	      }
	  // add the empty clause to the proof, close proof file
	  if (S.drupProofFile != NULL) { 
	    bool validProof = S.checkProof(); // check the proof that is generated inside the solver
	    if( verb > 0 ) cerr << "c checked proof, valid= " << validProof << endl;
	    fprintf(S.drupProofFile, "0\n"), fclose(S.drupProofFile);
	  }
	      if (S.verbosity > 0){
		  printf("c =========================================================================================================\n");
		  printf("c Solved by unit propagation\n");
		  printStats(S);
	      }
		  
		  // choose among output formats!
		  if( opt_modelStyle ) printf("UNSAT");
		  else printf("s UNSATISFIABLE\n");
	      cout.flush(); cerr.flush();
	      exit(20);
	  }
	  
	  vec<Lit> dummy;
	  // tell solver about the number of conflicts it is allowed to use (for the current iteration)
	  if( scheduleConflicts.size() > 0 && scheduleConflicts[solverIteration] >= 0 ) S.setConfBudget( scheduleConflicts[solverIteration] );
	  lbool ret = S.solveLimited(dummy);
	  S.budgetOff(); // remove budget again!
	  // have we reached UNKNOWN because of the limited number of conflicts? then continue with the next loop!
	  if( ret == l_Undef && scheduleConflicts.size() > 0 && scheduleConflicts[solverIteration] >= 0 ) 
	  {
	    if( S.verbosity > 0 ) cerr << "c schedule element [" << solverIteration << "] failed" << endl;
	    if( res != NULL) fclose(res);
	    if( S.drupProofFile != NULL ) {
	      fclose( S.drupProofFile );	// close the current file
	      S.drupProofFile = fopen((const char*) drupFile, "w");	// remove the content of that file
	      fclose( S.drupProofFile );	// close the file again
	    }
	    if (S.verbosity > 0 ) printf("c\nc ===========================[ Next Schedule Element ]=====================================================\nc\n");
	    continue; // next iteration
	  } else {
	    if( scheduleConflicts.size() > 0 && S.verbosity > 0) cerr << "c schedule element [" << solverIteration << "] succeed" << endl;
	  }
	  
	  // print stats
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
	  if(ret == l_False && S.drupProofFile != NULL ) {
	    bool validProof = S.checkProof(); // check the proof that is generated inside the solver
	    if( verb > 0 ) cerr << "c checked proof, valid= " << validProof << endl;
	    fprintf(S.drupProofFile, "0\n");
	  }
	  
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
	}
	
	
    } catch (OutOfMemoryException&){
	// printf("c ===============================================================================\n");
	printf("c Warning: caught an exception\n");
        if( opt_modelStyle ) printf("UNKNOWN\n"); 
	else printf("s UNKNOWN\n");
        exit(0);
    }
}
