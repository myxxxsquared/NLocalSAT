/**********************************************************************************[Coprocessor.cc]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Coprocessor.h"


#include "coprocessor-src/VarFileParser.h"
#include "coprocessor-src/Shuffler.h"
#include "mtl/Sort.h"

#include <iostream>
#include <cstring>

using namespace std;
using namespace Coprocessor;

Preprocessor::Preprocessor( Solver* _solver, CP3Config& _config, int32_t _threads)
: 
config( _config )
, threads( _threads < 0 ? config.opt_threads : _threads)
, solver( _solver )
, ca( solver->ca )
, log( config.opt_log )
, data( solver->ca, solver, log, config.opt_unlimited, config.opt_randomized, config.opt_debug )
, controller( config.opt_threads )
// attributes and all that
, thisClauses( 0 )
, thisLearnts( 0 )
, lastInpConflicts(0)
, formulaVariables(-1)
// classes for preprocessing methods
, propagation( config, solver->ca, controller )
, subsumption( config, solver->ca, controller, data, propagation )
, hte( config, solver->ca, controller, propagation )
, bve( config, solver->ca, controller, propagation, subsumption )
, bva( config, solver->ca, controller, data,propagation )
, cce( config, solver->ca, controller, propagation )
, ee ( config, solver->ca, controller, propagation, subsumption )
, unhiding ( config, solver->ca, controller, data, propagation, subsumption, ee )
, probing  ( config, solver->ca, controller, data, propagation, ee, *solver )
, rate  ( config, solver->ca, controller, data, *solver, propagation )
, res( config, solver->ca, controller, data,propagation)
, rew( config, solver->ca, controller, data, subsumption )
, fourierMotzkin( config, solver->ca, controller, data, propagation, *solver )
, dense( config, solver->ca, controller, data, propagation)
, symmetry(config, solver->ca, controller, data, *solver)
, xorReasoning(config, solver->ca, controller, data, propagation, ee )
, bce(config, solver->ca, controller, data, propagation )
, la(config, solver->ca, controller, data, propagation )
, entailedRedundant( config, solver->ca, controller, data)
, sls ( config, data, solver->ca, controller )
, twoSAT( config, solver->ca, controller, data)
, shuffleVariable (-1)
{
  controller.init();
}

Preprocessor::~Preprocessor()
{
  if (config.opt_verbose > 2) cerr << "c destruct preprocessor" << endl;
}

lbool Preprocessor::performSimplification()
{
  if( ! config.opt_enabled ) return l_Undef;
  if( config.opt_verbose > 4 ) cerr << "c start simplifying with coprocessor" << endl;

  if( formulaVariables == -1 ) {
    if( config.opt_verbose > 2 ) cerr << "c initialize CP3 with " << solver->nVars()  << " variables " << endl;
    formulaVariables = solver->nVars() ;
  }
  
  MethodClock mc ( data.isInprocessing() ? ipTime : ppTime ); // measure the time for this iteration!
  MethodClock moh( overheadTime ); // measure overhead
  if( config.printAfter != 0 ) cerr << "c printAfter " << config.printAfter << endl;
    
  // first, remove all satisfied clauses
  if( config.opt_simplify && !solver->simplify() ) { cout.flush(); cerr.flush(); return l_False; }

  lbool status = l_Undef;
  // delete clauses from solver
  
  if( config.opt_check ) cerr << "present clauses: orig: " << solver->clauses.size() << " learnts: " << solver->learnts.size() << endl;
  
  cleanSolver ();
  // initialize techniques
  data.init( solver->nVars() );
  data.resetPPhead(); // to see all unit propagations also in CP, even if they have been processed inside the solver already
  
  if( config.opt_shuffle ) shuffle();
  
  if( config.opt_check ) checkLists("before initializing");
  initializePreprocessor ();
  if( config.opt_check ) checkLists("after initializing");
  
  if( config.opt_verbose > 4 ) cerr << "c coprocessor finished initialization" << endl;
  
  const bool printBVE = false, printBVA = false, printProbe = false, printUnhide = false, 
	printCCE = false, printRATE = false, printEE = false, printREW = false, printFM = false, printHTE = false, printSusi = false, printUP = false,
	printTernResolve = false, printAddRedBin = false, printXOR = false, printENT=false, printBCE=false, printLA=false;  

  // begin clauses have to be sorted here!!
  sortClauses();
  moh.stop();
	
  for( int ppIteration = 0; ppIteration < ( data.isInprocessing() ? 1 : config.opt_simplifyRounds ); ++ ppIteration )
  {
    double iterTime = cpuTime();
    if( config.opt_verbose > 0 || config.opt_debug || true) cerr << "c pp iteration " << ppIteration << endl;
    // do preprocessing
    if( config.opt_up ) {
      if( config.opt_verbose > 0 ) cerr << "c up ..." << endl;
      if( config.opt_verbose > 4 ) cerr << "c coprocessor(" << data.ok() << ") propagate" << endl;
      if( status == l_Undef ) status = propagation.process(data, true);
      if( config.opt_verbose > 1 )  { printStatistics(cerr); propagation.printStatistics(cerr); }
    }
    
    if( config.opt_twosat_init ) {
      if( config.opt_verbose > 0 ) cerr << "c 2sat ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor 2SAT" << endl;
      if( status == l_Undef ) {
	bool solvedBy2SAT = twoSAT.solve();  // cannot change status, can generate new unit clauses
	if( solvedBy2SAT ) {
	  bool isNotSat = false;
	  for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	    const Clause& cl = ca[ data.getClauses()[i] ];
	    int j = 0;
	    for(  ; j < cl.size(); ++ j ) {
	      if( twoSAT.isSat(cl[j]) ) break;
	    }
	    if( j == cl.size() ) { isNotSat = true; break; }
	  }
	  if( isNotSat ) {
	    // only set the phase before search!
	    if( config.opt_ts_phase && !data.isInprocessing()) {
	      for( Var v = 0; v < data.nVars(); ++ v ) solver->varFlags[v].polarity = ( 1 == twoSAT.getPolarity(v) );
	    }
	  } else {
	    cerr // << endl 
	    << "c =================================" << endl 
	    << "c  use the result of 2SAT as model " << endl 
	    << "c =================================" << endl;
	    // initial twosat model should always be used as a model!
	    for( Var v = 0; v < data.nVars(); ++ v ) solver->varFlags[v].polarity = ( 1 == twoSAT.getPolarity(v) );
	  }
	} else {
	  data.setFailed();
	}
      }
      if (! solver->okay())
	  status = l_False;
    }  
   
    if( printUP || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'u')  ) {
    printFormula("after Sorting");
    }
    
    if( config.opt_debug )  { scanCheck("after SORT"); }  
    
    if( config.opt_xor ) {
      if( config.opt_verbose > 0 ) cerr << "c xor ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") XOR" << endl;
      if( status == l_Undef ) xorReasoning.process();  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); xorReasoning.printStatistics(cerr); }
      if (! data.ok() )
	  status = l_False;
    }
    data.checkGarbage(); // perform garbage collection
    
    if( config.opt_debug ) { checkLists("after XOR"); scanCheck("after XOR"); }
    if( printXOR || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'x')) {
    printFormula("after XOR");
    }
    
    if( config.opt_ent ) {
      if( config.opt_verbose > 0 ) cerr << "c ent ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") entailed redundancy" << endl;
      if( status == l_Undef ) entailedRedundant.process();  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); entailedRedundant.printStatistics(cerr); }
    }
    data.checkGarbage(); // perform garbage collection
    
    if( config.opt_debug )  { checkLists("after ENT"); scanCheck("after ENT"); }  
    if( printENT || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == '1') ) {
    printFormula("after ENT");
    }
    
    if( config.opt_ternResolve ) {
      if( config.opt_verbose > 0 ) cerr << "c res3 ..." << endl;
      res.process(false); 
      if( config.opt_verbose > 1 )  { printStatistics(cerr); res.printStatistics(cerr); }
      if( printTernResolve || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == '3') ) printFormula("after TernResolve");
    }
    
    // clear subsimp stats
    if ( true ) 
	subsumption.resetStatistics();

    if( config.opt_subsimp ) {
      if( config.opt_verbose > 0 ) cerr << "c subsimp ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") subsume/strengthen" << endl;
      if( status == l_Undef ) subsumption.process();  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); subsumption.printStatistics(cerr); }
      if (! solver->okay())
	  status = l_False;
      data.checkGarbage(); // perform garbage collection
      
      if( printSusi || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 's')) {
      printFormula("after Susi");
      }
    }
    
    if( config.opt_debug ) { checkLists("after SUSI"); scanCheck("after SUSI"); }
    
    if( config.opt_FM ) {
      if( config.opt_verbose > 0 ) cerr << "c FM ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") fourier motzkin" << endl;
      if( status == l_Undef ) fourierMotzkin.process();  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); fourierMotzkin.printStatistics(cerr); }
      if (! data.ok() )
	  status = l_False;
      data.checkGarbage(); // perform garbage collection
      
      if( config.opt_debug ) { checkLists("after FM"); scanCheck("after FM"); }
      if( printFM || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'f')) {
      printFormula("after FM");
      }
    }
    
    if( config.opt_rew ) {
      if( config.opt_verbose > 0 ) cerr << "c rew ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") rewriting" << endl;
      if( status == l_Undef ) rew.process();  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); rew.printStatistics(cerr); }
      if (! data.ok() )
	  status = l_False;
      data.checkGarbage(); // perform garbage collection
      
      if( config.opt_debug ) { checkLists("after REW"); scanCheck("after REW"); }
      if( printREW || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'r')) {
      printFormula("after REW");
      }
    }
    
    if( config.opt_ee ) { // before this technique nothing should be run that alters the structure of the formula (e.g. BVE;BVA)
      if( config.opt_verbose > 0 ) cerr << "c ee ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") equivalence elimination" << endl;
      if( status == l_Undef ) ee.process(data);  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); ee.printStatistics(cerr); }
      if (! data.ok() )
	  status = l_False;
      data.checkGarbage(); // perform garbage collection
      
      if( config.opt_debug ) { checkLists("after EE"); scanCheck("after EE"); }

      if( printEE || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'e') ) {
      printFormula("after EE");
      }
    }
    
    if ( config.opt_unhide ) {
      if( config.opt_verbose > 0 ) cerr << "c unhide ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") unhiding" << endl;
      if( status == l_Undef ) unhiding.process(); 
      if( config.opt_verbose > 1 )  { printStatistics(cerr); unhiding.printStatistics(cerr); }
      if( !data.ok() ) status = l_False;
      data.checkGarbage(); // perform garbage collection
      
      if( printUnhide || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'g') ) {
      printFormula("after Unhiding");
      }
      if( config.opt_debug ) {checkLists("after UNHIDING");  scanCheck("after UNHIDING"); }
    }
    
    if( config.opt_hte ) {
      if( config.opt_verbose > 0 ) cerr << "c hte ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") hidden tautology elimination" << endl;
      if( status == l_Undef ) hte.process(data);  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); hte.printStatistics(cerr); }
      data.checkGarbage(); // perform garbage collection

      if( config.opt_debug ) { checkLists("after HTE");  scanCheck("after HTE"); }
      if( printHTE || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'h')) {
      printFormula("after HTE");
      }
    }
    
    if ( config.opt_probe ) {
      if( config.opt_verbose > 0 ) cerr << "c probe ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") probing" << endl;
      if( status == l_Undef ) probing.process(); 
      if( !data.ok() ) status = l_False;
      if( config.opt_verbose > 1 )  { printStatistics(cerr); probing.printStatistics(cerr); }

      if( config.opt_debug ) { checkLists("after PROBE - before GC");  scanCheck("after PROBE - before GC"); }
      if( printProbe || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'p') ) {
      printFormula("after Probing");
      }
      data.checkGarbage(); // perform garbage collection
    }

    
    if ( config.opt_bve ) {
      if( config.opt_verbose > 0 ) cerr << "c bve ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") bounded variable elimination" << endl;
      if( status == l_Undef ) status = bve.runBVE(data);  // can change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); bve.printStatistics(cerr); }
      data.checkGarbage(); // perform garbage collection
      
      if( config.opt_debug ) { checkLists("after BVE");  scanCheck("after BVE"); }
      if( printBVE || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'v')) {
      printFormula("after BVE");
      }
    }
    
    if ( config.opt_bva ) {
      if( config.opt_verbose > 0 ) cerr << "c bva ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") blocked variable addition" << endl;
      if( status == l_Undef ) bva.process(); 
      if( config.opt_verbose > 1 )  { printStatistics(cerr); bva.printStatistics(cerr); }
      if( !data.ok() ) status = l_False;
      data.checkGarbage(); // perform garbage collection
      
      if( config.opt_debug ) { checkLists("after BVA");  scanCheck("after BVA"); }
      if( printBVA || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'w') ) {
      printFormula("after BVA");
      }
    }

    if( config.opt_bce ) {
      if( config.opt_verbose > 0 ) cerr << "c bce ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") blocked clause elimination" << endl;
      if( status == l_Undef ) bce.process();  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); bce.printStatistics(cerr); }
      data.checkGarbage(); // perform garbage collection
      
      if( config.opt_debug )  { checkLists("after BCE");  scanCheck("after BCE"); }  
      if( printBCE || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'b') ) {
	printFormula("after BCE");
      }
    }
    
    if( config.opt_la ) {
      if( config.opt_verbose > 0 ) cerr << "c la ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") blocked clause elimination" << endl;
      if( status == l_Undef ) la.process();  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); la.printStatistics(cerr); }
      data.checkGarbage(); // perform garbage collection
      
      if( config.opt_debug )  { checkLists("after LA");  scanCheck("after LA"); }  
      if( printBCE || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'l') ) {
      printFormula("after BCE");
      }
    }
    
    if( config.opt_cce ) {
      if( config.opt_verbose > 0 ) cerr << "c cce ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") (covered) clause elimination" << endl;
      if( status == l_Undef ) cce.process(data);  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); cce.printStatistics(cerr); }
      data.checkGarbage(); // perform garbage collection
      
      if( config.opt_debug )  { checkLists("after CCE");  scanCheck("after CCE"); }  // perform only if BCE finished the whole formula?!
      if( printCCE || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'c') ) {
      printFormula("after CCE");
      }
    }
    
    if( config.opt_rate ) {
      if( config.opt_verbose > 0 ) cerr << "c rate ..." << endl;
      if( config.opt_verbose > 4 )cerr << "c coprocessor(" << data.ok() << ") resolution asymmetric tautology elimination" << endl;
      if( status == l_Undef ) rate.process();  // cannot change status, can generate new unit clauses
      if( config.opt_verbose > 1 )  { printStatistics(cerr); rate.printStatistics(cerr); }
    
      data.checkGarbage(); // perform garbage collection
      
      if( config.opt_debug )  { checkLists("after RATE"), scanCheck("after RATE"); }  // perform only if BCE finished the whole formula?!
      if( printRATE || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 't') ) {
      printFormula("after RATE");
      }
    }

    //
    // end of simplification iteration
    //
    iterTime = cpuTime() - iterTime;
    if( config.opt_verbose > 0 || config.opt_debug || true) cerr << "c used time in interation " << ppIteration << "  : " << iterTime << " s" << endl;    
  }
  
  if( config.opt_addRedBins ) {
    if( config.opt_verbose > 0 ) cerr << "c add2 ..." << endl;
    res.process(true); 
    if( config.opt_verbose > 1 )  { printStatistics(cerr); res.printStatistics(cerr); }
    if( printAddRedBin || config.opt_debug || (config.printAfter != 0 && strlen(config.printAfter) > 0 && config.printAfter[0] == 'a') ) printFormula("after Add2");
  }
   

  if( config.opt_sls ) {
    if( config.opt_verbose > 0 ) cerr << "c sls ..." << endl;
    if( config.opt_verbose > 4 )cerr << "c coprocessor sls" << endl;
    if( status == l_Undef ) {
      bool solvedBySls = sls.solve( data.getClauses(), config.opt_sls_flips == -1 ? (uint64_t)4000000000000000 : (uint64_t)config.opt_sls_flips  );  // cannot change status, can generate new unit clauses
      cerr << "c sls returned " << solvedBySls << endl;
      if( solvedBySls ) {
	cerr << "c formula was solved with SLS!" << endl;
	cerr // << endl 
	 << "c ================================" << endl 
	 << "c  use the result of SLS as model " << endl
	 << "c ================================" << endl;
      }
      if( solvedBySls || config.opt_sls_phase ) {
	for( Var v= 0 ; v < data.nVars(); ++ v ) solver->varFlags[v].polarity = sls.getModelPolarity(v) == 1 ? 1 : 0; // minisat uses sign instead of polarity!
      }
    }
    if (! solver->okay())
        status = l_False;
  }
  
  if( config.opt_twosat ) {
    if( config.opt_verbose > 0 ) cerr << "c 2sat ..." << endl;
    if( config.opt_verbose > 4 )cerr << "c coprocessor 2SAT" << endl;
    if( status == l_Undef ) {
      bool solvedBy2SAT = twoSAT.solve();  // cannot change status, can generate new unit clauses
      if( solvedBy2SAT ) {
	// cerr << "binary clauses have been solved with 2SAT" << endl;
	// check satisfiability of whole formula!
	bool isNotSat = false;
	for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	  const Clause& cl = ca[ data.getClauses()[i] ];
	  if( cl.can_be_deleted() ) continue;
	  int j = 0;
	  for(  ; j < cl.size(); ++ j ) {
	    if( twoSAT.isSat( cl[j] ) ) break;
	  }
	  if( j == cl.size() ) { 
	    isNotSat = true; 
	    cerr << "c twosat does not satisfy: " << cl << endl;
	    break;
	  }
	}
	if( isNotSat ) {
	  // only set the phase before search!
	  if( config.opt_ts_phase && !data.isInprocessing()) {
	    for( Var v = 0; v < data.nVars(); ++ v ) solver->varFlags[v].polarity = ( -1 == twoSAT.getPolarity(v) );
	  }
	  cerr // << endl 
	  << "c ================================" << endl 
	  << "c  2SAT model is not a real model " << endl
	  << "c ================================" << endl;
	} else {
	  cerr // << endl 
	  << "c =================================" << endl 
	  << "c  use the result of 2SAT as model " << endl 
	  << "c =================================" << endl;
	}
      } else {
	cerr // << endl 
	 << "================================" << endl 
	 << " unsatisfiability shown by 2SAT " << endl
	 << "================================" << endl;
	data.setFailed();
      }
    }
    if (! solver->okay())
        status = l_False;
  }  
  
  // clear / update clauses and learnts vectores and statistical counters
  // attach all clauses to their watchers again, call the propagate method to get into a good state again
  if( config.opt_verbose > 4 ) cerr << "c coprocessor re-setup solver" << endl;
  if ( data.ok() ) {
    if( data.hasToPropagate() ) 
      //if( config.opt_up ) 
	propagation.process(data);
      //else cerr << "c should apply UP" << endl;
  }

  if( config.opt_check ) cerr << "present clauses: orig: " << solver->clauses.size() << " learnts: " << solver->learnts.size() << " solver.ok: " << data.ok() << endl;
  
  // if( config.opt_dense && !data.isInprocessing() ) {
  if( config.opt_dense ) {
    // do as very last step -- not nice, if there are units on the trail!
    dense.compress(); 
  }
  
  moh.cont();
  
  if( config.opt_check ) fullCheck("final check");

  destroyTechniques();
  
  if ( data.ok() ) reSetupSolver();
  
  if( config.opt_verbose > 5 ) printSolver(cerr, 4); // print all details of the solver
  if( config.opt_verbose > 4 ) printFormula("after full simplification");

  mc.stop();
  moh.stop();
  
  if( config.opt_printStats ) {
    
    printStatistics(cerr);
    propagation.printStatistics(cerr);
    subsumption.printStatistics(cerr);
    ee.printStatistics(cerr);
    if( config.opt_hte ) hte.printStatistics(cerr);
    if( config.opt_bve ) bve.printStatistics(cerr);
    if( config.opt_bva ) bva.printStatistics(cerr);
    if( config.opt_probe ) probing.printStatistics(cerr);
    if( config.opt_unhide ) unhiding.printStatistics(cerr);
    if( config.opt_ternResolve || config.opt_addRedBins ) res.printStatistics(cerr);
    if( config.opt_xor) xorReasoning.printStatistics(cerr);
    if( config.opt_sls ) sls.printStatistics(cerr);
    if( config.opt_twosat) twoSAT.printStatistics(cerr);
    if( config.opt_bce ) bce.printStatistics(cerr);
    if( config.opt_la ) la.printStatistics(cerr);
    if( config.opt_cce ) cce.printStatistics(cerr);
    if( config.opt_rate ) rate.printStatistics(cerr);
    if( config.opt_ent ) entailedRedundant.printStatistics(cerr);
    if( config.opt_rew ) rew.printStatistics(cerr);
    if( config.opt_FM ) fourierMotzkin.printStatistics(cerr);
    if( config.opt_dense ) dense.printStatistics(cerr);
    if( config.opt_symm ) symmetry.printStatistics(cerr);
  }
  
  // destroy preprocessor data
  if( config.opt_verbose > 4 ) cerr << "c coprocessor free data structures" << endl;
  data.destroy();

  if( !data.ok() ) status = l_False; // to fall back, if a technique forgets to do this

  cout.flush(); cerr.flush();

  return status;
}

lbool Preprocessor::performSimplificationScheduled(string techniques)
{
  if( ! config.opt_enabled ) return l_Undef;
  if( config.opt_verbose > 4 ) cerr << "c start simplifying with coprocessor" << endl;

  if( formulaVariables == -1 ) {
    if( config.opt_verbose > 2 ) cerr << "c initialize CP3 with " << solver->nVars()  << " variables " << endl;
    formulaVariables = solver->nVars() ;
  }
  
  //
  // scan for techniques
  //
  vector< string > grammar;
  grammar.push_back( string() );
  
  char c=0;
  uint32_t pos=0;
  uint32_t line = 0;
  uint32_t level=0;
  while( pos < techniques.size() ){
   c = techniques[pos++];
   if( c == '[' ) {
      level ++;
      if( level > 1 ) { 
	cerr << "c parser at " << pos-1 << " warning: too many '[' levels" << endl;
	exit(-2);
      } else {
	  if( grammar[line].size() > 0 ) {
	    grammar.push_back( string() );
	    line ++;  
	  }
      }
      continue;
   }
   if( c == ']' ) {
      if( level < 1 ) { 
	cerr << "c parser at " << pos-1 << " warning: ignore ']'" << endl;
	exit(-2);
      }
      if( level == 1 ) { 
	// star behing brackets?
	if( pos < techniques.size() && techniques[pos] == '+' && grammar[line].size() > 0 ) { grammar[line] += "+"; pos++; }
	if( grammar[line].size() > 0 ) {
	  grammar.push_back( string() );
	  line ++;  
	}
      }
      level --;
      continue;
   }
   if( c == '+' ) {
      if( level == 0 ) { 
	cerr << "c parser at " << pos-1 << " ignore '+' at level 0" << endl;
	continue;
      }
   }
   grammar[line] += c;
  }
  
  if( config.opt_verbose > 0 ) {
    cerr << "c parsed grammar:" << endl;
    for( uint32_t i = 0 ; i < grammar.size(); ++ i ) 
    {
      cerr << "c " << grammar[i] << endl;
    }
  }

  lbool status = l_Undef;
  if( grammar.size() == 0 ) {
    cerr << "c warning: set of techniques empty - abort" << endl;
    return status;
  }
  
  MethodClock mc ( data.isInprocessing() ? ipTime : ppTime ); // measure the time for this iteration!
  MethodClock moh (overheadTime); 
  
  // first, remove all satisfied clauses
  if( !solver->simplify() ) { cout.flush(); cerr.flush(); return l_False; }

  // delete clauses from solver
  
  if( config.opt_check ) cerr << "present clauses: orig: " << solver->clauses.size() << " learnts: " << solver->learnts.size() << endl;
  thisClauses = solver->clauses.size();
  thisLearnts = solver->learnts.size();
  
  cleanSolver ();
  // initialize techniques
  data.init( solver->nVars() );
  data.resetPPhead(); // to see all unit propagations also in CP, even if they have been processed inside the solver already
  
  if( config.opt_shuffle ) shuffle();
  
  if( config.opt_check ) checkLists("before initializing");
  initializePreprocessor ();
  if( config.opt_check ) checkLists("after initializing");
  
  if( config.opt_verbose > 4 ) cerr << "c coprocessor finished initialization" << endl;
  
  moh.stop();
  
  //
  //  perform scheduled preprocessing
  //
  sortClauses();
  uint32_t currentLine = 0;
  uint32_t currentPosition = 0;
  uint32_t currentSize = grammar[currentLine].size();
  bool change = false;

  while( status == l_Undef && (currentLine < grammar.size() || currentPosition < currentSize ) )
  {
    
    if( currentPosition >= currentSize ) { // start with next line, if current line has been evaluated
      if( config.opt_verbose > 1 ) cerr << "c reached end of line " << currentLine << endl;
      currentLine++;
      if( currentLine < grammar.size() ) {
	currentSize = grammar[currentLine].size();
	currentPosition=0;
	if( config.opt_verbose > 1 ) cerr << "c new data: current line: " << grammar[currentLine] << " pos: " << currentPosition << endl;
	continue;
      } else break;
    }
    
    char execute = grammar[currentLine][currentPosition];
    if( config.opt_verbose > 0 ) cerr << "c current line: " << grammar[currentLine] << " pos: " << currentPosition << " execute=" << execute << endl;
    if( execute == '+' ) { // if there is a star in a line and there has been change,
      if( change ) {
	currentPosition = 0;
      } else {
	currentPosition ++;
      }
      continue; // start current line in grammar again!
    }
    
    if( currentLine >= grammar.size() ) break; // stop if all lines of the grammar have been evaluated
    
    if( currentPosition == 0 ) { // if the line is started from scratch, reset the change flag
      change = false;
    }
    
    // in the next iteration, the position is increased
    currentPosition++;
    
    // unit propagation has letter "u"
    if( execute == 'u' && config.opt_up && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c up" << endl;
	propagation.process(data,true);
	change = propagation.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c UP changed formula: " << change << endl;
    }

    // subsumption has letter "s"
    else if( execute == 's' && config.opt_subsimp && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c subsimp" << endl;
	subsumption.process();
	change = subsumption.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c Subsumption changed formula: " << change << endl;
    }

    // addRed2 "a"
    else if( execute == 'a' && config.opt_addRedBins && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c addRed2" << endl;
	res.process(true);
	change = res.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c AddRed2 changed formula: " << change << endl;
    }
    
    // ternRes "3"
    else if( execute == '3' && config.opt_ternResolve && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c ternRes" << endl;
	res.process(false);
	change = res.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c TernRes changed formula: " << change << endl;
    }
    
    // xorReasoning "x"
    else if( execute == 'x' && config.opt_xor && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c xor" << endl;
	xorReasoning.process();
	change = xorReasoning.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c XOR changed formula: " << change << endl;
    }
    
    // probing "p"
    else if( execute == 'p' && config.opt_probe && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c probing" << endl;
	probing.process();
	change = probing.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c Probing changed formula: " << change << endl;
    }
    
    // unhide "g"
    else if( execute == 'g' && config.opt_unhide && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c unhiding" << endl;
	unhiding.process();
	change = unhiding.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c Unhiding changed formula: " << change << endl;
    }
    
    // bva "w"
    else if( execute == 'w' && config.opt_bva && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c bva" << endl;
	bva.process();
	change = bva.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c BVA changed formula: " << change << endl;
    }
    
    // bve "v"
    else if( execute == 'v' && config.opt_bve && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c bve" << endl;
	bve.process(data);
	change = bve.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c BVE changed formula: " << change << endl;
    }
    
    // ee "e"
    else if( execute == 'e' && config.opt_ee && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c ee" << endl;
	ee.process(data);
	change = ee.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c EE changed formula: " << change << endl;
    }
    
    // bce "b"
    else if( execute == 'b' && config.opt_bce && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c bce" << endl;
	bce.process();
	change = bce.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c BCE changed formula: " << change << endl;
    }

    // literaladdition "l"
    else if( execute == 'l' && config.opt_la && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c la" << endl;
	la.process();
	change = la.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c LA changed formula: " << change << endl;
    }
    
    // entailedRedundant "1"
    else if( execute == '1' && config.opt_ent && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c ent" << endl;
	entailedRedundant.process();
	change = entailedRedundant.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c ENT changed formula: " << change << endl;
    }
    
    // cce "c"
    else if( execute == 'c' && config.opt_cce && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c cce" << endl;
	cce.process(data);
	change = cce.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c CCE changed formula: " << change << endl;
    }
    
    // rate "t"
    else if( execute == 't' && config.opt_rate && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c rate" << endl;
	rate.process();
	change = rate.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c RATE changed formula: " << change << endl;
    }    
    
    // hte "h"
    else if( execute == 'h' && config.opt_hte && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c hte" << endl;
	hte.process(data);
	change = hte.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c HTE changed formula: " << change << endl;
    }
    
    // rewriting "r"
    else if( execute == 'r' && config.opt_rew && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c rew" << endl;
	rew.process();
	change = rew.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c REW changed formula: " << change << endl;
    }
    
    // fourier motzkin "f"
    else if( execute == 'f' && config.opt_FM && status == l_Undef && data.ok() ) {
	if( config.opt_verbose > 2 ) cerr << "c fm" << endl;
	fourierMotzkin.process();
	change = fourierMotzkin.appliedSomething() || change;
	if( config.opt_verbose > 1 ) cerr << "c FM changed formula: " << change << endl;
    }
    
    // none left so far
    else {
      cerr << "c warning: cannot execute technique related to  " << execute << endl;
    }
    
    // perform afte reach call
    if( config.opt_debug )  { scanCheck("after iteration"); printFormula("after iteration");}   
    data.checkGarbage(); // perform garbage collection
    if( config.opt_verbose > 3 )  printStatistics(cerr);
    if( config.opt_verbose > 4 )  {
      cerr << "c intermediate formula: " << endl;
      for( int i = 0 ; i < solver->trail.size(); ++ i ) cerr << " " <<solver->trail[i] << endl;
      for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	cerr << "(" << i << ") (" << data.getClauses()[i] << ")" ;
	if( ca[data.getClauses()[i]].mark() != 0 ) cerr << " (ign) ";
	if( ca[data.getClauses()[i]].can_be_deleted() != 0 ) cerr << " (del) ";
	cerr << " " << ca[ data.getClauses()[i] ] << endl;
      }
    }
  }

  if( config.opt_verbose > 4 )  {
      cerr << "c final formula: " << endl;
      for( int i = 0 ; i < solver->trail.size(); ++ i ) cerr << " " <<solver->trail[i] << endl;
      for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	cerr << "(" << i << ") (" << data.getClauses()[i] << ")" ;
	if( ca[data.getClauses()[i]].mark() != 0 ) cerr << " (ign) ";
	if( ca[data.getClauses()[i]].can_be_deleted() != 0 ) cerr << " (del) ";
	cerr << " " << ca[ data.getClauses()[i] ] << endl;
      }
  }
  
  
  if( false && config.opt_sls ) { // TODO: decide whether this should be possible!
    if( config.opt_verbose > 0 ) cerr << "c sls ..." << endl;
    if( config.opt_verbose > 4 )cerr << "c coprocessor sls" << endl;
    if( status == l_Undef ) {
      bool solvedBySls = sls.solve( data.getClauses(), config.opt_sls_flips == -1 ? (uint64_t)4000000000000000 : (uint64_t)config.opt_sls_flips  );  // cannot change status, can generate new unit clauses
      if( solvedBySls ) {
	cerr << "c formula was solved with SLS!" << endl;
	cerr // << endl 
	 << "c ================================" << endl 
	 << "c  use the result of SLS as model " << endl
	 << "c ================================" << endl;
      }
      if( solvedBySls || config.opt_sls_phase ) {
	for( Var v= 0 ; v < data.nVars(); ++ v ) solver->varFlags[v].polarity = sls.getModelPolarity(v) == 1 ? 1 : 0; // minisat uses sign instead of polarity!
      }
    }
    if (! solver->okay())
        status = l_False;
  }
  
  if( false && config.opt_twosat ) {// TODO: decide whether this should be possible! -> have a parameter, 2sat seems to be more useful
    if( config.opt_verbose > 0 ) cerr << "c 2sat ..." << endl;
    if( config.opt_verbose > 4 )cerr << "c coprocessor 2SAT" << endl;
    if( status == l_Undef ) {
      bool notFailed = twoSAT.solve();  // cannot change status, can generate new unit clauses
      
      if( data.hasToPropagate() ) if( propagation.process(data) == l_False ) {data.setFailed();} ;
      
      if( notFailed ) {
	// cerr << "binary clauses have been solved with 2SAT" << endl;
	// check satisfiability of whole formula!
	bool isNotSat = false;
	for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	  const Clause& cl = ca[ data.getClauses()[i] ];
	  int j = 0;
	  for(  ; j < cl.size(); ++ j ) {
	    if( twoSAT.isSat(cl[j]) ) break;
	  }
	  if( j == cl.size() ) { isNotSat = true; break; }
	}
	if( isNotSat ) {
	  // only set the phase before search!
	  if( config.opt_ts_phase && !data.isInprocessing()) {
	    for( Var v = 0; v < data.nVars(); ++ v ) solver->varFlags[v].polarity = ( 1 == twoSAT.getPolarity(v) );
	  }
	  cerr // << endl 
	  << "c ================================" << endl 
	  << "c  2SAT model is not a real model " << endl
	  << "c ================================" << endl;
	} else {
	  cerr // << endl 
	  << "c =================================" << endl 
	  << "c  use the result of 2SAT as model " << endl 
	  << "c =================================" << endl;
	  // next, search would be called, and then a model will be generated!
	  for( Var v = 0; v < data.nVars(); ++ v ) solver->varFlags[v].polarity = ( 1 == twoSAT.getPolarity(v) );
	}
      } else {
	cerr // << endl 
	 << "================================" << endl 
	 << " unsatisfiability shown by 2SAT " << endl
	 << "================================" << endl;
	data.setFailed();
      }
    }
    if (! solver->okay())
        status = l_False;
  }  
  
  // clear / update clauses and learnts vectores and statistical counters
  // attach all clauses to their watchers again, call the propagate method to get into a good state again
  if( config.opt_verbose > 4 ) cerr << "c coprocessor re-setup solver" << endl;
  if ( data.ok() ) {
    if( data.hasToPropagate() ) 
      //if( config.opt_up ) 
	propagation.process(data);
      //else cerr << "c should apply UP" << endl;
  }

  if( config.opt_check ) cerr << "present clauses: orig: " << solver->clauses.size() << " learnts: " << solver->learnts.size() << " solver.ok: " << data.ok() << endl;
  
  //if( config.opt_dense && !data.isInprocessing() ) {
  if( config.opt_dense ) {
    // do as very last step -- not nice, if there are units on the trail!
    dense.compress(); 
  }
  
  moh.cont();
  if( config.opt_check ) fullCheck("final check");

  destroyTechniques();
  
  if ( data.ok() ) reSetupSolver();
  
  if( config.opt_verbose > 5 ) printSolver(cerr, 4); // print all details of the solver
  if( config.opt_verbose > 4 ) printFormula("after full simplification");
  moh.stop();
  mc.stop();
  
  if( config.opt_printStats ) {
    
    printStatistics(cerr);
    propagation.printStatistics(cerr);
    subsumption.printStatistics(cerr);
    ee.printStatistics(cerr);
    if( config.opt_hte ) hte.printStatistics(cerr);
    if( config.opt_bve ) bve.printStatistics(cerr);
    if( config.opt_bva ) bva.printStatistics(cerr);
    if( config.opt_probe ) probing.printStatistics(cerr);
    if( config.opt_unhide ) unhiding.printStatistics(cerr);
    if( config.opt_ternResolve || config.opt_addRedBins ) res.printStatistics(cerr);
    if( config.opt_xor) xorReasoning.printStatistics(cerr);
    if( config.opt_sls ) sls.printStatistics(cerr);
    if( config.opt_twosat) twoSAT.printStatistics(cerr);
    if( config.opt_bce ) bce.printStatistics(cerr);
    if( config.opt_la ) la.printStatistics(cerr);
    if( config.opt_cce ) cce.printStatistics(cerr);
    if( config.opt_rate ) rate.printStatistics(cerr);
    if( config.opt_ent ) entailedRedundant.printStatistics(cerr);
    if( config.opt_rew ) rew.printStatistics(cerr);
    if( config.opt_FM ) fourierMotzkin.printStatistics(cerr);
    if( config.opt_dense ) dense.printStatistics(cerr);
    if( config.opt_symm ) symmetry.printStatistics(cerr);
  }
  
  // destroy preprocessor data
  if( config.opt_verbose > 4 ) cerr << "c coprocessor free data structures" << endl;
  data.destroy();

  if( !data.ok() ) status = l_False; // to fall back, if a technique forgets to do this

  cout.flush(); cerr.flush();

  return status;
}

lbool Preprocessor::preprocess()
{
  data.preprocessing();
  const bool wasDoingER = solver->getExtendedResolution();
  
  // do not preprocess, if the formula is considered to be too large!
  if( !data.unlimited() && ( data.nVars() > config.opt_cp3_vars || data.getClauses().size() + data.getLEarnts().size() > config.opt_cp3_cls || data.nTotLits() > config.opt_cp3_lits ) ) return l_Undef;
  
  if( config.opt_symm && config.opt_enabled ) { // do only if preprocessor is enabled
    symmetry.process(); 
    if( config.opt_verbose > 1 )  { printStatistics(cerr); symmetry.printStatistics(cerr); }
  }
  
  lbool ret = l_Undef;
  if( config.opt_ptechs && string(config.opt_ptechs).size() > 0 ) ret = performSimplificationScheduled( string(config.opt_ptechs) );
  else ret = performSimplification();
  
  if( config.opt_exit_pp > 0) { // exit?
    if( config.opt_exit_pp > 1) { // print?
      int cls = 0;
      for( int i = 0 ; i < data.getTrail().size(); ++ i ) cls ++;
      for( int i = 0 ; i < data.getClauses().size(); ++ i ) if( !ca[data.getClauses()[i]].can_be_deleted() ) cls ++;
      (config.opt_exit_pp == 2 ? cerr : cout ) << "p cnf " << data.nVars() << " " << cls << endl;
      for( int i = 0 ; i < data.getTrail().size(); ++ i ) {
	(config.opt_exit_pp == 2 ? cerr : cout ) << data.getTrail() << " 0" << endl;
      }
      for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	if( ca[data.getClauses()[i]].can_be_deleted() ) continue;
	for( int j = 0 ; j < ca[data.getClauses()[i]].size(); ++ j ) {
	  (config.opt_exit_pp == 2 ? cerr : cout ) << ca[data.getClauses()[i]][j] << " ";
	}
	(config.opt_exit_pp == 2 ? cerr : cout )  << "0" << endl;
      }
    }
    exit(0);
  } else {
    solver->setExtendedResolution( wasDoingER );
    return ret;
  }
}

bool Preprocessor::wantsToInprocess () 
{
  // if no inprocesing enabled, do not do it!
  if( !config.opt_inprocess ) return false;
  
  if( config.opt_verbose > 3 ) cerr << "c check " << lastInpConflicts << " and " << (int)config.opt_inprocessInt << " vs " << solver->conflicts << endl;
  if( lastInpConflicts + config.opt_inprocessInt > solver->conflicts ) {
    return false;  
  }
  return true;
}

lbool Preprocessor::inprocess()
{
  // if no inprocesing enabled, do not do it!
  if( !config.opt_inprocess ) return l_Undef;
  
  // do not preprocess, if the formula is considered to be too large!
  if( !data.unlimited() && ( (data.nVars() > config.opt_cp3_ipvars) || ((data.getClauses().size() + data.getLEarnts().size()) > config.opt_cp3_ipcls) || data.nTotLits() > config.opt_cp3_iplits ) ) return l_Undef;
  
  // TODO: do something before preprocessing? e.g. some extra things with learned / original clauses
  if (config.opt_inprocess) {
    
    /* make sure the solver is at level 0 - not guarantueed with partial restarts!*/
    solver->cancelUntil(0);
    
    if( config.opt_verbose > 3 ) cerr << "c start inprocessing after another " << solver->conflicts - lastInpConflicts << endl;
    data.inprocessing();
    const bool wasDoingER = solver->getExtendedResolution();
    
    
    if(config.opt_randInp) data.randomized();
    if(config.opt_inc_inp) giveMoreSteps();
    
    lbool ret = l_Undef;
    if( config.opt_itechs  && string(config.opt_itechs).size() > 0 ) ret = performSimplificationScheduled( string(config.opt_itechs) );
    else ret = performSimplification();
    
    lastInpConflicts = solver->conflicts;
    if( config.opt_verbose > 4 ) cerr << "c finished inprocessing " << endl;
    
    solver->setExtendedResolution( wasDoingER );
    
    return ret;
  }
  else 
    return l_Undef; 
}

void Preprocessor::giveMoreSteps()
{
  subsumption.giveMoreSteps();
  propagation.giveMoreSteps();
  hte.giveMoreSteps();
  bve.giveMoreSteps();
  bva.giveMoreSteps();
  cce.giveMoreSteps();
  rate.giveMoreSteps();
  ee.giveMoreSteps();
  unhiding.giveMoreSteps();
  probing.giveMoreSteps();
  res.giveMoreSteps();
  rew.giveMoreSteps();
  fourierMotzkin.giveMoreSteps();
}

lbool Preprocessor::preprocessScheduled()
{
  // TODO execute preprocessing techniques in specified order
  return l_Undef;
}

void Preprocessor::freezeExtern(int lit)
{
  if( lit > 0 ) data.setNotTouch(lit-1);
  else if (lit < 0 ) data.setNotTouch(-lit-1);
}

void Preprocessor::dumpFormula(std::vector< int >& outputFormula)
{
  outputFormula.clear(); // remove everything that has been there before
//  cerr << "c move " << data.getTrail() << " units, and about " << data.getClauses().size() << " clauses." << endl;
  // top level unit clauses
  for( int i = 0 ; i < data.getTrail().size(); ++ i ) {
    const Lit& l =  data.getTrail()[i];
    const int nl = sign(l) ? ( -var(l) -1 ) : (var(l) +1);
  //  cerr << "c turn lit " << l << " into " << nl << endl;
    outputFormula.push_back( nl );outputFormula.push_back( 0 );
  }
  for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
    const Clause& c = ca[data.getClauses()[i]];
    if( c.can_be_deleted() ) continue; // do only process valid clauses!
    for( int j = 0; j < c.size(); ++ j ) {
      const Lit& l =  c[j];
      const int nl = sign(l) ? ( -var(l) -1 ) : (var(l) +1);
   //   cerr << "c turn lit " << l << " into " << nl << endl;
      outputFormula.push_back( nl );
    }
    outputFormula.push_back( 0 );
  }
}

int Preprocessor::giveNewLit(const int& l) const
{
  // conversion to inner representation, check move value, return value
  const Lit lit = l > 0 ? mkLit(l-1,false) : mkLit(-l-1,true);
  const Lit nl = dense.giveNewLit(lit);
  return sign(nl) ? ( -var(nl) -1 ) : (var(nl) +1);
}

Lit Preprocessor::giveNewLit(const Lit& l) const
{
  const Lit nl = dense.giveNewLit(l);
  return nl;
}


void Preprocessor::printStatistics(ostream& stream)
{
stream << "c [STAT] CP3 "
<< ppTime.getCpuTime() << " s-ppTime, " 
<< ipTime.getCpuTime() << " s-ipTime, "
<< ppTime.getWallClockTime() << " s-ppwTime, " 
<< ipTime.getWallClockTime() << " s-ipwTime, "
<< memUsedPeak() << " MB, "
<< (data.ok() ? "ok ":"notok ")
<< overheadTime.getCpuTime() << " s-ohTime, "
<< endl;

stream << "c [STAT] CP3(2) "
<< data.getClauses().size() << " cls, " 
<< data.getLEarnts().size() << " learnts, "
<< thisClauses - data.getClauses().size() << " rem-cls, " 
<< thisLearnts - data.getLEarnts().size() << " rem-learnts, "
<< endl;
}

void Preprocessor::extendModel(vec< lbool >& model)
{
  if( config.opt_verbose > 0 ) cerr << "c extendModel with " << model.size() << " variables" << endl;

  // for the most recent changes that have not reached a dense.compress yet
  if( config.opt_dense ) {
    dense.adoptUndoStack(); // necessary here!
    // order is important! 
    dense.decompress( model ); // if model has not been compressed before, nothing has to be done!
  }
  
  if( config.opt_verbose > 0 ) cerr << "c formula variables: " << formulaVariables << " model: " << model.size() << endl;
  if( formulaVariables > model.size() ) model.growTo(formulaVariables);
  // cerr << "c run data extend model" << endl;
  data.extendModel(model);
  
  // get back the old number of variables inside the model, to be able to unshuffle!
  if (formulaVariables != - 1 && formulaVariables < model.size() ) {
    cerr << "c model size before: " << model.size() << " with formula variables: " << formulaVariables << " and shrink: " << model.size() - formulaVariables << endl;
    model.shrink( model.size() - formulaVariables );
    cerr << "c model size afterwards: " << model.size() << endl;
  }
  if( config.opt_shuffle ) unshuffle(model);
}


void Preprocessor::initializePreprocessor()
{
  thisClauses = 0;
  thisLearnts = 0;
  
  for( int p = 0; p < 2; ++ p ) {
    vec<CRef>& clss = (p == 0) ? data.getClauses() : data.getLEarnts();
    int& thisClss = (p == 0 ) ? thisClauses : thisLearnts;

    for (int i = 0; i < clss.size(); ++i)
    {
      const CRef cr = clss[i];
      Clause& c = ca[cr];
      // assert( c.mark() == 0 && "mark of a clause has to be 0 before being put into preprocessor" );
      if( ca[cr].mark() != 0  ) continue; // do not use any specially marked clauses!
      // cerr << "c process clause " << cr << endl;

      if( c.size() == 0 ) {
	data.setFailed(); 
	break;
      } else if (c.size() == 1 ) {
	if( data.enqueue(c[0]) == l_False ) break;
	c.set_delete(true);
	thisClss ++;
      } else {
	data.addClause( cr, config.opt_check );
	// TODO: decide for which techniques initClause in not necessary!
	subsumption.initClause( cr );
	propagation.initClause( cr );
	hte.initClause( cr );
	cce.initClause( cr );
	thisClss ++;
      }
    }
  }
  /*
  uint32_t clausesSize = (*solver).clauses.size();

  for (int i = 0; i < clausesSize; ++i)
  {
    const CRef cr = solver->clauses[i];
    Clause& c = ca[cr];
    // assert( c.mark() == 0 && "mark of a clause has to be 0 before being put into preprocessor" );
    if( ca[cr].mark() != 0  ) continue; // do not use any specially marked clauses!
    // cerr << "c process clause " << cr << endl;

    if( c.size() == 0 ) {
      data.setFailed(); 
      break;
    } else if (c.size() == 1 ) {
      if( data.enqueue(c[0]) == l_False ) break;
      c.set_delete(true);
      thisClauses ++;
    } else {
      data.addClause( cr, config.opt_check );
      // TODO: decide for which techniques initClause in not necessary!
      subsumption.initClause( cr );
      propagation.initClause( cr );
      hte.initClause( cr );
      cce.initClause( cr );
      thisClauses ++;
    }
  }

  clausesSize = solver->learnts.size();
  for (int i = 0; i < clausesSize; ++i)
  {
    const CRef cr = solver->learnts[i];
    Clause& c = ca[cr];
    // assert( c.mark() == 0 && "mark of a clause has to be 0 before being put into preprocessor" );
    // cerr << "c process learnt clause " << cr << endl;
    if( ca[cr].mark() != 0  ) continue; // do not use any specially marked clauses!
    if( c.size() == 0 ) {
      data.setFailed(); 
      break;
    } else if (c.size() == 1 ) {
      if( data.enqueue(c[0]) == l_False ) break;
      c.set_delete(true);
      thisLearnts++;
    } else {
      data.addClause( cr, config.opt_check );
      // TODO: decide for which techniques initClause in not necessary!
      subsumption.initClause( cr );
      propagation.initClause( cr );
      hte.initClause( cr );
      cce.initClause( cr );
      thisLearnts++;
    }
  }
  */
}

void Preprocessor::destroyTechniques()
{
    // propagation.destroy();
    subsumption.destroy();
    ee.destroy();
    if( config.opt_hte ) hte.destroy();
    if( config.opt_bve ) bve.destroy();
    if( config.opt_bva ) bva.destroy();
    if( config.opt_probe ) probing.destroy();
    if( config.opt_unhide ) unhiding.destroy();
    if( config.opt_ternResolve || config.opt_addRedBins ) res.destroy();
    if( config.opt_xor) xorReasoning.destroy();
    if( config.opt_sls ) sls.destroy();
    if( config.opt_twosat) twoSAT.destroy();
    if( config.opt_bce ) bce.destroy();
    if( config.opt_la ) la.destroy();
    if( config.opt_cce ) cce.destroy();
    if( config.opt_rate ) rate.destroy();
    if( config.opt_ent ) entailedRedundant.destroy();
  
}


void Preprocessor::cleanSolver()
{
  solver->watches.cleanAll();
  
  // clear all watches!
  for (int v = 0; v < solver->nVars(); v++)
    for (int s = 0; s < 2; s++)
      solver->watches[ mkLit(v, s) ].clear();
    
  solver->learnts_literals = 0;
  solver->clauses_literals = 0;
}

void Preprocessor::reSetupSolver()
{
  assert( solver->decisionLevel() == 0 && "can re-setup solver only if its at decision level 0!" );
    int kept_clauses = 0;

    // check whether reasons of top level literals are marked as deleted. in this case, set reason to CRef_Undef!
    if( solver->trail_lim.size() > 0 )
      for( int i = 0 ; i < solver->trail_lim[0]; ++ i )
        if( solver->reason( var(solver->trail[i]) ) != CRef_Undef )
          if( ca[ solver->reason( var(solver->trail[i]) ) ].can_be_deleted() )
            solver->vardata[ var(solver->trail[i]) ].reason = CRef_Undef;

    // give back into solver
    for (int i = 0; i < solver->clauses.size(); ++i)
    {
        const CRef cr = solver->clauses[i];
        Clause & c = ca[cr];
	assert( c.size() != 0 && "empty clauses should be recognized before re-setup" );
        if (c.can_be_deleted()) {
            delete_clause(cr);
	} else
	  {
	      assert( c.mark() == 0 && "only clauses without a mark should be passed back to the solver!" );
	      if (c.size() > 1)
	      {
		  if( ! config.opt_simplify && solver->qhead == 0 ) { // do not change the clause, if nothing has been propagated yet
		    solver->attachClause(cr);
		    solver->clauses[kept_clauses++] = cr; // add original clauss back! 
		    continue;
		  }
		
		  // do not watch literals that are false!
		  int j = 1;
		  for ( int k = 0 ; k < 2; ++ k ) { // ensure that the first two literals are undefined!
		    if( solver->value( c[k] ) == l_False ) {
		      for( ; j < c.size() ; ++j )
			if( solver->value( c[j] ) != l_False ) 
			  { const Lit tmp = c[k]; c[k] = c[j]; c[j] = tmp; break; }
		    }
		  }
		  // assert( (solver->value( c[0] ) != l_False || solver->value( c[1] ) != l_False) && "Cannot watch falsified literals" );
		  
		  // reduct of clause is empty, or unit
		  if( solver->value( c[0] ) == l_False ) { data.setFailed(); return; }
		  else if( solver->value( c[1] ) == l_False ) {
		    if( data.enqueue(c[0]) == l_False ) {
		      data.addCommentToProof("learnt unit during resetup solver");
		      data.addUnitToProof( c[0] ); // tell drup about this unit (whereever it came from)
		      if( config.opt_debug ) cerr  << "enqueing " << c[0] << " failed." << endl; return;
		    } else { 
		      if( config.opt_debug ) cerr << "enqueued " << c[0] << " successfully" << endl; 
		      c.set_delete(true);
		    }
		    if( solver->propagate() != CRef_Undef ) { data.setFailed(); return; }
		    c.set_delete(true);
		  } else {
		    solver->attachClause(cr);
		    solver->clauses[kept_clauses++] = cr; // add original clauss back! 
		  }
	      } else {
		if (solver->value(c[0]) == l_Undef)
		  if( data.enqueue(c[0]) == l_False ) { 
		    data.addCommentToProof("learnt unit during resetup solver");
		    data.addUnitToProof( c[0] ); // tell drup about this unit (whereever it came from)
		    return;
		  }
		else if (solver->value(c[0]) == l_False )
		{
		  // assert( false && "This UNSAT case should be recognized before re-setup" );
		  data.setFailed();
		}
		c.set_delete(true);
	      }
	  }
    }
    int c_old = solver->clauses.size();
    solver->clauses.shrink(solver->clauses.size()-kept_clauses);

    if( config.opt_verbose > 2 ) fprintf(stderr,"c Subs-STATs: removed clauses: %i of %i,%s" ,c_old - kept_clauses,c_old, (config.opt_verbose == 1 ? "\n" : ""));

    int learntToClause = 0;
    kept_clauses = 0;
    for (int i = 0; i < solver->learnts.size(); ++i)
    {
        const CRef cr = solver->learnts[i];
        Clause & c = ca[cr];
        assert( c.size() != 0 && "empty clauses should be recognized before re-setup" );
        if (c.can_be_deleted())
        {
            delete_clause(cr);
            continue;
        } 
	  assert( c.mark() == 0 && "only clauses without a mark should be passed back to the solver!" );
	  if (c.learnt()) {
            if (c.size() > 1)
            {
                solver->learnts[kept_clauses++] = solver->learnts[i];
            }
          } else { // move subsuming clause from learnts to clauses
	    if( config.opt_check ) cerr << "c clause " << c << " moves from learnt to original " << endl;
	    c.set_has_extra(true);
            c.calcAbstraction();
            learntToClause ++;
	    if (c.size() > 1)
            {
              solver->clauses.push(cr);
            }
 	  }
	      assert( c.mark() == 0 && "only clauses without a mark should be passed back to the solver!" );
	      if (c.size() > 1)
	      {
		  // do not watch literals that are false!
		  int j = 1;
		  for ( int k = 0 ; k < 2; ++ k ) { // ensure that the first two literals are undefined!
		    if( solver->value( c[k] ) == l_False ) {
		      for( ; j < c.size() ; ++j )
			if( solver->value( c[j] ) != l_False ) 
			  { const Lit tmp = c[k]; c[k] = c[j]; c[j] = tmp; break; }
		    }
		  }
		  // assert( (solver->value( c[0] ) != l_False || solver->value( c[1] ) != l_False) && "Cannot watch falsified literals" );
		  
		  // reduct of clause is empty, or unit
		  if( solver->value( c[0] ) == l_False ) { data.setFailed(); return; }
		  else if( solver->value( c[1] ) == l_False ) {
		    data.addCommentToProof("learnt unit during resetup solver");
		    data.addUnitToProof( c[0] ); // tell drup about this unit (whereever it came from)
		    if( data.enqueue(c[0]) == l_False ) { if( config.opt_debug ) cerr  << "enqueing " << c[0] << " failed." << endl; return; }
		    else { if( config.opt_debug ) cerr << "enqueued " << c[0] << " successfully" << endl; }
		    if( solver->propagate() != CRef_Undef ) { data.setFailed(); return; }
		    c.set_delete(true);
		  } else solver->attachClause(cr);
	      }
	      else if (solver->value(c[0]) == l_Undef) {
		if( data.enqueue(c[0]) == l_False ) { 
		  data.addCommentToProof("learnt unit during resetup solver");
		  data.addUnitToProof( c[0] ); // tell drup about this unit (whereever it came from)
		  return;
		}
	      } else if (solver->value(c[0]) == l_False )
	      {
		// assert( false && "This UNSAT case should be recognized before re-setup" );
		data.setFailed();
	      }
	  
    }
    int l_old = solver->learnts.size();
    solver->learnts.shrink(solver->learnts.size()-kept_clauses);
    if( config.opt_verbose > 3 ) fprintf(stderr, " moved %i and removed %i from %i learnts\n",learntToClause,(l_old - kept_clauses) -learntToClause, l_old);

    
    if( false) {
      cerr << "c trail after cp3: ";
      for( int i = 0 ; i< solver->trail.size(); ++i ) 
      {
	cerr << solver->trail[i] << " " ;
      }
      cerr << endl;
      
      if( false ) {
      cerr << "formula: " << endl;
      for( int i = 0 ; i < data.getClauses().size(); ++ i )
	if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getClauses()[i] ] << endl;
      for( int i = 0 ; i < data.getLEarnts().size(); ++ i )
	if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getLEarnts()[i] ] << endl;    
      }
      
      cerr << "c watch lists: " << endl;
      for (int v = 0; v < solver->nVars(); v++)
	  for (int s = 0; s < 2; s++) {
	    const Lit l = mkLit(v, s == 0 ? false : true );
	    cerr << "c watch for " << l << endl;
	    for( int i = 0; i < solver->watches[ l ].size(); ++ i ) {
	      cerr << ca[solver->watches[l][i].cref()] << endl;
	    }
	  }
    }

}

void Preprocessor::shuffle()
{
  VarShuffler vs(config);
  
  assert( solver->decisionLevel() == 0 && "shuffle only on level 0!" );
  
  // clear all assignments, to not being forced of keeping track of shuffled trail
  for( int i = 0 ; i < solver->trail.size(); ++ i ) {
    solver->varFlags[ var( solver->trail[i] ) ].assigns = l_Undef;
  }
  
  // shuffle trail, clauses and learned clauses
  shuffleVariable = data.nVars();
  vs.process( data.getClauses(), data.getLEarnts(), solver->trail, data.nVars(), ca );
  
  // set all assignments according to the trail!
  for( int i = 0 ; i < solver->trail.size(); ++ i ) {
    solver->varFlags[ var( solver->trail[i] ) ].assigns = sign(solver->trail[i]) ? l_False : l_True;
  }
}

void Preprocessor::unshuffle(vec< lbool >& model)
{
  // setup shuffler, and unshuffle model!
  VarShuffler vs(config);
  
  assert( (shuffleVariable == -1 || model.size() == shuffleVariable) && "number of variables has to match" );
  vs.unshuffle(model, model.size() );
}

void Preprocessor::sortClauses()
{
  uint32_t clausesSize = (*solver).clauses.size();
  for (int i = 0; i < clausesSize; ++i)
  {
    Clause& c = ca[solver->clauses[i]];
    if( c.can_be_deleted() ) continue;
    const uint32_t s = c.size();
    for (uint32_t j = 1; j < s; ++j)
    {
        const Lit key = c[j];
        int32_t i = j - 1;
        while ( i >= 0 && toInt(c[i]) > toInt(key) )
        {
            c[i+1] = c[i];
            i--;
        }
        c[i+1] = key;
    }
  }

  clausesSize = solver->learnts.size();
  for (int i = 0; i < clausesSize; ++i)
  {
    Clause& c = ca[solver->learnts[i]];
    if( c.can_be_deleted() ) continue;
    const uint32_t s = c.size();
    for (uint32_t j = 1; j < s; ++j)
    {
        const Lit key = c[j];
        int32_t i = j - 1;
        while ( i >= 0 && toInt(c[i]) > toInt(key) )
        {
            c[i+1] = c[i];
            i--;
        }
        c[i+1] = key;
    }
  }
}

void Preprocessor::delete_clause(const Minisat::CRef cr)
{
  Clause & c = ca[cr];
  c.mark(1);
  ca.free(cr);
}

void Preprocessor::printFormula(const string& headline)
{
   cerr << "=== Formula " << headline << ": " << endl;
   for( int i = 0 ; i < data.getSolver()->trail.size(); ++i )
       cerr << "[" << data.getSolver()->trail[i] << "]" << endl;   
   cerr << "c clauses " << endl;
   for( int i = 0 ; i < data.getClauses().size() && !data.isInterupted(); ++ i ) {
     cerr << "(" << data.getClauses()[i] << ")";
     if( ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << "(ign)";
     if( ca[  data.getClauses()[i] ].learnt() ) cerr << "(red)";
     cerr << ca[  data.getClauses()[i] ] << endl;
   }
   cerr << "c learnts" << endl;
   for( int i = 0 ; i < data.getLEarnts().size() && !data.isInterupted(); ++ i )
   {
     cerr << "(" << data.getLEarnts()[i] << ")";
     if( ca[  data.getLEarnts()[i] ].can_be_deleted() ) cerr << "(ign)";
     if( ! ca[  data.getClauses()[i] ].learnt() ) cerr << "(irred)";
     cerr << ca[  data.getLEarnts()[i] ] << endl;    
   }
   cerr << "==================== " << endl;
}

bool Preprocessor::checkLists(const string& headline)
{
  bool ret = false;
  cerr << "c check data structures: " << headline << " ... " << endl;
  int foundEmpty = 0;
  for( Var v = 0 ; v < data.nVars(); ++ v )
  {
    for( int p = 0 ; p < 2; ++ p ) {
      const Lit l = p == 0 ? mkLit(v,false) : mkLit(v,true);
      if( data.list(l).size() == 0 ) foundEmpty ++;
      for( int i = 0 ; i < data.list(l).size(); ++ i ) {
	for( int j = i+1 ; j < data.list(l).size(); ++ j ) {
	  if( data.list(l)[i] == data.list(l)[j] ) {
	    ret = true;
	    cerr << "c duplicate " << data.list(l)[j] << " for lit " << l << " at " << i << " and " << j << " out of " << data.list(l).size() << " = " << ca[data.list(l)[j]] << endl;
	  }
	}
      }
    }
  }
  cerr << "c found " << foundEmpty << " empty lists, out of " << data.nVars() * 2 << endl;
  
  if( false ) {
  for( int i = 0 ; i < data.getLEarnts().size(); ++ i ) {
    const Clause& c = ca[data.getLEarnts()[i]];
    if( c.can_be_deleted() ) continue;
    for( int j = 0 ; j < data.getClauses().size(); ++ j ) {
      if( data.getLEarnts()[i] == data.getClauses()[j] ) cerr << "c found clause " << data.getLEarnts()[i] << " in both vectors" << endl;
    }
  }
  
  for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
    const Clause& c = ca[data.getClauses()[i]];
    if( c.can_be_deleted() ) continue;
    for( int j = i+1 ; j < data.getClauses().size(); ++ j ) {
      if( data.getClauses()[i] == data.getClauses()[j] ) cerr << "c found clause " << data.getClauses()[i] << " in clause vector twice" << endl;
    }
  }
  
  for( int i = 0 ; i < data.getLEarnts().size(); ++ i ) {
    const Clause& c = ca[data.getLEarnts()[i]];
    if( c.can_be_deleted() ) continue;
    for( int j = i+1 ; j < data.getLEarnts().size(); ++ j ) {
      if( data.getLEarnts()[i] == data.getLEarnts()[j] ) cerr << "c found clause " << data.getLEarnts()[i] << " in learnts vector twice" << endl;
    }
  }
  }
  
  return ret;
}

void Preprocessor::scanCheck(const string& headline) {
   cerr << "c perform scan check " << headline << " [ok?: " << data.ok() << "]" << endl;
  // check whether clause is in solver in the right watch lists
  for( int p = 0 ; p < 2; ++ p ) {
  
    const vec<CRef>& clauses = (p==0 ? data.getClauses() : data.getLEarnts() );
    for( int i = 0 ; i<clauses.size(); ++ i ) {
      const CRef cr = clauses[i];
      const Clause& c = ca[cr];
      if( c.can_be_deleted() ) continue;
      
      for( int j = 0 ; j < c.size(); ++ j ) {
	
	// check whether this clause is in its list
	int k = 0;
	for(  ; k < data.list( c[j] ).size(); ++ k ) {
	  if( data.list( c[j] )[k] == cr ) break;
	}
	if( k == data.list( c[j] ).size() ) {
	  cerr << "c clause [" << cr << "](ign=" << c.can_be_deleted() << ") " << c << " not found in list for literal " << c[j] << endl;
	  if( config.opt_check > 1 ) assert ( false && "all clauses have to be in the list");
	}
	
	for( int k = j+1; k < c.size(); ++ k ) {
	  if( c[j] == c[k] ) {
	    cerr << "c clause ["<<clauses[i]<<"]" << c << " has duplicate literals" << endl;
	    if( config.opt_check > 1 ) assert ( false && "no duplicate literals are allowed in clauses");
	    j = c.size(); break; 
	  } else if( c[j] == ~c[k] ) {
	    cerr << "c clause [" << clauses[i]<< "]" << c << " has complementary literals" << endl;
	    if( config.opt_check > 1 ) assert ( false && "no complementary literals are allowed in clauses");
	  }
	  else { 
	    if ( toInt(c[j]) > toInt(c[k]) ) {
	      cerr << "c clause ["<<clauses[i]<<"]" << c << " is not sorted" << endl;
	      if( config.opt_check > 1 ) assert ( false && "clauses have to be sorted");
	      j = c.size(); break; 
	    }
	  }
	}
      }
      
    }
    
  }
  
  // all clauses in a list of literal l should contain that literal!
  for( Var v = 0 ; v < data.nVars(); ++v ) {
    for( int p = 0 ; p < 2; ++ p ) 
    {
      const Lit l = mkLit(v,p==0);
      vector<CRef>& list = data.list(l);
      for( int i = 0 ; i < list.size(); ++ i )
      {
	const Clause& c = ca[ list[i] ];
	bool found=false;
	for( int j = 0 ; j < c.size(); ++ j ) {
	  if( c[j] == l ) { found = true; break; }
	}
	if(!found) {
	  cerr << "c clause " << c << " is present in list for literal " << l << " but does not contain it!" << endl;
	}
      }
      
    }
  }
  
  cerr << "c finished check " << endl;
}

void Preprocessor::fullCheck(const string& headline)
{
  cerr << "c perform full solver state check " << headline << endl;
  checkLists(headline);
  
  // check whether clause is in solver in the right watch lists
  for( int p = 0 ; p < 2; ++ p ) {
  
    const vec<CRef>& clauses = (p==0 ? data.getClauses() : data.getLEarnts() );
    for( int i = 0 ; i<clauses.size(); ++ i ) {
      const CRef cr = clauses[i];
      const Clause& c = ca[cr];
      if( c.can_be_deleted() ) continue;
      
      void  *end = 0;
      if( c.size() == 1 ) cerr << "there should not be unit clauses! [" << cr << "]" << c << endl;
      else {
	for( int j = 0 ; j < 2; ++ j ) {
	  const Lit l = ~c[j];
	  vec<Solver::Watcher>&  ws  = solver->watches[l];
	  bool didFind = false;
	  for ( int j = 0 ; j < ws.size(); ++ j){
	      CRef     wcr        = ws[j].cref();
	      if( wcr  == cr ) { didFind = true; break; }
	  }
	  if( ! didFind ) cerr << "could not find clause[" << cr << "] " << c << " in watcher for lit " << l << endl;
	}
	
      }
      
    }
  }
  
  for( Var v = 0; v < data.nVars(); ++ v )
  {
    for( int p = 0 ; p < 2; ++ p ) 
    {
      const Lit l = mkLit(v, p==1);
      vec<Solver::Watcher>&  ws  = solver->watches[l];
      for ( int j = 0 ; j < ws.size(); ++ j){
	      CRef     wcr        = ws[j].cref();
	      const Clause& c = ca[wcr];
	      if( c[0] != ~l && c[1] != ~l ) cerr << "wrong literals for clause [" << wcr << "] " << c << " are watched. Found in list for " << l << endl;
	  }
    }
    if( solver->varFlags[ v ].seen != 0 ) cerr << "c seen for variable " << v << " is not 0, but " << (int) solver->varFlags[v].seen << endl;
  }
}


void Preprocessor::printSolver(ostream& s, int verbose)
{
  s << "Solver state:"  << endl
    << " ok " << solver->ok << endl
    << " decision level: " << solver->decisionLevel()  << endl;
  if( verbose == 0 ) return;
  s << " trail_lims: ";
  for( int i = 0 ; i < solver->trail_lim.size(); i ++ )
    s << " " << solver->trail_lim[i];
  s  << endl;
  s  << " trail: ";
  for( int i = 0 ; i < solver->trail.size(); ++ i ) {
    s << " " << solver->trail[i]; 
  }
  s << endl;
  
  cerr << "c seen variables:";
  for( Var v = 0 ; v < solver->nVars(); ++ v )
    if( solver->varFlags[v].seen != 0 ) cerr << " " << v+1;
  cerr << endl;
  
  cerr << "c assigned variables:";
  for( Var v = 0 ; v < solver->nVars(); ++ v )
    if( solver->varFlags[v].assigns != l_Undef ) cerr << " " << v+1;
  cerr << endl;
  
  if( verbose == 1 ) return;
  s << "formula clauses (without unit clauses):" << endl;
  for( int i = 0 ; i < solver->clauses.size(); ++ i ) {
    const Clause& c = solver->ca[ solver->clauses[i] ];
    if( c.mark() != 0 ) continue;
    s << c << endl; // print the clause, will print the tag as well
  }
  if( verbose == 2 ) return;
  s << "learnt clauses (without unit clauses):" << endl;
  for( int i = 0 ; i < solver->learnts.size(); ++ i ) {
    const Clause& c = solver->ca[ solver->learnts[i] ];
    if( c.mark() != 0 ) continue;
    s << c << endl; // print the clause, will print the tag as well
  }  
  if( verbose == 3 ) return;
  for( Var v = 0 ; v < solver->nVars(); ++ v ) {
    for( int pl = 0 ; pl < 2; ++ pl ) {
      const Lit p = mkLit(v, pl == 1 );
      vec<Minisat::Solver::Watcher>&  ws  = solver->watches[p];
      
      for (int i = 0 ; i <  ws.size();  i ++){
            CRef     cr        = ws[i].cref();
	cerr << "c watch for " << p << " clause " << ca[cr] << " with blocker " << ws[i].blocker() << endl;
      }
    }
  }
}
