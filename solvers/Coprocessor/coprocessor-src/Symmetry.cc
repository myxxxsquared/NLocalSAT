/*************************************************************************************[Symmetry.cc]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Symmetry.h"

#include "mtl/Sort.h"

using namespace Coprocessor;
using namespace Minisat;


Symmetry::Symmetry( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Solver& _solver)
: Technique(_config, _ca, _controller)
, data(_data)
, solver(_solver)
, processTime(0)
, addPairs(0)
, maxEq(0)
, maxOcc(0)
, eqs(0)
, replaces(0)
, totalConflicts(0)
, notYetAnalyzed(true)
, symmAddClause(0)
{  
}

bool Symmetry::process() {
  
  if( ! performSimplification() ) return true; // do not do anything?!
  modifiedFormula = false;
  
  // do not simplify, if the formula is considered to be too large!
  if( !data.unlimited() && ( data.nVars() > config.opt_symm_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_symm_cls && data.nTotLits() > config.opt_symm_lits  ) ) return true;  
  
  MethodTimer mt( &processTime );
  printf("c found units: %d, propagated: %d\n", solver.trail.size(), solver.qhead );
  
  vec<Lit> cls; cls.growTo(3,lit_Undef);
  Symm* varSymm = new Symm [ solver.nVars() ]; // ( solver.nVars() );
  Symm* oldSymm = new Symm [ solver.nVars() ]; // ( solver.nVars() );
  for( Var v = 0 ; v < solver.nVars(); ++ v ) {
    varSymm[v].v = v; oldSymm[v].v = v; 
  }
  int* freq = new int[ solver.nVars() ];
  memset( freq,0,sizeof(int) * solver.nVars());
  
  Symm* thisIter = varSymm;
  Symm* lastIter = oldSymm;
  
  const int iteration = config.sym_opt_iter;
  
  for( int i = 0 ; i < solver.clauses.size(); ++i ) {
    //printf("c clause %d / %d\n",i,solver.clauses.size() );
      const Clause& c = ca[solver.clauses[i]];
      //printf("c clause size: %d\n",c.size() );
      for( int j = 0 ; j < c.size(); ++ j ) {
	Var v = var(c[j]);
	if( false &&  sign( c[j] ) && config.sym_opt_hpol ) varSymm[v].sub( c.size() ); // take care of signs, is enabled
	else varSymm[v].add( c.size() );
	freq[v] ++;
      }
  }
  
  if( false ) {
    for( Var v = 0 ; v < solver.nVars(); ++ v ) {
      printf("c %4d[%4d] : %3d -- %3ld %3ld %3ld %3ld %3ld %3ld %3ld \n", v+1,freq[v],varSymm[v].v+1,varSymm[v].c2,varSymm[v].c3,varSymm[v].c4,varSymm[v].c5,varSymm[v].c6,varSymm[v].c7,varSymm[v].cl);
    }
  }
  
  for( int iter = 0 ; iter < iteration; ++ iter ) {
    Symm* tmp = thisIter; thisIter = lastIter; lastIter = tmp; // swap pointers
    
    // cumulate neighbors to variables
    for( int i = 0 ; i < solver.clauses.size(); ++i ) {
      const Clause& c = ca[solver.clauses[i]];
      int factor = config.sym_opt_hsize ? c.size() : 1;
      Symm thisClause;
      for( int j = 0 ; j < c.size(); ++ j ) {
	Var v = var(c[j]);
	// printf("c process variable %d\n", v + 1 );
	thisClause = ( sign(c[j]) && config.sym_opt_hpol ? lastIter[v].inv():  lastIter[v] ) * factor + thisClause; // substract, if necessary! // be careful with order here, otherwise, variable will be overwritten!
      }
      for( int j = 0 ; j < c.size(); ++ j ) {
	Var v = var(c[j]);
	thisIter[v] = lastIter[v] + thisClause;
      }
    }
    
    if( false ) {
    printf("c iteration %d\n",iter);
    for( Var v = 0 ; v < solver.nVars(); ++ v ) {
      printf("c %4d[%4d] : %3d -- %3ld %3ld %3ld %3ld %3ld %3ld %3ld \n", v+1,freq[v],varSymm[v].v+1,varSymm[v].c2,varSymm[v].c3,varSymm[v].c4,varSymm[v].c5,varSymm[v].c6,varSymm[v].c7,varSymm[v].cl);
    }
    }
    
  }
  
  // sort var structrure, to detect symmetry candidates
  sort<Symm>( thisIter, solver.nVars() );
  
  int avgFreq = solver.nVars() == 0 ? 0 : ((solver.clauses_literals + solver.nVars() - 1) / solver.nVars());
  printf("c avg freq: %d\n", avgFreq );
  // have new variable, if dependend variables are sufficiently frequent!
  // have at most the srqt of the size of the class pairs (first-last, seconds-second last, ...)
  
  if( false ) {
    for( Var v = 0 ; v < solver.nVars(); ++ v ) {
      printf("c %d : %3d -- %3ld %3ld %3ld %3ld %3ld %3ld %3ld \n", v+1,thisIter[v].v+1,thisIter[v].c2,thisIter[v].c3,thisIter[v].c4,thisIter[v].c5,thisIter[v].c6,thisIter[v].c7,thisIter[v].cl);
    }
  }
  
  // TODO continue her!
  
  vec<ScorePair> scorePairs;
  vec<Lit> assumptions;
  
  for( int i = 0 ; i < solver.nVars(); ++ i ) {
    int j = i+1;
    if( j >= solver.nVars() ) break;
    while( j < solver.nVars() && thisIter[i] == thisIter[j]) ++j ;
    if( j > i + 1 ) {
       int thisR = j - i;
       eqs ++;
       maxEq = thisR > maxEq ? thisR : maxEq;
       
       if( config.sym_opt_print ) {
       for( int k = 0; k < thisR; ++k ) {
	 if( freq[ thisIter[i+k].v ] > 0) printf("c %4d[%4d] : %3d -- %3ld %3ld %3ld %3ld %3ld %3ld %3ld \n", thisIter[i+k].v+1,freq[thisIter[i+k].v],thisIter[i+k].v+1,thisIter[i+k].c2,thisIter[i+k].c3,thisIter[i+k].c4,thisIter[i+k].c5,thisIter[i+k].c6,thisIter[i+k].c7,thisIter[i+k].cl);
       } }
       
       
       int b = j - 1; // pointer to last element
       for( int k = 0; k < thisR; ++k ) {
	 if( freq[ thisIter[i+k].v ] <= config.sym_opt_hmin || freq[ thisIter[i+k].v ] < ( avgFreq * config.sym_opt_hratio) ) continue;
	 
	 if( config.sym_opt_hprop ) { // try to add clauses by checking propagation
	    assert( solver.decisionLevel() == 0 && "can add those clauses only at level 0" );
	    
	    solver.propagate(); // in case of delayed units, get rid of them now!
	    
	    for( int m = thisR - 1 ; m > k ; -- m ) {
	      if ( freq[ thisIter[i+m].v ] <= config.sym_opt_hmin || freq[ thisIter[i+m].v ] < ( avgFreq * config.sym_opt_hratio) ) continue; // do not consider too small literals!
	      for( int o = 0 ; o < 4; ++ o ) { // check all 4 polarity combinations?
		if( !config.sym_opt_hpropA  && ( o == 1 || o == 2 ) ) continue; // just check equivalence
		const Lit l1 = mkLit(thisIter[i+k].v, o == 0 || o == 1);
		const Lit l2 = mkLit(thisIter[i+m].v, o == 0 || o == 2);
	      
		int oldHead = solver.realHead;
		if( solver.value(l1) != l_Undef ) continue; // already top level unit?
		if( solver.value(l2) != l_Undef ) continue; // already top level unit?

		solver.newDecisionLevel();
		assert( solver.decisionLevel() == 1 && "can do this only on level 1" );
		solver.uncheckedEnqueue(l1);solver.uncheckedEnqueue(l2); // double lookahead
		bool entailed = false;
		if( CRef_Undef != solver.propagate() ) { // check if conflict, if yes, add new clause!
		  if( solver.realHead > oldHead + 1) entailed = true; // only add clause, if ont already present!
		}
		solver.cancelUntil(0);
		if( entailed ) {
		  data.lits.clear();
		  data.lits.push_back( ~l1 );
		  data.lits.push_back( ~l2 );
		  CRef cr = ca.alloc(data.lits, false); // no learnt clause!!
		  solver.clauses.push(cr);
		  solver.attachClause(cr); // no data initialization necessary!!
		  if( config.sym_debug_out > 1 ) cerr << "c add clause [" << ~l1 << ", " << ~l2 << "]" << endl;
		  symmAddClause ++;
		} else if( config.sym_opt_conflicts > 0 && totalConflicts < config.sym_opt_total_conflicts ) {
		  assert( solver.assumptions.size() == 0 && "apply symmetry breaking only if no assumptions are used" );
		  bool oldUsePP = solver.useCoprocessorPP;
		  bool oldUseIP = solver.useCoprocessorIP;
		  int oldVerb = solver.verbosity;
		  totalConflicts = solver.conflicts - totalConflicts;
		  solver.verbosity = 0;
		  solver.useCoprocessorPP = false;
		  solver.useCoprocessorIP = false;
		  solver.setConfBudget( config.sym_opt_conflicts );
		  assumptions.clear();
		  assert( var(l1) != var(l2) && "assumptions should be different!" );
		  assumptions.push( l1 );assumptions.push( l2 );
		  if( config.sym_debug_out > 1 ) cerr << "c search with assumptions [" << l1 << ", " << l2 << "] starting at level " << solver.decisionLevel() << endl;
		  lbool ret = solver.solveLimited(assumptions) ;
		  solver.assumptions.clear();
		  solver.verbosity = oldVerb;
		  solver.useCoprocessorPP = oldUsePP;
		  solver.useCoprocessorIP = oldUseIP;
		  totalConflicts = solver.conflicts - totalConflicts;
		  if( ret == l_False ) { // TODO continue this here!
		    // entailed! 
		  } else if ( ret == l_True ) {
		    // found a model for the formula - handle it! 
		  }
		  // do nothing if no result has been found!
		}
	      }
	      if( !config.sym_opt_hpropF ) break; // stop after first iteration!
	    }
	  }
	 
	 
	 while( b > i+k && ( freq[ thisIter[b].v ] <= config.sym_opt_hmin || freq[ thisIter[b].v ] < ( avgFreq * config.sym_opt_hratio) ) ) --b;
	 
	 if( b <= k + i ) break; // stop here!

	  // printf("c add %d -- %d\n",i+k,b);
	  // printf("c add pair for variables %3d and %3d\n", thisIter[i+k].v+1, thisIter[b].v+1 );	 
	 addPairs ++;
	 // score is occurrences multiplied by size of symmetry candidate
	 scorePairs.push( ScorePair(thisIter[i+k].v,thisIter[b].v, (freq[ thisIter[i+k].v ] + freq[ thisIter[b].v ]) * thisR  )  );

	 b--; // do not consider the same variable again!
       }
       
    }
    i = j-1; // move pointer forward
  }
  
  solver.conflict_budget = -1;
  
  assert( solver.decisionLevel() == 0 && "after symmetry, reach level 0 again!" );
  
  // clear all the learned clauses inside the solver!
  if( config.sym_opt_cleanLearn ) {
    for( int i = 0 ; i < solver.learnts.size(); ++ i ) {
      solver.removeClause( solver.learnts[i] ); 
    }
  }
  
  if( addPairs > 0 ) solver.rebuildOrderHeap();
  
  sort(scorePairs);
  
  if( config.sym_opt_pairs ) {
    for( int i = 0 ; i < scorePairs.size(); ++ i ) {
      printf( "c %d : %d == %d , sc= %lf \n", i, scorePairs[i].v1 + 1 , scorePairs[i].v2 + 1, scorePairs[i].score ); 
    }
  }
 
  notYetAnalyzed = false;
  
  delete [] varSymm;
  delete [] oldSymm;
  delete [] freq;
  if( config.sym_opt_exit ) {
    printStatistics(cerr);
    exit(0);
  }
  
  return modifiedFormula;
}

void Coprocessor::Symmetry::printStatistics(ostream& stream)
{
  stream << "c [STAT] SYMM " << processTime << " s, " << eqs << " symm-cands, " << maxEq << " maxSize, " << addPairs  << " addedPairs " << symmAddClause << " entailedClauses, " << totalConflicts << " totCons, " << endl;
}
