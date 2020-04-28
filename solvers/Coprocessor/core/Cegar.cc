/****************************************************************************************[Cegar.cc]
 Copyright (c) 2012-2013, Norbert Manthey
**************************************************************************************************/

#include <math.h>

#include "mtl/Sort.h"
#include "core/Solver.h"
#include "core/Constants.h"

// to be able to use the preprocessor
#include "coprocessor-src/Coprocessor.h"
#include "coprocessor-src/CoprocessorTypes.h"

using namespace Minisat;

void Solver::initCegar(vec< Lit >& assumptions, int& currentSDassumptions, int solveCalls)
{
    if( assumptions.size() == 0 && solveCalls == 1 && (config.opt_maxSDcalls > 0 || config.opt_maxCBcalls > 0 ) )
    {
      initCegarDS(); // setup cegar data structures
      if( config.opt_maxSDcalls > 0 ) substituteDisjunctions( assumptions );
      if( config.opt_maxCBcalls > 0 ) cegarBVA( cegarClauseLits );
      currentSDassumptions = assumptions.size();
      destroyCegarDS(); // free resources
    }
}

bool Solver::cegarNextIteration(vec< Lit >& assumptions, int& currentSDassumptions, lbool& status)
{
      //if (verbosity >= 1) printf("c CEGAR handle current iteration with %s\n", status == l_True ? "true " : (status == l_Undef ? "undef": "false"));
      // check whether UNSAT answer is unsound, due to assumptions that have been added
      if( currentSDassumptions > 0 && status == l_False ) { // this UNSAT result might be due to the added assumptions
	if (verbosity >= 1) printf("c CEGAR wrong assumptions: %d\n", conflict.size());
	if( conflict.size() == 0 ) { // if the conflict does not depend on the assumptions, return false!
	  return false;
	}
	if (verbosity >= 1) printf("c == new abstraction round (SD) ===========================================================================\n");
	sdFailedCalls ++;
	if( sdFailedCalls >= config.opt_maxSDcalls ) { // do not "guess" any more, but solve the actual formula properly
	  assumptions.clear();
	  sdFailedAssumptions += currentSDassumptions;
	  currentSDassumptions = 0;
	} else { // prepare another SD call
	  giveNewSDAssumptions( assumptions, conflict ); // calculate the new set of assumptions due to current conflict
	  int oldSDassumptions = currentSDassumptions;
	  currentSDassumptions = assumptions.size();
	  sdFailedAssumptions += oldSDassumptions - currentSDassumptions;
	}
	cancelUntil( 0 ); // reset state of the solver!
	status = l_Undef;
	return true;
      }
      
      // check whether SAT answer is "sound", otherwise, add missing clauses
      if( status == l_True && cegarClauseLits.size() > 0 ) {
	cbFailedCalls ++;
	// add all cegar clauses, if limit has been reached. Otherwise add only the falsified clauses. 
	int unsatClauses = checkCEGARclauses( cegarClauseLits, cbFailedCalls >= config.opt_maxCBcalls ); // force cegarBVA to add all clauses back
	cbReintroducedClauses += unsatClauses;
	if( unsatClauses > 0 ) {
	  if (verbosity >= 1) printf("c == new abstraction round (CB) ===========================================================================\n");
	  cancelUntil( 0 ); // reset state of the solver!
	  status = l_Undef;
	  return true; // there have been clauses that are not satisfied yet
	} else cbFailedCalls --; // done here (all cegar clauses are also satisfied!
      }
      return false;
}


/// setup data structures for cegar
void Solver::initCegarDS()
{
  
  // get space for extra data structures
  cegarOcc.growTo( nVars() * 2, 0 );
  cegarOccs.resize( nVars() * 2 );
  
  // setup structures for the formula
  for( int i = 0 ; i < clauses.size(); ++ i ) {
    const Clause& c = ca [ clauses[i] ];
    for( int j = 0 ; j < c.size(); ++ j ) {
      cegarOcc[ toInt(c[j]) ] ++;
      cegarOccs[ toInt( c[j] ) ].push_back( clauses[i] );
    }
  }
  
  // occurrences of literals in clauses, and related counters
  if( cegarLiteralHeap != 0 ) delete cegarLiteralHeap;
  cegarLiteralHeap = new Heap<occHeapLt>( cegarOcc );  // heap that has literals ordered according to their number of occurrence
}
  
/// free space of cegar data structures
void Solver::destroyCegarDS()
{
  if( cegarLiteralHeap != 0 ) delete cegarLiteralHeap;
  cegarLiteralHeap = 0;
  cegarOcc.clear(true); // free memory
  vector< vector<CRef> >().swap( cegarOccs );
}


void Solver::cegarBVA(vec< Lit >& cegarClauseLits)
{
  cerr << "c start cegarBVA" << endl;
  assert( decisionLevel() == 0 && "should only be done on level 0" );
  const bool methodDebug = false;
  
  MethodClock methodTime( cbTime );

  // fill local data structures
  MarkArray markArray;
  markArray.resize( nVars() * 2 );
  vector<CegarBVAlitMatch> stack;
  vec<Lit> tmpLiterals;
  
  // init variables
  for( Var v = 0 ; v < nVars(); ++ v ) // only add literals that could lead to reduction
  {
    if( cegarOcc[ toInt( mkLit(v,false)) ] > 3 ) if( !cegarLiteralHeap->inHeap(toInt(mkLit(v,false))) ) cegarLiteralHeap->insert( toInt( mkLit(v,false) ));
    if( cegarOcc[ toInt( mkLit(v,true) ) ] > 3 ) if( !cegarLiteralHeap->inHeap(toInt(mkLit(v,true))) )  cegarLiteralHeap->insert( toInt( mkLit(v,true)  ));
  }
  
  // test all the literals, starting with the most frequent one (to heuristically achieve largest reduction first)
  while (cegarLiteralHeap->size() > 0 && cbSteps < config.opt_cbLimit && !asynch_interrupt ) // as long as there is something to do
  {
    const Lit right = toLit( (*cegarLiteralHeap)[0] );
    cegarLiteralHeap->removeMin();
    
    // work with "right" as first literal for BVA
    if( value( right ) != l_Undef ) continue;
    if( cegarOcc[ toInt(right)] < 3 ) continue; // there won't be a reduction!

    stack.clear(); // new for each literal!

    vector<CRef>& list = cegarOccs[ toInt(right) ];
    
    // try to find for each clause C a matching clause D!
    for( uint32_t i = 0 ; i <  list.size() && (  cbSteps < config.opt_cbLimit && !asynch_interrupt ) ; ++i )
    {
      const CRef C =  list[i]; // current clause that contains literal "right"
      if( C == CRef_Undef ) continue;
      Clause& clauseC = ca[ C ];
      cbSteps ++;
      if( clauseC.mark() != 0 || clauseC.size() < 3 ) continue; // satisfied or unit -> reject! furthermore, cegar bva works only with clauses of size 3 or larger
      markArray.nextStep();
      
      Lit l1 = lit_Undef;
      uint32_t min = 0;
      bool rightInFlag=false;
      // find minimum occurring literal in the clause clauseC
      for( uint32_t j = 0 ; j < clauseC.size(); ++ j ) {
	const Lit& lt = clauseC[j];
	markArray.setCurrentStep(toInt(lt));
	if( lt == right ) { markArray.reset(toInt(lt)); rightInFlag=true; continue; }
	if ( l1 == lit_Undef ) {
	  l1 = lt; min = cegarOcc[ toInt( lt) ];
	} else {
	  if( config.opt_cbLeast ) { 
	    if( min > cegarOcc[ toInt( lt) ] ) { // use least frequent, or most frequent literal
	      min = cegarOcc[ toInt( lt) ];
	      l1 = lt;
	    } else if( min < cegarOcc[ toInt( lt) ] ) {
	      min = cegarOcc[ toInt( lt) ];
	      l1 = lt;
	    }
	  }
	}
      }
      if( l1 == lit_Undef || cegarOcc[ toInt(l1) ] < 2 ) continue; // no join partner?
      
      if( methodDebug ) cerr << "c l1 lit: " << l1 << endl;

      // find a matching partner among the clauses D in Fl1
      for( uint32_t j = 0 ; j < cegarOccs[ toInt(l1) ].size(); ++j )
      {
	const CRef D = cegarOccs[ toInt(l1) ][j];
	cbSteps ++;
	if( D == C ) continue;
	const Clause& clauseD = ca[D];
	if( clauseD.mark() != 0 || (clauseC.size() != clauseD.size() && clauseC.size() != clauseD.size() + 1) ) continue;
	// for l2 in D
	Lit match = lit_Undef;
	// check whether the current clause matches! 
	for( uint32_t k =0; k < clauseD.size(); ++k ) {
	  const Lit l2 = clauseD[k];
	  if( l2 == right ) goto nextD; // skip this clause, if the literal right also occurs in it!
	  if( !markArray.isCurrentStep( toInt(l2) ) ) {
	    if( match == lit_Undef ) match = l2; // found matching literal?
	    else goto nextD; // this clause does not match!
	  }
	}
	
	if( methodDebug ) cerr << "c found match: " << match << " for clause " << clauseC << " and " << clauseD << endl;
	
	if( match == lit_Undef ) continue; // no literal to match, coult be a duplicate, or a subsuming clause
	assert ( match != right && "matching literal is the right literal");

	// count found match, store the matching literal!
	stack.push_back( CegarBVAlitMatch( match, C, D ) );
	nextD:;
      }

    }
    // evaluate the stack, and select the most frequent literal
    sort( stack );
    if( stack.size() < 3 ) continue; // at least one literal needs to occur three times

    int occ = 0, start = 0, bestOcc = 0, bestStart = 0; Lit bestLit = lit_Undef;
    for( int i = 0 ; i < stack.size(); ++ i ) 
    {
      if( methodDebug ) cerr << "c " << stack[i].match << " vs " << stack[start].match << endl;
      if( stack[i].match == stack[start].match ) {
	occ ++;
      } else {
	if( bestLit == lit_Undef || occ > bestOcc ){ // keep first found, if same nr. of occ!
	  bestLit = stack[start].match;
	  bestOcc = occ; bestStart = start;
	  if( methodDebug ) cerr << "c store best lit " << bestLit << " with bestOcc=" << occ << endl;
	}
	start = i; occ = 1; // saw already 1 literal
      }
    }
    // perform check for last literal as well!
    if( bestLit == lit_Undef || occ > bestOcc ){ // keep first found, if same nr. of occ!
	bestLit = stack[start].match;
	bestOcc = occ; bestStart = start;
	if( methodDebug ) cerr << "c store best lit " << bestLit << " with bestOcc=" << occ << endl;
    }
    assert( bestLit != lit_Undef && "there must be some most occurring literal in the stack" );
    
    if( bestOcc < 3 ) continue ; // only perform, if there will be a reduction
    const int reduction = 2 * bestOcc - 2 - bestOcc;
    assert( reduction > 0 && "there has to be reduction!" );
    // copy right pairs forward!
    int cegarClauses = 0;
    if( methodDebug ) cerr << "c lit " << right << " -- " << bestLit << endl;
    for( int i = 0 ; i < bestOcc; ++ i ) {
      stack[i] = stack[ bestStart+i ];
      if( ca[ stack[i].refC ].size() > ca[ stack[i].refD ].size() ) cegarClauses ++;
      if( methodDebug ) cerr << "pair [" << i << "] " << ca[ stack[i].refC ] << " -- " << ca[ stack[i].refD ] << endl;
    }
    
    if( config.opt_cbStrict  && cegarClauses > reduction ) continue;
    if( !config.opt_cbStrict && reduction > 0 ) continue;
    cbClauses += cegarClauses;
    cbReduction += reduction;
    if( methodDebug ) cerr << "c found reduction " << reduction << " for lit pair " << right << " and " << bestLit << " with cegarClauses " << cegarClauses << endl;
    
    // rewrite the found clause paits, collect the cegar clauses!
    // get next variable
    const Var newVariable = newVar();
    const Lit posLit = mkLit( newVariable, false );
    cbLits ++;
    if( methodDebug ) cerr << "c added variable " << newVariable << endl;
    cegarOccs.push_back( vector<CRef>() ); cegarOccs.push_back( vector<CRef>() );
    cegarOcc.push(0);cegarOcc.push(0);
    cegarLiteralHeap->addNewElement(nVars() * 2);
    markArray.resize( nVars() * 2 );
    
    // go over all the clause pairs
    for( int i = 0 ; i < bestOcc; ++ i ) {
      detachClause( stack[i].refC, true );
      Clause& C = ca[ stack[i].refC ];
      const Clause& D = ca[ stack[i].refD ];
      // rewrite clause C (replace literal "right" with literal "newVariable"
      for( int j = 0 ; j < C.size(); ++j ) {
	if( C[j] == right ) {
	  C[j] = posLit; break;
	}
      }
      // remove the clause from the list of literal "right"
      for( int j = 0 ; j < cegarOccs[ toInt(right) ].size(); ++ j ) {
	if( cegarOccs[ toInt(right) ][j] == stack[i].refC ) {
	  cegarOccs[ toInt(right) ][j] = cegarOccs[ toInt(right) ][ cegarOccs[ toInt(right) ].size() - 1 ];
	  cegarOccs[ toInt(right) ].pop_back();
	  break;
	}
      }
      // add clauses to solver and cegar structures
      attachClause( stack[i].refC);
      cegarOccs[ toInt(  posLit ) ].push_back( stack[i].refC );
      // memorize the cegar clauses
      if( C.size() > D.size() ) {
	cerr << "c cegar clause " << D << endl;
	for( int j = 0 ; j < D.size(); ++j ) cegarClauseLits.push( D[j] );
	cegarClauseLits.push( lit_Undef ); // mark end of clause!
      }
      // remove the clause D from all structures
      for( int j = 0 ; j < D.size(); ++ j ) {
	cegarOcc[ toInt( D[j] ) ] --;
	if( cegarLiteralHeap->inHeap( toInt( D[j] ) ) ) cegarLiteralHeap->update( toInt( D[j] ) );
	// remove the clause from the list of literal "D[j]"
	for( int k = 0 ; k < cegarOccs[ toInt(D[j]) ].size(); ++ k ) {
	  if( cegarOccs[ toInt(D[j]) ][k] == stack[i].refD ) {
	    cegarOccs[ toInt(D[j]) ][k] = cegarOccs[ toInt(D[j]) ][ cegarOccs[ toInt(D[j]) ].size() - 1 ];
	    cegarOccs[ toInt(D[j]) ].pop_back();
	    break;
	  }
	}
      }
      removeClause( stack[i].refD ); // remove clause from the solver
    }
    // add the remaining two clauses for BVA
for( int i = 0 ; i < 2; ++ i ) { // add the two new clauses
      tmpLiterals.clear();
      tmpLiterals.push( ~posLit );tmpLiterals.push( i == 0 ? right : bestLit ); // add the new variable
      if( methodDebug ) cerr << "c add the bva clause " << tmpLiterals << endl;
      const CRef ref = ca.alloc(tmpLiterals, false); // no learnt clause!
      // add clause to formula, and solver structures
      attachClause( ref );
      clauses.push( ref );
      for( int i = 0 ; i < ca[ ref ].size() ; ++ i ) {
	const Lit tl = ca[ ref ][i];
	cegarOccs[ toInt(tl) ] . push_back ( ref );
	if( cegarLiteralHeap->inHeap( toInt( tl ) ) ) cegarLiteralHeap->update( toInt(tl) );
	else cegarLiteralHeap->insert( toInt(tl) );
      }
    }
    
    // update occurrences and heap!
    cegarOcc[ toInt( right ) ] -= bestOcc - 1;
    if( cegarLiteralHeap->inHeap( toInt( right ) ) ) cegarLiteralHeap->update( toInt( right ) ); 
    else if( cegarOcc[ toInt(right) ] > 2 ) cegarLiteralHeap->insert( toInt( right ) );
    cegarOcc[ toInt( posLit ) ] += bestOcc;
    if( cegarOcc[ toInt(posLit) ] > 2 ) cegarLiteralHeap->insert( toInt( posLit ) );

  }
  
  // clear used data structures
  // free( lCount );
}


int Solver::checkCEGARclauses(vec< Lit >& cegarClauses, bool addAll)
{
  const bool methodDebug = true;
  if( methodDebug ) {
    cerr << "c this model:";
    for( Var v = 0; v < nVars(); ++ v ) {
      cerr << " " << (value(v) == l_True ? v+1 : -v-1);
    }
    cerr << endl;
  }
  int unsatClauses = 0;
  vec<Lit> tmpLit; // TODO should be possible to use a global vector here!
  if (verbosity >= 1) printf("c add all CEGAR clauses %d\n", addAll ? 1 : 0);
  if( addAll ) { // add all clauses to the formula, independent of their state (SAT/UNSAT)
    for( int i = 0; i < cegarClauses.size(); ++ i ) {
      if( cegarClauses[i] == lit_Undef ) {
	// check whether the current clause is satisfied:
	bool isSat = false;
	for( int j = 0 ; j < tmpLit.size(); ++ j ) {
	  if( value( tmpLit[j] ) == l_True ) { isSat = true; break; }
	}
	unsatClauses = (isSat ? unsatClauses : unsatClauses + 1 );
	// add clause
	// if (verbosity >= 1) cerr << "c re-add CEGAR clause " << tmpLit << endl;
	CRef ref = ca.alloc(tmpLit, false); // no learnt clause!
	assert( tmpLit.size() > 1 && "there should not be unit clauses" );
	// add clause to formula, and solver structures
	attachClause( ref );
	clauses.push( ref );
	tmpLit.clear();
      } else {
	tmpLit.push( cegarClauses[i] );
      }
    }
    cegarClauses.clear();
  } else {
    int keptLits = 0;
    for( int i = 0; i < cegarClauses.size(); ++ i ) {
      if( cegarClauses[i] == lit_Undef ) {
	// check whether the current clause is satisfied:
	bool isSat = false;
	for( int j = 0 ; j < tmpLit.size(); ++ j ) {
	  if( value( tmpLit[j] ) == l_True ) { isSat = true; break; }
	}
	if( methodDebug ) {
	  if( isSat) cerr << "c keep clause ";
	  else cerr << "c re-add clause ";
	  cerr << tmpLit << endl;
	}
	if( isSat ) {
	  for( int j = 0 ; j < tmpLit.size(); ++ j ) cegarClauses[ keptLits ++ ] = tmpLit[j];
	  cegarClauses[ keptLits ++ ] = lit_Undef;
	} else {
	  unsatClauses++;
	  // add clause to the solver
	  CRef ref = ca.alloc(tmpLit, false); // no learnt clause!
	  assert( tmpLit.size() > 1 && "there should not be unit clauses" );
	  // add clause to formula, and solver structures
	  attachClause( ref );
	  clauses.push( ref );
	  tmpLit.clear();
	}
      } else {
	tmpLit.push( cegarClauses[i] );
      }
    }
    cegarClauses.shrink( cegarClauses.size() - keptLits ); // remove the literals that are not needed any more
  }
  return unsatClauses; // notify caller about number of returned clauses
}

