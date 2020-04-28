/******************************************************************************************[sls.cc]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/sls.h"

using namespace Coprocessor;

Sls::Sls(CP3Config &_config, CoprocessorData& _data, ClauseAllocator& _ca, ThreadController& _controller)
: 
Technique(_config, _ca, _controller)
, data(_data)
, ca ( _ca )
, solveTime(0)
, flips ( 0 )
, unsats(0)
{

}

Sls::~Sls()
{

}


void Sls::createRandomAssignment()
{
	// init random assignment
	for( Var v = 0 ; v < data.nVars(); v++ )
	{
		varData[v].polarity = (rand() % 1 == 0 ? true : false );
		// (assignment, v, ( (rand() & 1) == 1 ? l_True : l_False) );
	}
}

Lit Sls::heuristic(){
  // get a random clause:
  const int& limitC = unsatClauses.size();
  const Clause& cl = ca[ unsatClauses[ rand() %  limitC ] ];
  // do walksat on that clause

  assert( cl.size() > 0 && "cannot handle empty clauses!" );

  data.lits.clear();
  data.lits.push_back( cl[0] );
  int smallestBreak = varData[ var( cl[0] ) ].breakCount;

  for( int i = 1; i < cl.size(); ++ i ) {
    int thisBreak =   varData[ var( cl[i] ) ].breakCount;
    
    if( thisBreak > smallestBreak )  continue;
    
    if ( thisBreak == smallestBreak ) {
      data.lits.push_back( cl[i] );
    } else {
      data.lits.clear();
      data.lits.push_back( cl[i] );
    }
    
  }

  if( config.opt_sls_debug ) cerr << "smallest break: " << smallestBreak << " candidates: " << data.lits.size() << endl;

  Lit tmp = lit_Undef;
  // if literal without break, select smallest such literal!
  if( smallestBreak == 0 ) {
    tmp = data.lits[ rand() % data.lits.size() ]; 
  } else {
    
    // with 20 percent, select a random variable!
    if( rand() % 10000 < config.opt_sls_rand_walk ) {
      tmp = cl[ rand() % cl.size() ]; 
    } else {
      // select one of the variables with the smallest breack count!
      tmp = data.lits[ rand() % data.lits.size() ];   
    }
  }

  assert( tmp != lit_Undef && "sls pick heuristic has to be able to select at least one literal!" );
  return tmp;
}


bool Sls::solve( const vec<CRef>& formula, uint64_t stepLimit )
{
  // do not simplify, if the formula is considered to be too large!
  if( !data.unlimited() && ( data.nVars() > config.opt_sls_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_sls_cls ) && data.nTotLits() > config.opt_sls_lits ) return false;
  
  MethodTimer mt ( &solveTime );
  
  // setup main variables
  unsatClauses.reserve(formula.size());
  
  unsatClauses.clear();
  indexes.clear();
  indexes.resize(formula.size(),-1); // index to data
  
  clsData.resize( formula.size() );
  varData.resize( data.nVars() );
  
  occ.resize( data.nVars() * 2 );
  for( int i = 0 ; i < occ.size(); ++ i ) occ[i].clear();
  
  createRandomAssignment();

  int minSize = -1;
  int maxSize = -1; // TODO: detect k -sat, adtopt flips with nr of clauses!
  int clsCount = 0;
  
  for( int i = 0 ; i < formula.size(); ++ i ) {
    const int index = i;
    const Clause& c = ca[ formula[i] ];

    if( c.can_be_deleted() || c.size() < 2) continue;
    clsCount ++;
    minSize = (minSize == -1 ? c.size() : (minSize < c.size() ? minSize : c.size() ) );
    maxSize = (maxSize == -1 ? c.size() : (maxSize > c.size() ? maxSize : c.size() ) );
    // count sat lits
    int satLits = 0;
    Lit satLit = lit_Undef;
    for( int j = 0; j < c.size(); j ++ ) {
      const Lit& l  = c[j];
      if( isSat(l) ) {
	if( satLits == 0 ) clsData[ index ].watch1 = var(l);
	else clsData[ index ].watch2 = var(l);
	satLit = l; satLits ++;
      }
      occ[ toInt(l) ] . push_back(index);
    }
    
    // handle unit/unsat case!
    if( satLits == 0 ) {
      addHeap( index ); 
      if( config.opt_sls_debug) cerr << "c added index " << index << " to unsat clauses" << endl;
    } else if( satLits == 1 ) {
      varData[ var(satLit) ].breakCount ++;
    }
    
    clsData[ index ].satLiterals = satLits;
  }

  // reduce/adopt stepLimit if formula is too large, or ksat
  if( stepLimit > 0 && config.opt_sls_adopt && clsCount > 1000000 ) {
      stepLimit = (stepLimit < 1000000 ? stepLimit : 1000000 ); // reduce to 1 million, if necessary (too many clauses)
  }
  if( minSize == maxSize && minSize > 2 && maxSize < 10 ) stepLimit = config.opt_sls_ksat_flips == -1 ? 0 : config.opt_sls_ksat_flips;
  
  
      if( config.opt_sls_debug ) {
	for( int i = 0 ; i < formula.size(); ++ i ) {
	  const Clause& c = ca[ formula[i] ];
	  if( c.can_be_deleted() || c.size() == 1 ) continue;
	  int satLits = 0;
	  for( int j = 0 ; j < c.size(); ++j ) {
	    if( isSat(c[j]) ) satLits ++;
	  }
	  assert( satLits == clsData[i].satLiterals && "number of sat lits has to be the same!" ); // although one is not yet flipped
	  cerr << "c clause[" << i << "] " << c << " has " << clsData[i].satLiterals << " satisfied literals, watches 1=" << clsData[ i ].watch1 + 1<< " 2=" << clsData[ i ].watch2 + 1<< endl;
	}
	
	for( int i = 0 ; i < unsatClauses.size(); ++ i ) {
	  const Clause& c = ca[ formula[unsatClauses[i]] ];
	  int satLits = 0;
	  for( int j = 0 ; j < c.size(); ++j ) {
	    if( isSat(c[j]) ) satLits ++;
	  }
	  cerr << "c UNSAT clause[" << unsatClauses[i] << "] " << c << " has " << clsData[ unsatClauses[i] ].satLiterals << " satisfied literals, watches 1=" << clsData[ unsatClauses[i] ].watch1 + 1<< " 2=" << clsData[ unsatClauses[i] ].watch2 + 1<< endl;
	}
	
      }
  
  // cerr << "c sls initialized " << endl;
  
  // suche
  for( flips = 0 ; (flips < stepLimit || stepLimit == 0 ) && !data.isInterupted() && unsatClauses.size() > 0 ; ++ flips )
  {
    if( config.opt_sls_debug ) {
     for( int i = 0 ; i < unsatClauses.size(); ++ i ) {
       if( clsData[ unsatClauses[i] ].satLiterals != 0 ) cerr << "c unsat clause has sat lits (according to counter) : [" << unsatClauses[i] << "]: " << ca[ formula[unsatClauses[i]] ] << endl;
     }
    }
    
    if( config.opt_sls_debug ) {
      cerr << "c sat lits: ";
      for( Var v = 0; v < data.nVars(); ++v ) if( isSat(mkLit(v,false)) ) cerr << " " << v + 1;
      cerr << endl;
      cerr << "c unsat lits: ";
      for( Var v = 0; v < data.nVars(); ++v ) if( isUnsat(mkLit(v,false)) ) cerr << " " << v + 1;
      cerr << endl;
    }
    
    // pick unsat lit per heuristic (walksat)
    const int unsatIndex = unsatClauses[ rand() % unsatClauses.size() ];
    const Clause& c = ca[ formula[ unsatIndex ] ];
    const Lit& unsatLit = c [ rand() % c.size() ];

    // update flip
    const Var v = var(unsatLit);
    
    if( config.opt_sls_debug ) cerr << "c flip literal " << ~unsatLit << " to " << unsatLit << " , taken from clause " << c << " [left:" << unsatClauses.size() << "]" << endl;
    assert( isUnsat( unsatLit ) && "this literal has to be false" );
    
    const vector<int>& plusClauses = occ[ toInt( unsatLit) ];
    const vector<int>& negClauses  = occ[ toInt(~unsatLit) ];
    
    // handle clauses that get one more satisfied literal
    for( int i = 0; i < plusClauses.size(); ++ i ) {
      const int pIndex = plusClauses[i];
      if( config.opt_sls_debug ) cerr << "c give this clause one more sat literal: [" << pIndex << "]: " << ca[ formula[pIndex] ] 
	                   << ", current satLits: " << clsData[pIndex].satLiterals 
	                   << ", watches 1=" << clsData[ pIndex ].watch1 + 1<< " 2=" << clsData[ pIndex ].watch2 + 1<< endl;
      
      if( clsData[pIndex].satLiterals == 0 ) { // cls became sat
	delHeap( pIndex );
	clsData[pIndex].watch1 = v;
	varData[v].breakCount ++;
	// TODO: all variables in this clause: dekrement make count, if make count wanted
      } else if ( clsData[pIndex].satLiterals == 1 ) {
	clsData[pIndex].watch2 = v;
	varData[ clsData[pIndex].watch1 ].breakCount --;
	assert( clsData[pIndex].watch1 != clsData[pIndex].watch2 && "the two watched literals have to be different" );
      } else  { // already 2 or more literals sat
	// nothing to be done here!
      }
      clsData[pIndex].satLiterals ++; // after case check!
      
      if( config.opt_sls_debug ) {
	const Clause& c = ca[ formula[pIndex] ];
	int satLits = 0;
	for( int j = 0 ; j < c.size(); ++j ) {
	  if( isSat(c[j]) ) satLits ++;
	}
	assert( satLits + 1== clsData[pIndex].satLiterals && "number of sat lits has to be the same!" ); // although one is not yet flipped
      }
    }
    
    // handle clauses that get one more satisfied literal
    for( int i = 0; i < negClauses.size(); ++ i ) {
      const int nIndex = negClauses[i];
      if( config.opt_sls_debug ) cerr << "c give this clause one less sat literal: [" << nIndex << "]: " << ca[ formula[nIndex] ] << ", current satLits: " << clsData[nIndex].satLiterals << endl;
      assert( clsData[nIndex].satLiterals > 0 && "was sat before" );
      
      if( clsData[nIndex].satLiterals == 1 ) { // cls became sat
	assert( clsData[nIndex].watch1 == v && "last sat variable");
	addHeap(nIndex);
	varData[v].breakCount --;
	// clsData[nIndex].watch1 = 0; // TODO: chech whether necessary
      } else if( clsData[nIndex].satLiterals == 2 ) {
	if( v == clsData[nIndex].watch1 ) clsData[nIndex].watch1 = clsData[nIndex].watch2; // set other sat lit to watcher
	varData[ clsData[nIndex].watch1 ].breakCount ++;
	assert( clsData[nIndex].watch1 != v && "variable is not satisfied any more" );
      } else { // there have to be at least 2 sat lits! -> set watcher!

	assert( clsData[nIndex].satLiterals > 2 && "here, at least 3 literals have to be satisfied");

	if( clsData[nIndex].watch1 == v || clsData[nIndex].watch2 == v ) {
	  const Clause& c = ca[ formula[ nIndex ] ];
	  int satLits = 0;
	  for( int j = 0; j < c.size(); j ++ ) {
	    const Lit& l  = c[j];
	    if( var(l) == v ) continue; // v will be flipped
	    if( isSat(l) ) {
	      if( satLits == 0 ) { clsData[ nIndex ].watch1 = var(l); satLits++; }
	      else { clsData[ nIndex ].watch2 = var(l); satLits++; break; }
	    }
	  }
	  if( config.opt_sls_debug && satLits < 2 ) {
	    cerr << "c not enough sat lits for [" << nIndex << "]: " << c << " with set watches 1=" << clsData[ nIndex ].watch1 + 1<< " 2=" << clsData[ nIndex ].watch2 + 1<< endl;
	    cerr << "c sat lits: ";
	    for( int j = 0; j < c.size(); j ++ ) {
	      const Lit& l  = c[j];
	      if( var(l) == v ) continue; // v will be flipped
	      if( isSat(l) ) {
		cerr << " " << l;
	      }
	    }
	    cerr << endl;
	  }
	  assert ( satLits > 1 && " there have to be at least to satisfied literals " );
	  assert( clsData[nIndex].watch1 != clsData[nIndex].watch2 && "the two watched literals have to be different" );
	}
      }
      clsData[nIndex].satLiterals --;
      
      if( config.opt_sls_debug ) {
	const Clause& c = ca[ formula[nIndex] ];
	int satLits = 0;
	for( int j = 0 ; j < c.size(); ++j ) {
	  if( isSat(c[j]) ) satLits ++;
	}
	assert( satLits == clsData[nIndex].satLiterals + 1 && "number of sat lits has to be the same!" ); // although one is not yet flipped
      }
    }
    
    // flip polarity of variable
    varData[v].polarity = ! varData[v].polarity;
  }
  
  unsats = unsatClauses.size();
  return unsatClauses.size() == 0;
}

#if 0
bool Sls::solve( const vec<CRef>& formula, uint32_t stepLimit )
{
        solveTime = cpuTime() - solveTime;
	// setup main variables
	assignment.resize(data.nVars());
	this->varCnt = data.nVars();
	this->formulaAdress = (vec<CRef>*)&formula;
	
	// for algorithm
	bool solution = false;
	unsigned restarts = 0;

	// init search
	init();
	
	if( config.opt_sls_debug ) cerr << "c start with " << unsatisfiedClauses << " unsatisfied clauses" << endl;
	// search
	solution = search(stepLimit);
	
	solveTime = cpuTime() - solveTime;
	
	if( config.opt_sls_debug ) {
	  if( solution) {
	    bool foundUnsatisfiedClause = false;;
	    for( int i = 0 ; i < formula.size()  ; ++ i ) {
	      bool thisClauseIsSatisfied = false;
	      const Clause& cl = ca[ formula[i] ];
	      if( cl.can_be_deleted() ) continue;
	      for( int j = 0 ; j < cl.size(); ++ j ) {
		if ( isSat( assignment, cl[j] ) ) { thisClauseIsSatisfied = true; break; }
	      }
	      if( ! thisClauseIsSatisfied ) { 
		foundUnsatisfiedClause = true;
		if( config.opt_sls_debug ) cerr << "the clause " << ca[formula[i]] << " is not satisfied by the SLS model" << endl;
		break;
	      }
	    }
	    if( !foundUnsatisfiedClause ) {
	      cerr << "SLS model was successfully checked" << endl; 
	    }
	  }
	}
	
	if( config.opt_sls_debug ) {
	  cerr << "SLS model: ";
	  for( Var v = 0 ; v < data.nVars(); ++ v ) cerr << " " << ((int)assignment[v]) * (v+1);
	  cerr << endl;
	}
	
	
	
	// return satisfying assignment or 0, if no solution has been found so far
	return solution;
}

#endif

void Sls::printStatistics( ostream& stream )
{
  stream << "c [STAT] SLS " << solveTime << " s, " << flips << " flips, " << flips / solveTime << " fps" << endl;
  stream << "c [STAT] SLS-info " <<  unsats << " unsatClauses" << endl;
}


void Sls::destroy()
{
  unsats = unsatClauses.size();
  vector<CRef>().swap( unsatClauses); // data
  vector<int>().swap( indexes ); // indexes
  vector<VarData>().swap( varData );
  vector< ClsData >().swap( clsData );
  vector< vector< int > >().swap( occ );
}

