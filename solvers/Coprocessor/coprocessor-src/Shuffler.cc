/*************************************************************************************[Shuffler.cc]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef SHUFFLER_HH
#define SHUFFLER_HH

#include "coprocessor-src/Shuffler.h"

using namespace Minisat;
using namespace std;
using namespace Coprocessor;


VarShuffler::VarShuffler(CP3Config &_config) 
: config(_config) 
, variables(0)
, seed(0) {}

void VarShuffler::process(vec< Minisat::CRef >& clauses, vec< Minisat::CRef >& learnts, vec< Lit >& trail, uint32_t vars, ClauseAllocator& ca)
{
  setSeed( config.opt_shuffle_seed );
  setupShuffling(vars);
  
  shuffle( clauses, ca, config.opt_shuffle_order );
  shuffle( learnts, ca, config.opt_shuffle_order );
  shuffle( trail, config.opt_shuffle_order );
  
}


void VarShuffler::setSeed( uint32_t s ) { seed = s ; randomizer.set(seed); }
    
void VarShuffler::setupShuffling(uint32_t vars) {
  // shuffle only once!
  if( variables != 0 ) return;
  variables = vars ;

  // creae shuffle array
  replacedBy.resize( vars, lit_Undef );
  for( Var v = 0 ; v < vars; ++v ) replacedBy[v] = mkLit(v,false);

  if( config.shuffle_debug_out > 2 ) {
    cerr << "c step 1" << endl;
    for( Var v = 0 ; v < vars; ++v ) { 
      cerr << "c " << v+1 << "  => " << replacedBy[v] << endl;
    }  
  }
  
  for( Var v = 0 ; v < vars; ++v ) { 
    uint32_t r = randomizer.rand() % vars;
    Lit lr = replacedBy[v];
    replacedBy[v] = replacedBy[r];
    replacedBy[r] = lr;
  }
  
  if( config.shuffle_debug_out > 2 ) {
    cerr << "c step 2" << endl;
    for( Var v = 0 ; v < vars; ++v ) { 
      cerr << "c " << v+1 << "  => " << replacedBy[v] << endl;
    }  
  }
  

  for( Var v = 0 ; v < vars; ++v ) { 
    const uint32_t r = randomizer.rand() & 1;
    if( r == 1 ) replacedBy[v] = ~replacedBy[v];
  }
  
  if( config.shuffle_debug_out > 1 ) {
    cerr << "c step 3" << endl;
    for( Var v = 0 ; v < vars; ++v ) { 
      cerr << "c " << v+1 << "  => " << replacedBy[v] << endl;
    }  
  }
  
}
    
void VarShuffler::shuffle( vec<CRef>& clauses, ClauseAllocator& ca, bool shuffleOrder ){
  // shuffle formula
  for( uint32_t i = 0 ; i < clauses.size(); ++ i ) 
  {
    Clause& c = ca[ clauses[i] ];
    for( uint32_t j = 0 ; j < c.size(); ++ j )
    {
      const Lit l = c[j];
      c[j] =  sign(l) ? ~ replacedBy[ var(l) ] : replacedBy[var(l)] ;
    }
    if( shuffleOrder ) { // shuffle the order within the clause
      for( uint32_t j = 0 ; j < c.size(); ++ j ) {
	const Lit l = c[j];
	int r = randomizer.rand() % c.size();
	c[j] = c[r];
	c[r] = l;
      }
    }
  }
  // shuffle order of clauses
  if( shuffleOrder ) {
    for( uint32_t i = 0 ; i < clauses.size(); ++ i ) {
      const CRef tmp = clauses[i];
      int tmpPos = randomizer.rand( clauses.size() );
      clauses[i] = clauses[tmpPos];
      clauses[tmpPos] = tmp;
    }
  }

  if( config.shuffle_debug_out > 2 ) {
    cerr << "c rewritten clauses: " << endl;
    for( uint32_t i = 0 ; i < clauses.size(); ++ i ) {
      Clause& c = ca[ clauses[i] ];
      cerr << c << endl;
    } 
  }
  
}

void VarShuffler::shuffle( vec<Lit>& lits, bool shuffleOrder ) {
  for( int i = 0 ; i < lits.size(); ++ i ) {
    const Lit l = lits[i];
    lits[i] =  sign(l) ? ~ replacedBy[ var(l) ] : replacedBy[var(l)] ;
  }
  if( shuffleOrder ) { // shuffle the order within the vector
      for( uint32_t j = 0 ; j < lits.size(); ++ j ) {
	const Lit l = lits[j];
	int r = randomizer.rand() % lits.size();
	lits[j] = lits[r];
	lits[r] = l;
      }
  }
  if( config.shuffle_debug_out > 2 ) {
    cerr << "c rewritten vector: " << lits << endl;
  }
}

void VarShuffler::unshuffle( vec<lbool>& model, uint32_t vars )
{
  vec<lbool> copy;
  model.copyTo(copy);

  int max = vars < model.size() ? vars : model.size();
  
  setSeed( config.opt_shuffle_seed );
  setupShuffling(vars); // be sure tio setup the full range, such that the replacement matches the one used for creating the shuffling

  if( config.shuffle_debug_out > 1 ) {
    cerr << "c before unshuffle model: "<< endl;
    for( Var v = 0 ; v < max; ++v ) cerr <<  " " << mkLit(v, model[v] == l_False );
    cerr << endl;
  }
  
  for( Var v = 0; v < max; ++v ) {
    model [v] = sign( replacedBy[v]) ? (copy[ var(replacedBy[v]) ] == l_False ? l_True : l_False) :  copy[ var(replacedBy[v]) ];
  }
  
  if( config.shuffle_debug_out > 1 ) {
    cerr << "c after unshuffle model: " << endl;
    for( Var v = 0 ; v < max; ++v ) cerr <<  " " << mkLit(v, model[v] == l_False );
    cerr << endl;
  }
}


#endif