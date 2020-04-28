/*************************************************************************************[Entailed.cc]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Entailed.h"


using namespace Coprocessor;

EntailedRedundant::EntailedRedundant( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data )
: Technique(_config, _ca,_controller)
,data(_data)
,processTime(0)
,subsumed(0)
,removedClauses(0)
,extraSubs(0)
{
  
}

void EntailedRedundant::reset()
{
  
}
  
bool EntailedRedundant::process()
{
  if( config.entailed_debug > 0 ) cerr << "c run ENT process" << endl;
  MethodTimer mt(&processTime);
  
  if( ! performSimplification() ) return false; // do not do anything?!
  modifiedFormula = false;
  
  // do not simplify, if the formula is considered to be too large!
  if( !data.unlimited() && ( data.nVars() > config.opt_ent_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_ent_cls && data.nTotLits() > config.opt_ent_lits ) ) return false;
  
  data.ma.resize( 2*data.nVars() );
  data.lits.clear();
  data.clss.clear();
  
  for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
    const CRef cr = data.getClauses()[i];
    Clause& c = ca[ cr ];
    if( c.can_be_deleted() || c.size() < config.opt_entailed_minClsSize ) continue; // clause does not fulfill criteria

    // select the smallest literal
    data.ma.nextStep();
    Lit min = c[0];
    data.ma.setCurrentStep( toInt(c[0] ) );
    for( int i = 1; i < c.size(); ++ i ) {
      min = data[min] <= data[c[i]] ? min : c[i];
      data.ma.setCurrentStep( toInt(c[i] ) );
    }
    
    if( config.entailed_debug > 1  ) cerr << "c work on clause " << c << " with min literal " << min << " toRemoveSoFar: " << data.clss.size() << endl;
    
    // all clauses that contain this literal are candidate - all literals except one have to be part of the clause!
    vector<CRef>& clss = data.list(min);
    for( int i = 0 ; i < clss.size(); ++i ) {
      if( cr == clss[i] ) continue;
      Clause& candidate = ca[clss[i]];
      if( candidate.can_be_deleted() || candidate.learnt() ) continue; // do work on the formula only!
      if( candidate.size() > c.size() + 1 ) continue; // this clause is too large! resolution can remove only a single literal!
      Lit resolveLit = lit_Undef;
      int m = 0; // for original clause
      int n = 0; // for candidate
      data.lits.clear();
      while( n < candidate.size() && m < c.size() ) {
	if( candidate[n] == c[m] ) { // match
	  if( config.entailed_debug > 4 ) cerr << "c " << candidate[n] << " == " << c[m] << endl;
	  n++; m++;
	} else if( c[m] < candidate[n] ) { // there is a literal inside original, which is not inside candidate - this literal is part of the data.lits literals
	  if( config.entailed_debug > 4 ) cerr << "c " << candidate[n] << " > " << c[m] << " -> new missing: " << data.lits << endl;
	  data.lits.push_back( c[m] );
	  m ++;
	} else if( candidate[n] < c[m] ) { // there is a literal inside candidate, which is not inside original
	  if( resolveLit == lit_Undef ) resolveLit = candidate[n];
	  else if( resolveLit != lit_Undef ) { 
	    resolveLit = lit_Error; 
	    if( config.entailed_debug > 4 ) cerr << "c " << candidate[n] << " < " << c[m] << " -> resolveLit: " << resolveLit << " => no candidate!" << endl;
	    goto checkNextCandidate;
	  }
	  if( config.entailed_debug > 4 ) cerr << "c " << candidate[n] << " < " << c[m] << " -> resolveLit: " << resolveLit << endl;
	  data.lits.push_back( ~resolveLit );
	  n ++;
	}
      }
      for( ; n < candidate.size(); ++ n ) {
	if( resolveLit == lit_Undef ) resolveLit = candidate[n];
	  else if( resolveLit != lit_Undef ) { resolveLit = lit_Error; break; }
	  data.lits.push_back( ~resolveLit );
      }
      
      
      if( resolveLit != lit_Error ) for( ;m < c.size(); ++m ) data.lits.push_back(c[m]);
      if( resolveLit == lit_Undef ) { // candidate subsumes other clause - subsume, continue
	subsumed ++;
	if( config.entailed_debug > 1 ) cerr << "c " << candidate << " subsumes " << c << "(" << clss[i] << " - " << cr << ")" << endl;
	data.clss.push_back(cr);
	goto checkNextClause;
      } else if ( resolveLit == lit_Error ) {
	continue; // candidate is no candidate!
      } else {
	if( config.entailed_debug > 3 ) cerr << "c found candidate " << candidate << " with missing vector " << data.lits << endl;
	if( data.lits.size() == 1 ) {
	  if( config.entailed_debug > 1 ) cerr << "c " << c << " extra-subsumes " << candidate << endl;
	  candidate.set_delete(true);
	  data.removedClause( clss[i] );
	  extraSubs ++;
	  continue;
	}
	assert(data.lits.size() > 1 && "there have to be some missing literals!" );
	// find a clause that contains all literals in the vector data.lits, and furthermore contains only literals that appear in the clause c
	Lit min2 = data.lits[0];
	for( int j = 1 ; j < data.lits.size(); ++ j ) min2 = data[min2] <= data[data.lits[j]] ? min2 : data.lits[j];
	const vector<CRef>& matches = data.list( min2 );
	for( int j = 0 ; j < matches.size(); ++ j ) {
	  const CRef cr2 = matches[j];
	  if( cr2 == cr || cr2 == clss[i] ) continue; // do not handle same clause twice!
	  const Clause& c2 = ca[cr2];
	  if( c2.can_be_deleted() || c2.size() < data.lits.size() || c2.learnt() ) continue; // this clause is too small to contain all literals in data.lits
	  if( config.entailed_debug > 4 ) cerr << "c consider as match: " << c2 << endl;
	  int n = 0; // for literals inside data.lits
	  int m = 0; // for literals inside the clause
	  
	  while( n < data.lits.size() && m < c2.size() ) {
	    if( data.lits[n] == c2[m] ) { // match
	      n++; m++;
	    } else if( c2[m] < data.lits[n] ) { // there is a literal inside c2, which is not inside data.lits - check whether in c
	      if( !data.ma.isCurrentStep( toInt(c2[m] ) ) ) {
		if( config.entailed_debug > 3 ) cerr << "c reject match " << c2 << " , because " << c2[m] << " notin " << c << endl;
		goto checkNextMatch; // not inside c -> no match for the current candidate
	      }
	      m ++;
	    } else if( data.lits[n] < c2[m] ) { // there is a literal inside data.lits, which is not inside c2
	      if( config.entailed_debug > 3 ) cerr << "c reject match " << c2 << " , because " << data.lits[n] << " notin " << c2 << endl;
	      goto checkNextMatch; // not inside data.lits -> no match for the current candidate
	    }
	  }
	  
	  if( n < data.lits.size() ) {
	    if( config.entailed_debug > 3 ) cerr << "c reject match " << c2 << " , because " << data.lits[n] << " notin " << c2 << endl;
	    goto checkNextMatch; // not all literals found -> not match for current candidate
	  }
	  for( ; m<c2.size(); ++m ) { // check whether all remaining literals are also part of c
	    if( !data.ma.isCurrentStep( toInt(c2[m] ) ) ) {
		if( config.entailed_debug > 3 ) cerr << "c reject match " << c2 << " , because " << c2[m] << " notin " << c << endl;
		goto checkNextMatch; // not inside c -> no match for the current candidate
	      }
	  }
	  
	  // here, candidate and match are found!
	  if( config.entailed_debug > 0 ) cerr << "c ENT clause " << c << " is resolvent of " << candidate << " and " << c2 << endl;
	  data.clss.push_back(cr);
	  goto checkNextClause;
	  
	  checkNextMatch:;
	}
      }
      checkNextCandidate:;
    }
    
    checkNextClause:;
  }
  
  // remove all found clauses!
  for( int i = 0 ; i < data.clss.size(); ++ i ) 
  {
    if( config.entailed_debug > 3 ) cerr << "c ENT remove clause " << ca[data.clss[i]] << endl;
    ca[data.clss[i]].set_delete(true);
    data.removedClause( data.clss[i] );
  }
  removedClauses += data.clss.size();
  
  return false;
}
    
void EntailedRedundant::printStatistics(ostream& stream)
{
  stream << "c [STAT] ENT " << processTime << " s, " << removedClauses << " cls, " << subsumed << " subs, " << extraSubs << " extraSubs, " << endl;
}

void EntailedRedundant::giveMoreSteps()
{
  
}
  
void EntailedRedundant::destroy()
{
  
}