/*****************************************************************************************[rate.cc]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/rate.h"

using namespace Coprocessor;

RATElimination::RATElimination( CP3Config& _config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Solver& _solver, Propagation& _propagation )
: Technique(_config, _ca,_controller)
, data(_data)
, solver( _solver)
, propagation( _propagation )

, rateSteps(0)
, rateCandidates(0)
, remRAT(0)
, remAT(0)
, remHRAT(0)
, remBCE(0)
{
  
}


void RATElimination::reset()
{
  
}

bool RATElimination::process()
{
  MethodClock mc( rateTime );
  
  if( ! performSimplification() ) return false; // do not do anything?!
  modifiedFormula = false;
  
  // do not simplify, if the formula is considered to be too large!
  if( !data.unlimited() && ( data.nVars() > config.opt_rate_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_rate_cls && data.nTotLits() <= config.opt_rate_lits) ) return false;
  
  LitOrderRATEHeapLt comp(data, config.rate_orderComplements); // use this sort criteria!
  Heap<LitOrderRATEHeapLt> rateHeap(comp);  // heap that stores the variables according to their frequency (dedicated for BCE)
  
  // setup own structures
  rateHeap.addNewElement(data.nVars() * 2); // set up storage, does not add the element
  rateHeap.clear();

  // structures to have inner and outer round
  MarkArray nextRound;
  vector<Lit> nextRoundLits;
  nextRound.create(2*data.nVars());
  
  // make sure that all clauses in the formula do not contain assigned literals
  if( l_False == propagation.process(data,true) ) {
    return true;
  }
  
  // init
  for( Var v = 0 ; v < data.nVars(); ++ v )
  {
    if( data.doNotTouch(v) ) continue; // do not consider variables that have to stay fixed!
    if( data[  mkLit(v,false) ] > 0 ) if( !rateHeap.inHeap(toInt(mkLit(v,false))) )  nextRoundLits.push_back( mkLit(v,false) );
    if( data[  mkLit(v,true)  ] > 0 ) if( !rateHeap.inHeap(toInt(mkLit(v,true))) )   nextRoundLits.push_back( mkLit(v,true) );
  }
  data.ma.resize(2*data.nVars());
  data.ma.nextStep();
  
  // re-setup solver!
  const bool oldLhbrAllow = solver.lhbrAllowed;
  solver.lhbrAllowed = false;
  reSetupSolver();
  
  do {
    
    // re-init heap
    for( int i = 0 ; i < nextRoundLits.size(); ++ i ) {
      const Lit l = nextRoundLits[i];
      if( ! nextRound.isCurrentStep( toInt(l) ) ) continue; // has been processed before already
      assert( !rateHeap.inHeap(toInt(l)) && "literal should not be in the heap already!" );
      rateHeap.insert( toInt(l) );
    }
    nextRoundLits.clear();
    nextRound.nextStep();
    
    // do RAT Elimination on all the literals of the heap
    while (rateHeap.size() > 0 && (data.unlimited() || config.rate_Limit > rateSteps) && !data.isInterupted() )
    {
      // interupted ?
      if( data.isInterupted() ) break;
      
      const Lit right = toLit(rateHeap[0]);
      assert( rateHeap.inHeap( toInt(right) ) && "item from the heap has to be on the heap");
      rateHeap.removeMin();
      
      if( data.doNotTouch(var(right)) ) continue; // do not consider variables that have to stay fixed!

      // check whether a clause is a tautology wrt. the other clauses
      const Lit left = ~right; // complement
      if( config.opt_rate_debug > 0 ) cerr << endl << "c RATE work on literal " << right << " with " << data.list(right).size() << " clauses " << endl;
      if( config.opt_rate_debug > 3 ) cerr << "current trail: " << data.getTrail() << endl;
      data.lits.clear(); // used for covered literal elimination
      for( int i = 0 ; i < data.list(right).size(); ++ i ) 
      {
	Clause& c = ca[ data.list(right)[i] ];
	if( c.can_be_deleted() || c.learnt() ) continue; 
	if( c.size() < config.rate_minSize ) continue; // ignore "small" clauses
	
	rateCandidates ++;
	if( config.opt_rate_debug > 0 ) cerr << endl << "c test clause [" << data.list(right)[i] << "] " << c << endl;
	
	if( config.opt_rate_debug > 3 ) {
	  cerr << "c current formula: " << endl;
	  for( int t = 0 ; t < data.getClauses().size(); ++ t ) {
	    if( ! ca[data.getClauses()[t]].can_be_deleted() ) cerr << "[" << data.getClauses()[t] << "] "<< ca[data.getClauses()[t]] << endl;
	  }
	  for( Var v = 0 ; v < data.nVars(); ++v ) {
	    for ( int p = 0 ; p < 2; ++ p ) {
	      const Lit l = mkLit(v,p==0);
	      if( data.list(l).size() > 0 ) {
		cerr << "c list(" << l << "): " << endl;
		for( int t = 0 ; t < data.list(l).size(); ++t ) if( !ca[ data.list(l)[t] ].can_be_deleted() ) cerr << "[" << data.list(l)[t] << "] " << ca[ data.list(l)[t] ] << endl;
		cerr << endl;
	      }
	    }
	  }
	}
	
	// literals to propagate
	data.lits.clear();
	for( int j = 0 ; j < c.size(); ++ j) if( c[j] != right ) data.lits.push_back( c[j] );
	const int defaultLits = data.lits.size(); // number of lits that can be kept for each resolvent
	
	data.lits.push_back(right); // to test whether c is AT, and hence can be removed by ATE
	
	solver.detachClause( data.list(right)[i], true ); // detach the clause eagerly
	assert( solver.decisionLevel() == 0 && "check can only be done on level 0" );
	solver.newDecisionLevel();
	if( config.opt_rate_debug > 2 ) cerr << "c enqueue complements in " << data.lits << endl;
	for( int j = 0 ; j < data.lits.size(); ++ j ) solver.uncheckedEnqueue( ~data.lits[j] ); // enqueue all complements
	CRef confl = solver.propagate(); // check whether unit propagation finds a conflict for (F \ C) \land \ngt{C}, and hence C would be AT
	rateSteps += solver.trail.size(); // approximate effort for propagation
	solver.cancelUntil(0); // backtrack
	if( confl != CRef_Undef ) {
	  remAT++;
	  for( int j = 0 ; j < ca[ data.list(right)[i]].size(); ++ j ) { // all complementary literals can be tested again
	    if( ! nextRound.isCurrentStep(toInt(~ca[ data.list(right)[i]][j]) ) ) {
	      nextRoundLits.push_back( ~ca[ data.list(right)[i]][j] );
	      nextRound.setCurrentStep( toInt(~ca[ data.list(right)[i]][j]) );
	    }
	  }

	  if( config.opt_rate_debug > 1 ) cerr << "c RATE eliminate AT clause [" << data.list(right)[i] << "] " << ca[data.list(right)[i]] << endl;
	  ca[ data.list(right)[i]] .set_delete(true);
	  data.removedClause( data.list(right)[i] );
	  data.addCommentToProof("AT clause during RATE");
	  data.addToProof(c,true);
	  continue;
	}
	
	
	data.lits.resize(defaultLits);
	// data.lits contains the complements of the clause C, except literal right.
	data.ma.nextStep();
	for( int j = 0 ; j < data.lits.size(); ++ j ) {
	  data.ma.setCurrentStep( toInt( data.lits[j] ) ); // mark all literals of c except right, for fast resolution checks
	}
	
	if( config.opt_rate_debug > 3 ) {
	  cerr << "c current formula: " << endl;
	  for( int t = 0 ; t < data.getClauses().size(); ++ t ) {
	    if( ! ca[data.getClauses()[t]].can_be_deleted() ) cerr << "[" << data.getClauses()[t] << "] "<< ca[data.getClauses()[t]] << endl;
	  }
	}
	
	
	if( config.opt_rate_debug > 2 ) cerr << "c RATE resolve with " << data.list(left).size() << " clauses" << endl;
	bool allResolventsAT = true;
	bool allTaut = true;
	for( int j = 0 ; allResolventsAT && j < data.list(left).size(); ++ j ) // for all clauses D \in F_{\ngt{l}}
	{
	  Clause& d = ca[ data.list(left)[j] ];
	  if( d.can_be_deleted() ) continue; // no resolvent required
	  rateSteps ++;
	  if( config.opt_rate_debug > 2 ) cerr << "c RATE resolve with clause [" << data.list(left)[j] << "]" << d << endl;
	  bool isTaut = resolveUnsortedStamped( right, d, data.ma, data.lits ); // data.lits contains the resolvent
	  rateSteps += d.size(); // approximate effort for resolution
	  if( config.opt_rate_debug > 2 ) cerr << "c RATE resolvent (taut=" << isTaut << ") : " << data.lits << endl;
	  
	  if( isTaut ) { data.lits.resize( defaultLits ); continue; } // if resolvent is a tautology, then the its also AT (simulates BCE). remove the literals from D from the resolvent again
	  else allTaut = false;

	  // test whether the resolvent is AT
	  solver.newDecisionLevel();
	  if( config.opt_rate_debug > 2 ) cerr << "c enqueue complements in " << data.lits << endl;
	  for( int k = 0 ; k < data.lits.size(); ++ k ) solver.uncheckedEnqueue( ~data.lits[k] );	// enqueue all complements
	  CRef confl = solver.propagate();	// check whether unit propagation finds a conflict for (F \ C) \land \ngt{C}, and hence C would be AT
	  rateSteps += solver.trail.size(); // approximate effort for propagation
	  if( config.opt_rate_debug > 2 ) cerr << "c propagate with conflict " << (confl != CRef_Undef ? "yes" : " no") << endl;
	  solver.cancelUntil(0);	// backtrack
	  if( confl == CRef_Undef ) allResolventsAT = false;	// not AT
	  data.lits.resize(defaultLits);	// remove the literals from D again
	  
	  if( !data.unlimited() && config.rate_Limit <= rateSteps) {	// check step limits
	    allResolventsAT = false; break; 
	  }
	}
	if( allResolventsAT ) {	// clause C is RAT, remove it!
	  data.addToExtension(data.list(right)[i], right); 
	  if( config.opt_rate_debug > 1 ) cerr << "c RATE eliminate RAT clause [" << data.list(right)[i] << "] " << c << endl;
	  c.set_delete(true);
	  remRAT = (!allTaut) ? remRAT+1 : remRAT;
	  remBCE = ( allTaut) ? remBCE+1 : remBCE;
	  for( int k = 0 ; k < c.size(); ++ k ) {	// all complementary literals can be tested again
	    if( ! nextRound.isCurrentStep(toInt(~c[k]) ) ) {
	      nextRoundLits.push_back( ~c[k] );
	      nextRound.setCurrentStep( toInt(~c[k]) );
	    }
	  }
	  data.addCommentToProof("rat clause during RATE");
	  data.addToProof(c,true);
	  data.removedClause( data.list(right)[i] );
	} else {
	  solver.attachClause( data.list(right)[i] ); // if clause cannot be removed by RAT Elimination, attach it again!
	}
      } // end iterating over all clauses that contain (right)
    }
  
  } while ( nextRoundLits.size() > 0 && (data.unlimited() || config.rate_Limit > rateSteps) && !data.isInterupted() ); // repeat until all literals have been seen until a fixed point is reached!

  solver.lhbrAllowed = oldLhbrAllow; // restore lhbr state!
  // clean solver!
  cleanSolver();
  
  return modifiedFormula;
}

bool RATElimination::resolveUnsortedStamped( const Lit l, const Clause& d, MarkArray& ma, vector<Lit>& resolvent )
{
    for( int i = 0 ; i < d.size(); ++ i ) {
      const Lit& dl = d[i];
      if( dl == ~l) continue; // on this literal we currently resolve
      if( ma.isCurrentStep( toInt( ~dl ) ) ) return true; // complementary literals in the resolvent
      if( ! ma.isCurrentStep( toInt(dl) ) ) {
	resolvent.push_back( dl );	// literal not yet present in resolvent, add it
      }
    }
    return false;
}

void RATElimination::printStatistics(ostream& stream)
{
  cerr << "c [STAT] RATE "  << rateTime.getCpuTime() << " seconds, " << rateSteps << " steps, "
  << rateCandidates << " checked, "
  << remRAT  << " rem-RAT, "
  << remBCE  << " rem-BCE, "
  << remAT   << " rem-AT, "
  << remHRAT << " rem-HRAT," << endl;
}

void RATElimination::giveMoreSteps()
{
  rateSteps = rateSteps < config.opt_bceInpStepInc ? 0 : rateSteps - config.opt_bceInpStepInc;
}
  
void RATElimination::destroy()
{
  
}

void RATElimination::cleanSolver()
{
  // clear all watches!
  solver.watches.cleanAll();
  
  // clear all watches!
  for (int v = 0; v < solver.nVars(); v++)
    for (int s = 0; s < 2; s++)
      solver.watches[ mkLit(v, s) ].clear();

  solver.learnts_literals = 0;
  solver.clauses_literals = 0;
  solver.watches.cleanAll();
  
  for( int i = 0 ; i < solver.learnts.size(); ++ i ) 
    ca[ solver.learnts[i] ].sort();
  for( int i = 0 ; i < solver.clauses.size(); ++ i ) 
    ca[ solver.clauses[i] ].sort(); 
}

void RATElimination::reSetupSolver()
{
  assert( solver.decisionLevel() == 0 && "solver can be re-setup only at level 0!" );
    // check whether reasons of top level literals are marked as deleted. in this case, set reason to CRef_Undef!
    if( solver.trail_lim.size() > 0 )
      for( int i = 0 ; i < solver.trail_lim[0]; ++ i )
        if( solver.reason( var(solver.trail[i]) ) != CRef_Undef )
          if( ca[ solver.reason( var(solver.trail[i]) ) ].can_be_deleted() )
            solver.vardata[ var(solver.trail[i]) ].reason = CRef_Undef;

    // give back into solver
    for( int p = 0 ; p < 1; ++ p ) { // do not use learned clauses, because they might be dropped without any notice later again
      vec<CRef>& clauses = (p == 0 ? solver.clauses : solver.learnts );
      for (int i = 0; i < clauses.size(); ++i)
      {
	  const CRef cr = clauses[i];
	  Clause & c = ca[cr];
	  assert( c.size() != 0 && "empty clauses should be recognized before re-setup" );
	  if ( !c.can_be_deleted() ) // all clauses are neccesary for re-setup!
	  {
	      assert( c.mark() == 0 && "only clauses without a mark should be passed back to the solver!" );
	      if (c.size() > 1)
	      {
		  // do not watch literals that are false!
		  int j = 1;
		  for ( int k = 0 ; k < 2; ++ k ) { // ensure that the first two literals are undefined!
		    if( solver.value( c[k] ) == l_False ) {
		      for( ; j < c.size() ; ++j )
			if( solver.value( c[j] ) != l_False ) 
			  { const Lit tmp = c[k]; c[k] = c[j]; c[j] = tmp; break; }
		    }
		  }
		  // assert( (solver.value( c[0] ) != l_False || solver.value( c[1] ) != l_False) && "Cannot watch falsified literals" );
		  
		  // reduct of clause is empty, or unit
		  if( solver.value( c[0] ) == l_False ) { data.setFailed(); return; }
		  else if( solver.value( c[1] ) == l_False ) {
		    if( data.enqueue(c[0]) == l_False ) { return; }
		    else { 
		      c.set_delete(true);
		    }
		    if( solver.propagate() != CRef_Undef ) { data.setFailed(); return; }
		    c.set_delete(true);
		  } else solver.attachClause(cr);
	      }
	      else if (solver.value(c[0]) == l_Undef)
		  if( data.enqueue(c[0]) == l_False ) { return; }
	      else if (solver.value(c[0]) == l_False )
	      {
		// assert( false && "This UNSAT case should be recognized before re-setup" );
		data.setFailed();
	      }
	  }
      }
    }
}


