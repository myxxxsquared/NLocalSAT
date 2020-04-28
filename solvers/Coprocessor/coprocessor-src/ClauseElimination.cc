/*****************************************************************************[ClauseElimination.cc]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/ClauseElimination.h"

using namespace Coprocessor;

static const int cceLevel = 1;

ClauseElimination::ClauseElimination(CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, Propagation& _propagation)
: Technique( _config, _ca, _controller )
, propagation(_propagation)
, steps(0)
, processTime(0)
, removedClauses(0)
, removedBceClauses(0)
, removedNonEEClauses(0)
, cceSize(0)
, candidates(0)
{

}

void ClauseElimination::giveMoreSteps()
{
    steps = steps < config.opt_cceInpStepInc ? 0 : steps - config.opt_cceInpStepInc;
}


bool ClauseElimination::process(CoprocessorData& data)
{
  processTime = cpuTime() - processTime;
  
  if( ! performSimplification() ) return false; // do not do anything?!
  modifiedFormula = false;
  
  if( data.outputsProof() ) printDRUPwarning( cerr, "CCE cannot produce DRUP/DRAT proofs yet" );
  
  // do not simplify, if the formula is considered to be too large!
  if( !data.unlimited() && ( data.nVars() > config.opt_cce_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_cce_cls  && data.nTotLits() > config.opt_cce_lits ) ) return false;
  if( !data.ok() ) return modifiedFormula;
  
  // TODO: have a better scheduling here! (if a clause has been removed, potentially other clauses with those variables can be eliminated as well!!, similarly to BCE!)
  if( config.opt_ccelevel == 0 ) return modifiedFormula; // do not run anything!

  if( propagation.process(data,true) == l_False){
    if( config.cce_debug_out > 0 ) cerr << "c propagation failed" << endl;
    data.setFailed();
    return modifiedFormula;
  }
  modifiedFormula = modifiedFormula || propagation.appliedSomething();

  uint32_t maxSize = 0;
  for( uint32_t i = 0 ; i< data.getClauses().size() ; ++ i ) {
    const CRef ref = data.getClauses()[i];
    Clause& clause = ca[ ref ];
    if( clause.can_be_deleted() ) continue;
    maxSize = clause.size() > maxSize ? clause.size() : maxSize;
  }
  
  cceSize = (maxSize * config.opt_ccePercent) / 100;
  cceSize = cceSize > 2 ? cceSize : 3;	// do not process binary clauses
  if( config.cce_debug_out > 0 ) cerr << "c work on clauses larger than " << cceSize << " maxSize= " << maxSize << endl;
  WorkData wData( data.nVars() );
  for( int i = 0 ; i < data.getClauses().size(); ++ i )
  {
    if( ca[ data.getClauses()[i] ].size() <= cceSize ) continue; // work only on very large clauses to eliminate them!
    if( ca[ data.getClauses()[i] ].can_be_deleted() ) continue;
    if( config.cce_debug_out > 1) cerr << "c work on clause " << ca[ data.getClauses()[i] ] << endl;
    candidates ++;
    eliminate(data, wData, data.getClauses()[i] );
    if( !data.unlimited() && steps > config.opt_cceSteps ) break;
    // FIXME: not possible here, because clause vector is also modified! data.garbageCollect();
  }
  steps += wData.steps;
  removedBceClauses += wData.removedBceClauses;
  removedClauses += wData.removedClauses;
  removedNonEEClauses += wData.removedNonEEClauses;
  processTime = cpuTime() - processTime;
  return modifiedFormula;
}

bool ClauseElimination::eliminate(CoprocessorData& data, ClauseElimination::WorkData& wData, Minisat::CRef cr)
{
  assert(config.opt_ccelevel > 0 && "level needs to be higher than 0 to run elimination" );
  // put all literals of the clause into the mark-array and the other vectors!
  const Clause& c = ca[cr];
  if( c.can_be_deleted() ) return false;
  if( config.cce_debug_out > 2 ) cerr << "c process " << c << endl;
  wData.reset();
  if( config.cce_debug_out > 1 ) cerr <<  "do cce on " <<  c << endl;
  for( int i = 0; i < c.size(); ++ i ) {
    const Lit& l = c[i];
    wData.array.setCurrentStep( toInt(l) );
    wData.cla.push_back(l);
    if( !data.doNotTouch(var(l)) ) wData.toProcess.push_back(l);        // only if semantics is not allowed to be changed!
/*
    wData.toUndo.push_back(lit_Undef);
    wData.toUndo.push_back(l);
    cerr << "c CLA add to current extension: " << l << endl;
    for( int k = 0 ; k < beforeCla; ++ k ) {
      if( l != wData.cla[k] ) wData.toUndo.push_back( wData.cla[k] );
      */
  }
  
  int oldProcessSize = -1; // initially, do both ALA and CLA!
  bool doRemoveClause = false;
  bool preserveEE = true;
  while( true ) {
    
    for( int i = 0 ; i < wData.toProcess.size(); ++i ) {                          // do ALA for all literals in the array (sometimes also again!)
      const Lit l = wData.toProcess[i];
      assert( l != lit_Undef && l != lit_Error && "only real literals can be in the queue" );
      if( config.cce_debug_out > 1 ) cerr << "ALA check list of literal " << l << endl;
      const vector<CRef>& lList = data.list(l);
      for( int j = 0 ; j < lList.size(); ++ j ) { // TODO: add step counter here!
        if( lList[j] == cr ) continue;                                            // to not work on the same clause twice!
	const Clause& cj = ca[lList[j]];
	if( cj.can_be_deleted() || cj.learnt() ) continue;                                       // act as the clause is not here
	wData.steps ++;
	if( config.cce_debug_out > 1 ) cerr << "c analyze " << cj << endl;
	if( cj.size() > wData.toProcess.size() + 1 ) continue;                    // larger clauses cannot add a contribution to the array!
	Lit alaLit = lit_Undef;
	for( int k = 0 ; k < cj.size(); ++k ) {                                   // are all literals of that clause except one literal inside the array?
	  const Lit& lk = cj[k];
	  if( wData.array.isCurrentStep(toInt(lk)) ) continue;                    // literal is already in array
          else if (wData.array.isCurrentStep(toInt(~lk)) ) { alaLit = lit_Error; break; } // resolvent would be a tautology
          else if (alaLit != lit_Undef ) { alaLit = lit_Error; break; }           // more than one hitting literal
          else alaLit = lk;                                                       // literal which can be used to extend the array
	}
	if( alaLit == lit_Error ) continue; // to many additional literals inside the clause
	else if( alaLit == lit_Undef ) { doRemoveClause=true; break; }
	alaLit = ~alaLit;
	if( config.cce_debug_out > 1 ) cerr << "c found ALA literal " << alaLit << endl;
	if( wData.array.isCurrentStep( toInt(alaLit) ) ) continue;
	if( wData.array.isCurrentStep( toInt(~alaLit) ) ) {                       // complement of current literal is also in CLA(F,C)
	  doRemoveClause = true; break;
	} else {
	  if( config.cce_debug_out > 1 ) cerr << "c add literal " << alaLit << " to ALA for " << cj << endl;
	  wData.array.setCurrentStep( toInt(alaLit) );
	  if( !data.doNotTouch(var(alaLit)) ) wData.toProcess.push_back(alaLit);  // only if semantics is not allowed to be changed!
          // i = -1; break; // need to redo whole calculation, because one more literal has been added!
	  // exit(0);
	}
      }
      if( doRemoveClause  ) { 
	if( config.cce_debug_out > 1 ) cerr <<  "c ALA found tautology for " << c << endl;
	break;
      }
    } // tested all literals for ALA
    if( oldProcessSize == wData.toProcess.size() || config.opt_ccelevel < 2) break;         // no new literals found (or parameter does not allow for CLA)
    
    bool foundMoreThanOneClause = false;
    int outerOldClaSize = wData.cla.size();
    if( config.cce_debug_out > 1 ) cerr << "c start process iteration with cla size " << wData.cla.size() << endl;
    for( int i = wData.nextAla ; i < wData.toProcess.size(); ++i ) {              // do CLA for all literals that have not been tested yet!
      bool firstClause = true;
      
      int oldClaSize = wData.cla.size(); // remember old value to check whether something happened!
      const Lit l = ~wData.toProcess[i];
      if( config.cce_debug_out > 2 )  cerr << "c work on literal " << l << endl;
      assert( l != lit_Undef && l != lit_Error && "only real literals can be in the queue" );
      if( config.cce_debug_out > 1 ) cerr << "c CLA check literal " << l << endl;
      if( config.cce_debug_out > 2 ) cerr << "c start inner iteration with cla size " <<  wData.cla.size()  << endl;
      
      if( config.cce_debug_out > 0 ) {
	cerr << "c current virtual clause: " << endl;
	for( Var tv = 0 ; tv < data.nVars(); ++ tv ) 
	  for( int tp = 0 ; tp < 2; tp ++ )
	    if( wData.array.isCurrentStep( toInt( mkLit(tv,tp==1) ) ) ) cerr << " " << mkLit(tv,tp==1) ;
	cerr << endl;
      }
      
      
      const vector<CRef>& lList = data.list(l);
      int beforeCla = wData.cla.size();
      for( int j = 0 ; j < lList.size(); ++ j ) { // TODO: add step counter here!
        const Clause& cj = ca[lList[j]];
	if( cj.can_be_deleted()  || cj.learnt() ) continue;                                       // act as the clause is not here
	wData.steps ++;
	if( firstClause ) {                                                       // first clause fills the array, the other shrink it again
          if( config.cce_debug_out > 1 ) cerr << "c analyze as first " << cj << endl;
          for( int j = 0 ; j < cj.size(); ++j ) {
	    if( cj[j] == l ) continue;
	    if( wData.array.isCurrentStep( toInt(~cj[j] ) ) ) {
	      wData.cla.resize( oldClaSize );
	      if( config.cce_debug_out ) cerr << "c reduce CLA back to old size, because literal " << cj[j] << " leads to tautology " << endl;
	      goto ClaNextClause;
	    } else if( !wData.array.isCurrentStep( toInt(cj[j]) ) ) { // TODO: check whether this needs to be done! if( !wData.array.isCurrentStep( toInt( cj[j] ) ) ) { // add only, if not already in!
	      // FIXME: ensure that a literal is not added twice!
	      wData.cla.push_back(cj[j]);
	      if( config.cce_debug_out > 0 ) cerr << "c add " << cj[j] << " to CLA" << endl;
	      if( config.cce_debug_out > 0  && wData.array.isCurrentStep( toInt( cj[j] ) ) ) cerr << "c regard resolvent literal that is already in the virtual clause: " << cj[j] << endl;
	    }
	  }
	  if( wData.cla.size() == beforeCla ) break; // no new literal -> jnothing to be added with CLA
	  firstClause = false; // only had first clause, if not tautology!
	  if( config.cce_debug_out > 1 ) cerr << "c increased(/kept) cla to " << wData.cla.size() << endl;
	} else { // not the first clause
          if( config.cce_debug_out > 1 ) cerr << "c analyze as following " << cj << endl;
// TODO: not necessary?!          //int resetTo = wData.cla.size();  // store size of cla before this clause to be able to reset it
	  wData.helpArray.nextStep();
          for( int j = 0 ; j < cj.size(); ++j ){   // tag all literals inside the clause
	     if( cj[j] == l ) continue; // do not tag the literal itself!
            if( wData.array.isCurrentStep( toInt(~cj[j]) ) ){  // this clause produces a tautological resolvent
	      if( config.cce_debug_out ) cerr << "c reduce CLA back to old size, because literal " << cj[j] << " leads to tautology " << endl;
	      goto ClaNextClause;
	    }
	    wData.helpArray.setCurrentStep( toInt(cj[j]) );
	  }
	  foundMoreThanOneClause = true;
	  int current = oldClaSize;                                      // store current size of cla, so that it can be undone
	  for( int j = oldClaSize; j < wData.cla.size(); ++ j )          // only use literals inside cla that are tagged!
	    if( wData.helpArray.isCurrentStep( toInt(wData.cla[j]) ) ){   // if the literal has been in the clause
	      if( config.cce_debug_out > 1 ) cerr << "c keep in cla this time " << wData.cla[j] << endl;
              wData.cla[current++] = wData.cla[j];                       // move the literal inside the cla vector
	    }
	  if( current == oldClaSize ) { // stop cla, because the set is empty
	    if( config.cce_debug_out > 0 ) cerr << "c do not add any literals under current literal" << endl;
	    wData.cla.resize(oldClaSize); break;
	  } else {
	    if( config.cce_debug_out > 0 ) cerr << "c kept " << current - oldClaSize << " literals" << endl;
	  }
	  wData.cla.resize( current );        // remove all other literals from the vector!
	}
ClaNextClause:;
      } // processed all clauses of current literal inside of CLA
      if( config.cce_debug_out && !foundMoreThanOneClause ) cerr << "c found only one resolvent clause -- could do variable elimination!" << endl;
      // TODO: if something new has been found inside CLA, add it to the toBeProcessed vector, run ALA again!
      if( beforeCla < wData.cla.size() ) {
	preserveEE = false;
	// push current cla including the literal that led to it to the undo information
	wData.toUndo.push_back(lit_Undef);
	wData.toUndo.push_back( ~l );
	if( config.cce_debug_out ) cerr << "c CLA add to current extension: " << ~l << endl;
	for( int k = 0 ; k < beforeCla; ++ k ) {
	  if( ~l != wData.cla[k] ) wData.toUndo.push_back( wData.cla[k] );
	  if( wData.array.isCurrentStep( toInt(~wData.cla[k]) ) ) { 
	    doRemoveClause = true;
	    if( config.cce_debug_out )  cerr << "c found remove clause because it became tautology" << endl;
	  }
	}
	// these lines have been added after the whole algorithm!
	for( int k = beforeCla; k < wData.cla.size(); ++ k ) {
	  if( config.cce_debug_out > 1 ) cerr << "c consider " << wData.cla[k] << " for being added to cla" << endl;
	  if( !wData.array.isCurrentStep( toInt(wData.cla[k]) ) ) { // TODO: add only, if already there
	    wData.toProcess.push_back( wData.cla[k] );
	    wData.array.setCurrentStep( toInt(wData.cla[k]) );
	  } else {
	    if( config.cce_debug_out > 0 ) cerr << "c already out literal " << wData.cla[k] << " survived all resolvents, still, do not use it!" << endl; 
	    wData.cla[k] = wData.cla[ wData.cla.size() ];
	    wData.cla.pop_back();
	    --k;
	  }
	}
	if( config.cce_debug_out ) {
	  cerr << "c current undo: " << endl;
	  for( int k = 1 ; k < wData.toUndo.size(); ++ k ) {  
	    if( wData.toUndo[k] == lit_Undef ) cerr << endl;
	    else cerr << " " << wData.toUndo[k];
	  }
	  cerr << endl;
	}
      }
      if( doRemoveClause ) break;
      oldProcessSize = wData.toProcess.size();                    // store the size, so that CLA can recognize whether there is more to do
    } // processed all literals inside the processed vector
    if( config.cce_debug_out > 1 ) cerr << "c end process iteration with cla size " << wData.cla.size()  << endl;
    if( outerOldClaSize == wData.cla.size() || doRemoveClause) break;  // nothing found, or ATE with the clause -> stop
  } // end: while(true)
  
  // take care of the ALA vector, check for ATE, done already above
  // if not ATE, try to check BCE with mark array!
  if( ! doRemoveClause && config.opt_ccelevel > 2) {
    // TODO: go for ABCE 
    for( int i = 0 ; i < wData.cla.size() ; ++i ) {
       if( doRemoveClause = markedBCE( data, wData.cla[i], wData.array ) ) {
	 preserveEE = false;
	 wData.toUndo.push_back(lit_Undef);
	 wData.toUndo.push_back(wData.cla[i]);
	 if( config.cce_debug_out > 1 ) cerr << "c BCE sucess on literal " << wData.cla[i] << endl;
	 for( int j = 0 ; j < wData.cla.size(); ++ j )
	   if( wData.cla[i] != wData.cla[j] ) wData.toUndo.push_back( wData.cla[j] );
	 break; // need only removed by BCE once
       }
    }
    if( doRemoveClause ) {
      // TODO: take care that BCE clause is also written to undo information! 
      if( config.cce_debug_out > 1 ) cerr << "c cce with BCE was able to remove clause " << ca[cr] << endl;
      wData.removedBceClauses ++;
    }
  } 
  
  // TODO: put undo to real undo information!
  if( doRemoveClause ) {
    if( config.cce_debug_out > 1 ) cerr << "clause " << ca[cr] << " is removed by cce" << endl;
    ca[cr].set_delete(true);
    data.removedClause( cr );
    assert( (wData.toUndo.size() > 0 || preserveEE ) && "should not add empty undo information to extension!");
    if( wData.toUndo.size() > 0 ) {
      if( config.cce_debug_out > 0 ) cerr << "c store CCE backup data: " << wData.toUndo << endl;
      data.addExtensionToExtension( wData.toUndo );
    }
    wData.removedClauses ++;
    if( !preserveEE ) wData.removedNonEEClauses ++;
    modifiedFormula = true;
    return true;
  } else {
    if( config.cce_debug_out > 2 )  cerr << "clause " << ca[cr] << " cannot be removed by cce" << endl;
    return false; 
  }
}

bool ClauseElimination::markedBCE(const CoprocessorData& data, const Lit& l, const MarkArray& array)
{
  const Lit nl = ~l;
  if( data.doNotTouch( var(nl) ) ) return false; // not allowed to perform BCE on the current literal!
  for( int i = 0 ; i < data.list(nl).size(); ++ i )
    if( ! markedBCE(~l, ca[ data.list(nl)[i] ], array ) ) return false;
  return true;
}

bool ClauseElimination::markedBCE(const Lit& l, const Clause& c, const MarkArray& array)
{
  for( int i = 0 ; i < c.size(); ++ i ) 
    if( c[i] != l && array.isCurrentStep( toInt( ~c[i] )) ) return true;
  return false;
}

void ClauseElimination::initClause(const Minisat::CRef cr)
{

}

void ClauseElimination::destroy()
{
}




void ClauseElimination::parallelElimination(CoprocessorData& data)
{
  assert( false && "Method not yet implemented" );
}

void* ClauseElimination::runParallelElimination(void* arg)
{
  assert( false && "Method not yet implemented" );
  return 0;
}

void ClauseElimination::printStatistics(ostream& stream)
{
  stream << "c [STAT] CCE " << processTime << " s, " 
			    << removedClauses << " cls, " 
			    << removedNonEEClauses << " nonEE-cls, "
			    << removedBceClauses << " bce-cls, "
			    << steps << " checks "
			    << cceSize << " rejectSize "
			    << candidates << " candidates "
			    << endl;
}
