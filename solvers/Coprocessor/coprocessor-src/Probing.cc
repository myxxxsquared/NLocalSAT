/**************************************************************************************[Probing.cc]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Probing.h"

using namespace Coprocessor;



Probing::Probing(CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Propagation& _propagation, EquivalenceElimination& _ee, Solver& _solver)
: Technique( _config, _ca, _controller )
, data( _data )
, solver( _solver )
, propagation ( _propagation )
, ee ( _ee )
, probeLimit(config.pr_prLimit)
, probeChecks(0)
, probeLHBRs(0)
, processTime(0)
, l1implied(0)
, l1failed(0)
, l1learntUnit(0)
, l1ee(0)
, l2implied(0)
, l2failed(0)
, l2ee(0)
, totalL2cand(0)
, probes(0)
, probeCandidates(0)
, l2probes(0)
, viviTime(0)
, viviLits(0)
, viviCls(0)
, viviCands(0)
, viviLimit(config.pr_viviLimit)
, viviChecks(0)
, viviSize(0)
, lhbr_news(0)
{

}


void Probing::giveMoreSteps()
{
probeChecks = probeChecks < config.pr_opt_inpStepInc1 ? 0 : probeChecks - config.pr_opt_inpStepInc1;
viviChecks = viviChecks < config.pr_opt_inpStepInc2 ? 0 : viviChecks - config.pr_opt_inpStepInc2;
}

bool Probing::process()
{
  MethodTimer mt( &processTime );
  if( ! performSimplification() ) return false; // do not do anything?!
  modifiedFormula = false;
  if( !data.ok() ) return false;
  
  // do not enter, if already unsatisfiable!
  if( (! config.pr_probe && ! config.pr_vivi) || !data.ok() ) return data.ok();
  
  // if all limits are reached, do not continue!
  if( !data.unlimited() && ( data.nVars() > config.opt_probe_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_probe_cls && data.nTotLits() > config.opt_probe_lits) ) {
    if( !data.unlimited() && ( data.nVars() > config.opt_viv_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_viv_cls   && data.nTotLits() > config.opt_viv_lits) ) {
      return false;
    }
  }
  
  // resetup solver
  reSetupSolver();
  
  data.ma.resize( data.nVars() * 2 );

  assert( solver.decisionLevel() == 0 && "decision level of solver has to be 0 before probing" );
  
  if( solver.propagate() != CRef_Undef ) {
    data.setFailed();
  } else {
    // run probing / vivi only, if the formula is not UNSAT before
    
    // safe the polarity for phase saving
    vec<Solver::VarFlags> polarity;
    solver.varFlags.copyTo( polarity );
    
    if( config.pr_debug_out > 0 ) cerr << "c brefore probing: cls: " << data.getClauses().size() << " vs. ls: " << data.getLEarnts().size() << endl;

    const int beforeClauses = data.getClauses().size();
    const int beforeLClauses = data.getLEarnts().size();
    
    // run probing?
    if( config.pr_probe && data.ok()  ) {
      
      // do not probe, if the formula is considered to be too large!
      if( data.unlimited() || ( data.nVars() <= config.opt_probe_vars || data.getClauses().size() + data.getLEarnts().size() <= config.opt_probe_cls   || data.nTotLits() <= config.opt_hte_lits ) ) {
	if( config.pr_debug_out > 0 ) cerr << "c old trail: " << solver.trail.size() << endl;
	probing();
	if( config.pr_debug_out > 0 ) cerr << "c new trail: " << solver.trail.size() << " solver.ok: " << data.ok() << endl;
      }
    }
    
    if( config.pr_debug_out > 0 ) cerr << "c after probing: cls: " << data.getClauses().size() << " vs. ls: " << data.getLEarnts().size() << endl;
    
    // run clause vivification?
    const int beforeVivClauses = data.getClauses().size();
    if( config.pr_vivi && data.ok() ) {
      if( data.unlimited() || ( data.nVars() <= config.opt_viv_vars || data.getClauses().size() + data.getLEarnts().size() <= config.opt_viv_cls  || data.nTotLits() <= config.opt_hte_lits ) ) {
	clauseVivification();
      }
      assert( solver.decisionLevel() == 0 && "after vivification the decision level should be 0!" );
    }

    if( config.pr_debug_out > 0 ) cerr << "c after vivification: cls: " << data.getClauses().size() << " vs. ls: " << data.getLEarnts().size() << endl;
    
    // restore the polarity for phase saving
    for( int i = 0 ; i < solver.varFlags.size(); ++ i ) solver.varFlags[i].polarity = polarity[i].polarity;

    // clean solver again!
    cleanSolver();
    
    for( int i = beforeClauses; i < data.getClauses().size(); ++ i ) data.addClause( data.getClauses()[i], config.pr_debug_out > 0 ); // incorporate new clauses into the solver
    probeLHBRs = probeLHBRs + data.getClauses().size() - beforeVivClauses; // stats
    
    if( beforeLClauses < data.getLEarnts().size() ) {
      if( config.pr_keepLHBRs > 0 ) {
	if( config.pr_debug_out ) cerr << "c add another " << data.getLEarnts().size() - beforeLClauses << " new learnt clauses to the formula" << endl;
	for( int i = beforeLClauses; i < data.getLEarnts().size(); ++ i ) {
	  data.addClause( data.getLEarnts()[i], config.pr_debug_out > 0 );
	}
      } else {
	if( config.pr_debug_out ) cerr << "c remove " << data.getLEarnts().size() - beforeLClauses << " new learnt clauses to the formula" << endl;
	for( int i = beforeLClauses; i < data.getLEarnts().size(); ++ i ) {
	  ca.free( data.getLEarnts()[i] ); // these clauses never made it into CP3 ... could also be added, parameter!
	}
	data.getLEarnts().shrink( data.getLEarnts().size() - beforeLClauses ); // if added, then do not remove!
      }
    }
    
    if( config.pr_debug_out > 3 ) {
      for( Var v = 0 ; v < data.nVars(); ++ v ) {
	for( int p = 0 ; p < 2; ++p ) {
	  const Lit l = mkLit(v, p==1);
	  vector<CRef>& list  = data.list( l );
	  cerr << "c data list for lit " << l << ": " << endl;
	  for( int i = 0 ; i < list.size(); ++ i ) {
	    cerr << "c [" << list[i] << "] : " << ca[ list[i] ] << " - " << (ca[ list[i] ].can_be_deleted() ? "del " : "keep" ) << endl;
	  }
	}
      }
    }
    
    sortClauses();
    if( propagation.process(data,true) == l_False){
      if( config.pr_debug_out > 1 ) cerr << "c propagation failed" << endl;
      data.setFailed();
    }
    modifiedFormula = modifiedFormula || propagation.appliedSomething();

    
    
    
    if( data.getEquivalences().size() > 0 ) {
      ee.applyEquivalencesToFormula(data); // do not search for lit-sccs, but apply found equivalences
      modifiedFormula = modifiedFormula || ee.appliedSomething();
    }
    
  }
  
  return data.ok();
}

CRef Probing::prPropagate( bool doDouble )
{
  // prepare tracking ternary clause literals
  doubleLiterals.clear();
  data.ma.nextStep();
  
  CRef    confl     = CRef_Undef;
    int     num_props = 0;
    solver.watches.cleanAll();

    if( config.pr_debug_out > 1 ) cerr << "c head: " << solver.qhead << " trail elements: " << solver.trail.size() << endl;
    solver.clssToBump.clear();
    while (solver.qhead < solver.trail.size()){
        Lit            p   = solver.trail[solver.qhead++];     // 'p' is enqueued fact to propagate.
        vec<Solver::Watcher>&  ws  = solver.watches[p];
        Solver::Watcher        *i, *j, *end;
        num_props++;
	
	if( config.pr_debug_out > 1 ) cerr << "c for lit " << p << " have watch with " << ws.size() << " elements" << endl;
	
	// probing should perform LHBR?
	if( config.pr_LHBR > 0 && solver.vardata[var(p)].dom == lit_Undef ) {
	  solver.vardata[var(p)].dom = p; // literal is its own dominator, if its not implied due to a binary clause
	  // if( config.opt_printLhbr ) cerr << "c undominated literal " << p << " is dominated by " << p << " (because propagated)" << endl; 
	}
	
	    // First, Propagate binary clauses 
	if( config.opt_pr_probeBinary ) { // option to disable propagating binary clauses in probing
	  const vec<Solver::Watcher>&  wbin  = solver.watches[p]; // this code needs to be added to the usual probing version!
	  
	  for(int k = 0;k<wbin.size();k++)
	  {
	    if( !wbin[k].isBinary() ) continue;
	    const Lit& imp = wbin[k].blocker();
	    assert( ca[ wbin[k].cref() ].size() == 2 && "in this list there can only be binary clauses" );
	    if(solver.value(imp) == l_False) {
	      return wbin[k].cref();
	    }
	    if(solver.value(imp) == l_Undef) {
	      solver.uncheckedEnqueue(imp,wbin[k].cref());
	      solver.vardata[ var(imp) ].dom = solver.vardata[ var(p) ].dom ; // set dominator
	    }
	  }
	}
	
        for (i = j = (Solver::Watcher*)ws, end = i + ws.size();  i != end;){
	    if( i->isBinary() ) { *j++ = *i++; continue; } // skip binary clauses (have been propagated before already!}
            // Try to avoid inspecting the clause:
            const Lit blocker = i->blocker();
            if (solver.value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            const CRef     cr        = i->cref();
            Clause&  c         = ca[cr];
	    // more fine grained probe limit
	    probeChecks++;
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            const Solver::Watcher w     = Solver::Watcher(cr, first, 1); // always a large clause
            if (first != blocker && solver.value(first) == l_True){
                *j++ = w; continue; }

            Lit commonDominator = (config.pr_LHBR ? solver.vardata[var(false_lit)].dom : lit_Error); // inidicate whether lhbr should still be performed
            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (solver.value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    solver.watches[~c[1]].push(w);
		    // track "binary clause" that has been produced by a ternary clauses!
		    if( doDouble && c.size() == 3 ) {
		      if( !data.ma.isCurrentStep(toInt(c[0])) ) {
			doubleLiterals.push_back(c[0]);
			data.ma.setCurrentStep(toInt(c[0]));
		      }
		      if( !data.ma.isCurrentStep(toInt(c[1])) ) {
			doubleLiterals.push_back(c[1]);
			data.ma.setCurrentStep(toInt(c[1]));
		      }
		    }
                    goto NextClause;
		} // no need to indicate failure of lhbr, because remaining code is skipped in this case!
                else { // lhbr analysis! - any literal c[k] culd be removed from the clause, because it is not watched at the moment!
		  assert( data.value(c[k]) == l_False && "for lhbr all literals in the clause need to be set already" );
		  if( commonDominator != lit_Error ) { // do only, if its not broken already - and if limit is not reached
		    commonDominator = ( commonDominator == lit_Undef ? 
				solver.vardata[var(c[k])].dom : 
				( commonDominator != solver.vardata[var(c[k])].dom ? lit_Error : commonDominator ) );
		  }
		}

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (solver.value(first) == l_False){
                confl = cr;
                solver.qhead = solver.trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            } else { // the current clause is a unit clause, hence, LHBR might also be possible!
                solver.uncheckedEnqueue(first, cr);
		
		if( config.pr_LHBR ) solver.vardata[ var(first) ].dom = solver.vardata[ var(first) ].dom ; // set dominator for this variable!
		
		// check lhbr!
		if( commonDominator != lit_Error && commonDominator != lit_Undef ) { // no need to ask for permission, because commonDominator would be lit_Error anyways
		  solver.oc.clear();
		  solver.oc.push(first);
		  solver.oc.push(~commonDominator);
		  
		  data.addCommentToProof("added by LHBR");
		  data.addToProof( solver.oc ); // if drup is enabled, add this clause to the proof!
		  
		  // if commonDominator is element of the clause itself, delete the clause (hyper-self-subsuming resolution)
		  const bool clearnt = c.learnt();
		  float cactivity = 0;
		  if( clearnt ) cactivity = c.activity();
		  bool willSubsume = false;
		  if( true ) { // check whether the new clause subsumes the other
		    for( int k = 1; k < c.size(); ++ k ) if ( c[k] == ~commonDominator ) { willSubsume = true; break; }
		  }
		  lhbr_news ++;
		  if( willSubsume )
		  { // created a binary clause that subsumes this clause  FIXME: actually replace this clause here instead of creating a new one! adapt code below!
		    if( c.mark() == 0 ){
		      data.addCommentToProof("Subsumed by LHBR clause", true);
		      data.addToProof(c,true);  // remove this clause from the proof, if not done already
		    }
		    c.mark(1); // the bigger clause is not needed any more
		  } 
		  // a new clause is required
		  CRef cr2 = ca.alloc(solver.oc, clearnt ); // add the new clause - now all references could be invalid!
		  if( clearnt ) { ca[cr2].setLBD(1); solver.learnts.push(cr2); ca[cr2].activity() = cactivity; }
		  else solver.clauses.push(cr2);
		  solver.clssToBump.push(cr2); // add clause to solver lazily!
		  solver.vardata[var(first)].reason = cr2; // set the new clause as reason
		  solver.vardata[ var(first) ].dom = solver.vardata[ var(commonDominator) ].dom ; // set NEW dominator for this variable!
		  goto NextClause; // do not use references any more, because ca.alloc has been performed!
		} 
	    }

        NextClause:;
        }
        ws.shrink(i - j);
	for( int k = 0 ; k < solver.clssToBump.size(); ++k ) solver.attachClause(solver.clssToBump[k]); // add lhbr clauses lazily
	solver.clssToBump.clear();
    }


    return confl;
}

bool Probing::prAnalyze( CRef confl )
{
    learntUnits.clear();
    // do not do analysis -- return that nothing has been learned
    if( config.pr_uip == 0 && solver.decisionLevel() == 0) return false;
  
    if( config.pr_debug_out > 2 ) {
	for ( Var i = 0 ; i < data.nVars(); ++ i ) 
	  assert ( solver.varFlags[ i ].seen == 0 && "value has to be true!"); 
    }
    
    // genereate learnt clause - extract all units!
    int pathC = 0;
    Lit p     = lit_Undef;
    unsigned uips = 0;
    unsigned loops = 0;
    
    // Generate conflict clause:
    //
    data.lits.clear();
    data.lits.push_back(lit_Undef);      // (leave room for the asserting literal)
    
    int index   = solver.trail.size() - 1;

    if( config.pr_debug_out > 2 ) {
      for ( int i = 0 ; i < ca[confl].size(); ++ i ) 
	assert ( solver.varFlags[ var( ca[confl][i] ) ].seen == 0 && "value cannot be true!"); 
    }
    
    do{
        if( config.pr_debug_out > 3 ) cerr << "c next conflict [" << confl << "] with pathC= " << pathC << " and level " << solver.decisionLevel() << endl;
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        
        if( config.pr_debug_out > 3 ) {
        cerr << "c use for resolution " ;
	  for ( int i = 0 ; i < ca[confl].size(); ++ i ) cerr << " " << ca[confl][i] << "@" << solver.level(var(ca[confl][i])) ;
	  cerr << endl;
	}
        
        loops ++;
        // take care of level 2 decision!
        if( confl != CRef_Undef ) {
        
	  Clause& c = ca[confl];

	  // Special case for binary clauses
	  // The first one has to be SAT
	  if( p != lit_Undef && c.size()==2 && solver.value(c[0])==l_False) {
	    assert(solver.value(c[1])==l_True && "the other literal has to be satisfied!" );
	    Lit tmp = c[0];
	    c[0] =  c[1], c[1] = tmp;
	  }
	  
	  for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
	      Lit q = c[j];

	      if (!solver.varFlags[var(q)].seen && solver.level(var(q)) > 0){
		  solver.varBumpActivity(var(q));
		  if( config.pr_debug_out > 2 ) cerr << "c set seen INT for " << var(q) +1<< endl;
		  solver.varFlags[var(q)].seen = 1; // for every variable, which is not on level 0, set seen!
		  if (solver.level(var(q)) >= solver.decisionLevel())
		      pathC++;
		  else
		      data.lits.push_back(q);
	      }
	  }
        
	}
	
	assert ( (loops != 1 || pathC > 1) && "in the first iteration there have to be at least 2 literals of the decision level!" );
	
        // Select next clause to look at:
        while (!solver.varFlags[var(solver.trail[index--])].seen ) ;
        p     = solver.trail[index+1];
        confl = solver.reason(var(p));
	assert( solver.varFlags[var(p)].seen == 1 && "this variable should have been inside the clause" );
        solver.varFlags[var(p)].seen = 0;
	if( config.pr_debug_out > 2 ) cerr << "c reset seen INT for " << var(p) +1 << endl;
        pathC--;

	// this works only is the decision level is 1
	if( pathC <= 0 ) {
	  assert( loops > 1 && "learned clause can occur only if already 2 clauses have been resolved!" );
	  if( solver.decisionLevel() == 1) {
	   if( config.pr_debug_out > 1 ) cerr << "c possible unit: " << ~p << endl;
	   uips ++;
	   // learned enough uips - return. if none has been found, return false!
	   if( config.pr_uip != -1 && uips > config.pr_uip ) {
	     // reset seen literals
	     assert( data.lits[0] == lit_Undef && "so far the lit_undef from the first position should not be overwritten" );
	     for( int i = 1 ; i < data.lits.size(); ++ i ){
	       solver.varFlags[ var(data.lits[i]) ].seen = 0;
	       if( config.pr_debug_out > 2 ) cerr << "c reset seen ALLUIP for " << var(data.lits[i]) +1 << endl;
	     }
	     
	     if( config.pr_debug_out > 2 ) {
		  for ( Var i = 0 ; i < data.nVars(); ++ i ) 
		    assert ( solver.varFlags[ i ].seen == 0 && "value has to be true!"); 
	     }
	     
	     return learntUnits.size() == 0 ? false : true;
	   }
	   learntUnits.push(~p);
	  } else {
	    static bool didit = false;
	    if( !didit ) { cerr << "[TODO] have more advanced learning routine for level 1 ?!?" << endl; didit = true; }
	    break;
	  }
	}
	
    }while (index >= solver.trail_lim[0] ); // pathC > 0 finds unit clauses
    data.lits[0] = ~p;
  
    // reset seen literals
    for( int i = 0 ; i < data.lits.size(); ++ i ) {
      solver.varFlags[ var(data.lits[i]) ].seen = 0;
      if( config.pr_debug_out > 2 ) cerr << "c reset seen EXT for " << var(data.lits[i]) +1 << endl;
    }
    
    // print learned clause
    if( config.pr_debug_out > 1 ) {
      cerr << "c probing returned conflict: ";
      for( int i = 0 ; i < data.lits.size(); ++ i ) cerr << " " << data.lits[i];
      cerr << endl;
    }

  if( config.pr_debug_out > 2 ) {
      for ( Var i = 0 ; i < data.nVars(); ++ i ) 
	assert ( solver.varFlags[ i ].seen == 0 && "value has to be true!"); 
  }
    
  // NOTE no need to add the unit again, has been done in the loop already!
  
  return true;
}

bool Probing::prDoubleLook(Lit l1decision)
{
  // reject double lookahead, if necessary!
  if( ! config.pr_double ) return false;
  
  data.ma.nextStep();
  
  if( config.pr_debug_out > 0 ) cerr << "c double lookahead after " << l1decision << " at level 1" << endl;
  
  // TODO: sort literals in double lookahead queue, use only first n literals
  // static bool didit = false;
  // if( !didit ) { cerr << "c sort literals in double queue according to some heuristic (occurrences, ... )" << endl; didit = true; }
  
  CRef thisConflict = CRef_Undef;
  
  for( int i = 0 ; i < doubleLiterals.size(); ++ i )
  {
    Var v = var(doubleLiterals[i]);
    if( solver.value(v) != l_Undef || data.ma.isCurrentStep(v) ) continue; // no need to check assigned variable!
    data.ma.setCurrentStep(v); // do each variable only once per level!

    // cerr << "c test variable " << v + 1 << endl;

    assert( solver.decisionLevel() == 1 && "probing only at level 1!");
    const Lit posLit = doubleLiterals[i];
    if( config.pr_debug_out > 0 ) cerr << "c deciding " << posLit << " at level 2" << endl;
    solver.newDecisionLevel();
    solver.uncheckedEnqueue(posLit);
    l2probes++;
    probeChecks++;
    thisConflict = prPropagate();
    if( config.pr_debug_out > 1 ) cerr << "c conflict after level 2 propagate " << posLit << " present? " << (thisConflict != CRef_Undef) << " trail elements: " << solver.trail.size() << endl;
    
    if( config.pr_debug_out > 1 ) {
      cerr << "c current trail: ";
      for( int k = 0 ; k < solver.trail.size(); ++ k )
	cerr << " " << solver.trail[k];
      cerr << endl;
    }
    
    if( thisConflict != CRef_Undef ) {
      l2failed++;
      prAnalyze( thisConflict );
      int backtrack_level = 1;
      if( data.lits.size() == 0 ) {
	data.lits.push_back(~l1decision);
	data.lits.push_back(~posLit);
      } else {
	if( data.lits.size() == 1 ) backtrack_level = 0;
	else backtrack_level = solver.level( var( data.lits[1] ) );
      }
      
      if( config.pr_debug_out > 0 ){ 
	cerr << "c learnt clause at level " << solver.decisionLevel() << " with jump to " << backtrack_level << " after decideing " << l1decision << " and " << posLit << " ";
	for( int i = 0 ; i < data.lits.size(); ++i ) cerr << " " << data.lits[i];
	cerr << endl;
      }
      
      solver.cancelUntil(backtrack_level);
      if (data.lits.size() == 1){
	// cerr << "c unit lit is unsat: " << (data.value( data.lits[0] ) == l_False) << endl;
	data.addCommentToProof("found unit during doubble look ahead");
	data.addUnitToProof( data.lits[0] );
	solver.enqueue(data.lits[0]);
	// cerr << "c return value for enqueing lit " << data.lits[0] << " is " << ret << endl;
	if( config.pr_debug_out > 0 ) cerr << "c L2 learnt clause: " << data.lits[0] << " 0" << endl;
      } else {
	CRef cr = ca.alloc(data.lits, config.pr_keepLearnts == 1);
	data.addCommentToProof("add learned clause that is added during double look ahead");
	data.addToProof(data.lits);
	// solver.clauses.push(cr);
	solver.attachClause(cr);
	l2conflicts.push_back(cr);
	solver.uncheckedEnqueue(data.lits[0], cr);
	if( config.pr_debug_out > 0 ) cerr << "c L2 learnt clause, adding to l2conflicts: ("<<cr<<")" << ca[cr] << " 0" << endl;
      }
      
      CRef cClause = solver.propagate() ;
      if( cClause != CRef_Undef ) { 
	if( solver.decisionLevel() == 0 ) {
	   data.setFailed(); return true;
	}
	if( config.pr_debug_out > 1 ) {
	  cerr << "c l1 propagating (" << data.lits << ") learned clause at level " << solver.decisionLevel() << " failed" << endl;
	} 
	// perform l1 analysis - as in usual probing routine
	l1failed++;
	if( !prAnalyze( cClause ) ) {
	  learntUnits.push( ~l1decision );
	}
	solver.cancelUntil(0);
	// tell system about new units!
	for( int i = 0 ; i < learntUnits.size(); ++ i ) {
	  data.addUnitToProof( learntUnits[i] );
	  data.enqueue( learntUnits[i] );
	}
	if( !data.ok() ) return true; // interrupt loop, if UNSAT has been found!
	l1learntUnit+=learntUnits.size();
	if( solver.propagate() != CRef_Undef ) { data.setFailed(); return true; } // UNSAT has been found - current state is level 0
	
	return true; 
      }
      if( solver.decisionLevel() == 1 ) {i--;continue;}
      else return true;
    }
    solver.varFlags.copyTo( prL2Positive );
    // other polarity
    solver.cancelUntil(1);
    
    assert( solver.decisionLevel() == 1 && "probing only at level 1!");
    const Lit negLit = ~posLit;
    if( config.pr_debug_out > 0 )  cerr << "c deciding " << negLit << " at Level 2" << endl;
    solver.newDecisionLevel();
    solver.uncheckedEnqueue(negLit);
    l2probes++;
    probeChecks++;
    thisConflict = prPropagate();
    if( config.pr_debug_out > 1 ) cerr << "c conflict after level 2 propagate " << negLit << " present? " << (thisConflict != CRef_Undef) << " trail elements: " << solver.trail.size() << endl;
    if( config.pr_debug_out > 1 ) {
      cerr << "c current trail: ";
      for( int k = 0 ; k < solver.trail.size(); ++ k )
	cerr << " " << solver.trail[k];
      cerr << endl;
    }
    if( thisConflict != CRef_Undef ) {
      l2failed++;
      prAnalyze( thisConflict );
      int backtrack_level = 1;
      if( data.lits.size() == 0 ) {
	data.lits.push_back(~l1decision);
	data.lits.push_back(~negLit);
      } else {
	if( data.lits.size() == 1 ) backtrack_level = 0;
	else backtrack_level = solver.level( var( data.lits[1] ) );
      }
      if( config.pr_debug_out > 0 ) {
	cerr << "c learnt clause at level " << solver.decisionLevel() << " with jump to " << backtrack_level << " after decideing " << l1decision << " and " << negLit << " :  ";
	for( int i = 0 ; i < data.lits.size(); ++i ) cerr << " " << data.lits[i];
	cerr << endl;
      }
      solver.cancelUntil(backtrack_level);
      if (data.lits.size() == 1){
	solver.enqueue(data.lits[0]);
	data.addCommentToProof("add clause during double look ahead");
	data.addUnitToProof( data.lits[0] );
	if( config.pr_debug_out > 0 ) cerr << "c L2 learnt clause: " << data.lits[0] << " 0" << endl;
      }else{
	CRef cr = ca.alloc(data.lits, config.pr_keepLearnts == 1);
	// solver.clauses.push(cr);
	data.addCommentToProof("add clause during double look ahead");
	data.addToProof( data.lits );
	solver.attachClause(cr);
	l2conflicts.push_back(cr);
	solver.uncheckedEnqueue(data.lits[0], cr);
	if( config.pr_debug_out > 0 ) cerr << "c L2 learnt clause, adding to l2conflicts: ("<<cr<<")" << ca[cr] << " 0" << endl;
      }
      CRef cClause = solver.propagate() ;
      if( cClause != CRef_Undef ) { if( config.pr_debug_out > 1 ) {
	cerr << "c l1 propagating (" << data.lits << ") learned clause at level " << solver.decisionLevel() << " failed" << endl;} 
	if( solver.decisionLevel() == 0 ) { // reached UNSAT here!
	  data.setFailed(); return true;
	}
	// perform l1 analysis - as in usual probing routine
	l1failed++;
	if( !prAnalyze( cClause ) ) {
	  learntUnits.push( ~l1decision );
	}
	solver.cancelUntil(0);
	// tell system about new units!
	for( int i = 0 ; i < learntUnits.size(); ++ i ) data.enqueue( learntUnits[i] );
	if( !data.ok() ) return true; // interrupt loop, if UNSAT has been found!
	l1learntUnit+=learntUnits.size();
	if( solver.propagate() != CRef_Undef ) { data.setFailed(); return true; } // UNSAT has been found - current state is level 0
	
	return true; 
      }
      if( solver.decisionLevel() == 1 ) {i--;continue;}
      else return true; // decision level == 0
    }
    // could copy to prNegatie here, but we do not do this, but refer to the vector inside the solver instead
   
    if( solver.decisionLevel() != 2 ) cerr << "c L2 lookahead resulted in decision level " << solver.decisionLevel() << endl;
    assert( solver.decisionLevel() == 2 && "double look-ahead can only be continued at level 1!");
    assert( solver.trail_lim.size() == 2 && "there have to be 2 decisions!" );
    
    // prepare new learnt clause!
    learntUnits.clear();
    learntUnits.push();
    learntUnits.push( ~l1decision );
    unsigned oldl2implieds = l2implieds.size();
    // look for necessary literals, and equivalent literals (do not add literal itself)
    if( config.pr_necBinaries ) { // if necessary assignments should be generated during probing, do it here!
      for( int i = solver.trail_lim[1] + 1; i < solver.trail.size(); ++ i )
      {
	// check whether same polarity in both trails, or different polarity and in both trails
	const Var tv = var( solver.trail[ i ] );
	if( config.pr_debug_out > 1 ) cerr << "c compare variable (level 1)" << tv + 1 << ": pos = " << toInt(prL2Positive[tv].assigns) << " neg = " << toInt(solver.varFlags[tv].assigns) << endl;
	if( solver.varFlags[ tv ].assigns == prL2Positive[tv].assigns ) {
	  if( config.pr_debug_out > 1 ) cerr << "c l2 implied literal: " << l1decision << " -> " << solver.trail[i] << endl;
	  learntUnits[0] = solver.trail[ i ];
	  l2implied ++;
	  CRef cr = ca.alloc(learntUnits, config.pr_keepImplied == 1);
	  l2implieds.push_back(cr);
	  data.addCommentToProof("learn implications for L2 necessary assignments");
	  data.addToProof( ca[cr] );
	} else { // this is for statistics only and is currently not handled!
  // 	if( 
  // 	  (solver.assigns[ tv ] == l_True && prPositive[tv] == l_False)
  // 	  || (solver.assigns[ tv ] == l_False && prPositive[tv] == l_True)
  // 	) l2ee ++;
	}
	
      }
    }
    
    solver.cancelUntil(1);
    
    if( config.pr_debug_out > 1 ) {
      cerr << "c current trail: ";
      for( int k = 0 ; k < solver.trail.size(); ++ k )
	cerr << " " << solver.trail[k];
      cerr << endl;
    }
    
    // add all found implied literals!
    for( int i = oldl2implieds ; i < l2implieds.size(); ++i )
    {
      CRef cr = l2implieds[i];
      if( config.pr_debug_out > 1 ) cerr << "c add clause " << ca[cr] << endl;
      solver.attachClause(cr);
      solver.uncheckedEnqueue(ca[cr][0], cr);
    }

    // propagate implied(necessary) literals on level 1 inside solver
    thisConflict = solver.propagate() ;
    if( thisConflict != CRef_Undef ) {
      // perform l1 analysis - as in usual probing routine
      l1failed++;
      if( !prAnalyze( thisConflict ) ) {
	learntUnits.push( ~l1decision );
      }
      solver.cancelUntil(0);
      // tell system about new units!
      for( int i = 0 ; i < learntUnits.size(); ++ i ) {
	data.addUnitToProof( learntUnits[i] );
	data.enqueue( learntUnits[i] );
      }
      if( !data.ok() ) return true; // interrupt loop, if UNSAT has been found!
      l1learntUnit+=learntUnits.size();
      if( solver.propagate() != CRef_Undef ) { data.setFailed(); return true; } // UNSAT has been found - current state is level 0
      
      return true; 
    }
    
  }
  
  // first decision is not a failed literal
  return false;
}

void Probing::cleanSolver()
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
  
  if( config.pr_debug_out > 1 ) {
    cerr << "c formula before resetup: " << endl;
      for( int i = 0 ; i< solver.clauses.size(); ++ i ) {
      const CRef cr = solver.clauses[i];
      const Clause& c = ca[cr];
      if( c.can_be_deleted() ) continue;
      cerr << "[" << cr << "] : " << c << endl;
    }
  }
}

void Probing::reSetupSolver()
{

  if( config.pr_debug_out > 1 ) {
    cerr << "c formula before resetup: " << endl;
      for( int i = 0 ; i< solver.clauses.size(); ++ i ) {
      const CRef cr = solver.clauses[i];
      const Clause& c = ca[cr];
      if( c.can_be_deleted() ) continue;
      cerr << "[" << cr << "] : " << c << endl;
    }
  }

  assert( solver.decisionLevel() == 0 && "solver can be re-setup only at level 0!" );
    // check whether reasons of top level literals are marked as deleted. in this case, set reason to CRef_Undef!
    if( solver.trail_lim.size() > 0 )
      for( int i = 0 ; i < solver.trail_lim[0]; ++ i )
        if( solver.reason( var(solver.trail[i]) ) != CRef_Undef )
          if( ca[ solver.reason( var(solver.trail[i]) ) ].can_be_deleted() )
            solver.vardata[ var(solver.trail[i]) ].reason = CRef_Undef;

    // give back into solver
    for( int p = 0 ; p < 2; ++ p ) {
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
		  if( config.pr_debug_out > 1 ) cerr << "c resetup clause [" << i << "]("<< cr <<")" << c << endl;
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
		    if( data.enqueue(c[0]) == l_False ) { if( config.pr_debug_out>2 ) cerr  << "enqueing " << c[0] << " failed." << endl; return; }
		    else { 
		      if( config.pr_debug_out>2 ) cerr << "enqueued " << c[0] << " successfully" << endl;
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

    
   if( false ) {
      cerr << "c trail before probing: ";
      for( int i = 0 ; i< solver.trail.size(); ++i ) 
      {
	cerr << solver.trail[i] << " " ;
      }
      cerr << endl;
      
      if( true ) {
      cerr << "formula: " << endl;
      for( int i = 0 ; i < data.getClauses().size(); ++ i )
	if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getClauses()[i] ] << endl;
      for( int i = 0 ; i < data.getLEarnts().size(); ++ i )
	if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getLEarnts()[i] ] << endl;    
      }
      
      cerr << "c watch lists: " << endl;
      for (int v = 0; v < solver.nVars(); v++)
	  for (int s = 0; s < 2; s++) {
	    const Lit l = mkLit(v, s == 0 ? false : true );
	    cerr << "c watch for " << l << endl;
	    for( int i = 0; i < solver.watches[ l ].size(); ++ i ) {
	      cerr << ca[solver.watches[l][i].cref()] << endl;
	    }
	  }
    }
}



void Probing::printStatistics( ostream& stream )
{
  stream << "c [STAT] PROBING(1) " 
  << processTime << " s, "
  <<  l1implied << " implied "
  <<  l1failed << " l1Fail, "
  <<  l1learntUnit << " l1Units "
  <<  l1ee << " l1EE "
  <<  l2implied << " l2implied "
  <<  l2failed << " l2Fail "
  <<  l2ee  << " l2EE "
  <<  lhbr_news << " pr-lhbrs, "
  <<  probeLHBRs << " vivi-lhbrs "
  << endl;   
  
  stream << "c [STAT] PROBING(2) " 
  << probes << " probes "
  << probeCandidates << " probeCands "
  << l2probes << " l2probes "
  << totalL2cand << " l2cands "
  << probeChecks << " checks "
  << endl;   
  
  stream << "c [STAT] VIVI " 
  << viviTime << "  s, "
  <<  viviLits << " lits, "
  <<  viviCls << " cls, "
  << viviCands << " candidates, "
  << viviChecks << " checks, "
  << viviSize << " viviSize"
  << endl;   
}

void Probing::sortClauses()
{
  uint32_t clausesSize = solver.clauses.size();
  for (int i = 0; i < clausesSize; ++i)
  {
    Clause& c = ca[solver.clauses[i]];
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

  clausesSize = solver.learnts.size();
  for (int i = 0; i < clausesSize; ++i)
  {
    Clause& c = ca[solver.learnts[i]];
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
  
  if( config.pr_debug_out > 1 ) {
    cerr << "c formula after sort: " << endl;
      for( int i = 0 ; i< solver.clauses.size(); ++ i ) {
      const CRef cr = solver.clauses[i];
      const Clause& c = ca[cr];
      if( c.can_be_deleted() ) continue;
      cerr << "[" << cr << "] : " << c << endl;
    }
  }
}

void Probing::probing()
{
  
  // resize data structures
  prPositive.growTo( data.nVars() );
  
  
  CRef thisConflict = CRef_Undef;
  
  
  BIG big;
  big.create(ca,data.nVars(),data.getClauses(),data.getLEarnts()); // lets have the full big
  
  big.fillSorted( variableHeap, data, config.pr_rootsOnly );
  // if there are no root variables (or lits implied by roots), consider all variables!
  if( variableHeap.size() == 0 ) big.fillSorted( variableHeap, data, false, true );
  probeCandidates += variableHeap.size();
  // cerr << "sort literals in probing queue according to some heuristic (BIG roots first, activity, ... )" << endl;
  
  // probe for each variable 
  Lit repeatLit = lit_Undef;
  
  bool globalModify = modifiedFormula;
  do {
    modifiedFormula = false;
    for( int index = 0;  index < variableHeap.size() && !data.isInterupted()  && (probeLimit > probeChecks || data.unlimited()) && data.ok(); ++ index )
    {
      // repeat variable, if demanded - otherwise take next from heap!
      Var v = var(repeatLit);
      if( repeatLit == lit_Undef ) {
	v = variableHeap[index];
      }
      repeatLit = lit_Undef;
      
      if( solver.value(v) != l_Undef ) continue; // no need to check assigned variable!

      // cerr << "c test variable " << v + 1 << endl;

      assert( solver.decisionLevel() == 0 && "probing only at level 0!");
      const Lit posLit = mkLit(v,false);
      solver.newDecisionLevel();
      solver.uncheckedEnqueue(posLit);
      probes++;
      probeChecks++;
      thisConflict = prPropagate();
      if( config.pr_debug_out > 1 ) cerr << "c conflict after propagate " << posLit << " present? " << (thisConflict != CRef_Undef) << " trail elements: " << solver.trail.size() << endl;
      if( thisConflict != CRef_Undef ) {
	l1failed++;
	if( !prAnalyze( thisConflict ) ) {
	  learntUnits.push( ~posLit );
	}
	solver.cancelUntil(0);
	// tell system about new units!
	data.addCommentToProof("unit clauses that have been learned on level 1 during probing");
	for( int i = 0 ; i < learntUnits.size(); ++ i ) { data.enqueue( learntUnits[i] ); data.addUnitToProof(learntUnits[i]); }
	if( !data.ok() ) break; // interrupt loop, if UNSAT has been found!
	l1learntUnit+=learntUnits.size();
	if( solver.propagate() != CRef_Undef ) { data.setFailed(); break; }
	continue;
      } else {
	totalL2cand += doubleLiterals.size();
	if( prDoubleLook(posLit) ) { 
	  if( config.pr_debug_out > 1 ) cerr << "c double lookahead returned with true -> repeat " << posLit << endl;
	    repeatLit = posLit; 
	    continue;
	} // something has been found, so that second polarity has not to be propagated
	else if( config.pr_debug_out > 1 ) cerr << "c double lookahead did not fail" << endl;
      }
      solver.varFlags.copyTo( prPositive );
      
      if( config.pr_debug_out > 0 ) {
	cerr << "c positive trail: " ;
	for( int i = 0 ; i < solver.trail.size(); ++ i ) cerr << " " << solver.trail[i];
	cerr << endl;
      }
      
      // other polarity
      solver.cancelUntil(0);
      
      assert( solver.decisionLevel() == 0 && "probing only at level 0!");
      const Lit negLit = mkLit(v,true);
      solver.newDecisionLevel();
      solver.uncheckedEnqueue(negLit);
      probes++;
      probeChecks++;
      thisConflict = prPropagate();
      if( config.pr_debug_out > 1 ) cerr << "c conflict after propagate " << negLit << " present? " << (thisConflict != CRef_Undef) << " trail elements: " << solver.trail.size() << endl;
      if( thisConflict != CRef_Undef ) {
	l1failed++;
	if( !prAnalyze( thisConflict ) ) {
	  learntUnits.push( ~negLit );
	}
	solver.cancelUntil(0);
	// tell system about new units!
	data.addCommentToProof("unit clauses that have been learned on level 1 during probing");
	for( int i = 0 ; i < learntUnits.size(); ++ i ) { data.enqueue( learntUnits[i] ); data.addUnitToProof( learntUnits[i] ); }
	l1learntUnit+=learntUnits.size();
	if( !data.ok() ) break; // interrupt loop, if UNSAT has been found!
	if( solver.propagate() != CRef_Undef ) { data.setFailed(); break; }
	continue;
      } else {
	totalL2cand += doubleLiterals.size();
	if( prDoubleLook(negLit) ) { 
	  if( config.pr_debug_out > 1 ) cerr << "c double lookahead returned with true -> repeat " << negLit << endl;
	    repeatLit = negLit; 
	    continue;
	} // something has been found, so that second polarity has not to be propagated
	else if( config.pr_debug_out > 1 ) cerr << "c double lookahead did not fail" << endl;
      }
      // could copy to prNegatie here, but we do not do this, but refer to the vector inside the solver instead
      if(!data.ok() ) break;

      assert( solver.decisionLevel() == 1 && "");
      
      if( config.pr_debug_out > 0 ) {
	cerr << "c negative trail: " ;
	for( int i = 0 ; i < solver.trail.size(); ++ i ) cerr << " " << solver.trail[i];
	cerr << endl;
      }
      
      if( data.outputsProof() ) printDRUPwarning(cerr,"necessary assignments and equivalences from Probing cannot be handled easily with DRAT");
      data.lits.clear();
      data.lits.push_back(negLit); // equivalent literals
      doubleLiterals.clear();	  // NOTE re-use for unit literals!
      // look for necessary literals, and equivalent literals (do not add literal itself)
      for( int i = solver.trail_lim[0] + 1; i < solver.trail.size(); ++ i )
      {
	// check whether same polarity in both trails, or different polarity and in both trails
	const Var tv = var( solver.trail[ i ] );
	if( config.pr_debug_out > 1 )cerr << "c compare variable (level 0) " << tv + 1 << ": pos = " << toInt(prPositive[tv].assigns) << " neg = " << toInt(solver.varFlags[tv].assigns) << endl;
	if( solver.varFlags[ tv ].assigns == prPositive[tv].assigns ) {
	  if( config.pr_debug_out > 1 )cerr << "c implied literal " << solver.trail[i] << endl;
	  doubleLiterals.push_back(solver.trail[ i ] );
	  l1implied ++;
	} else if( config.pr_EE ) {
	  if( solver.varFlags[ tv ].assigns == l_True && prPositive[tv].assigns == l_False ) {
	    if( config.pr_debug_out > 1 )cerr << "c equivalent literals " << negLit << " == " << solver.trail[i] << endl;
	    data.lits.push_back( solver.trail[ i ] ); // equivalent literals
	    l1ee++;
	    modifiedFormula = true;
	  } else if( solver.varFlags[ tv ].assigns == l_False && prPositive[tv].assigns == l_True ) {
	    if( config.pr_debug_out > 1 )cerr << "c equivalent literals " << negLit << " == " << solver.trail[i] << endl;
	    data.lits.push_back( solver.trail[ i ] ); // equivalent literals
	    l1ee++;
	    modifiedFormula = true;
	  }
	}
      }
      
      if( config.pr_debug_out > 1 ) {
      cerr << "c trail: " << solver.trail.size() << " trail_lim[0] " << solver.trail_lim[0] << " decisionLevel " << solver.decisionLevel() << endl;
      cerr << "c found implied literals " << doubleLiterals.size() << "  out of " << solver.trail.size() - solver.trail_lim[0] << endl;
      }
      
      solver.cancelUntil(0);
      // add all found implied literals!
      if( doubleLiterals.size() > 0 ) data.addCommentToProof("literals that have been implied during double look ahead");
      for( int i = 0 ; i < doubleLiterals.size(); ++i )
      {
	const Lit l = doubleLiterals[i];
	if( solver.value( l ) == l_False ) { data.setFailed(); break; }
	else if ( solver.value(l) == l_Undef ) {
	  solver.uncheckedEnqueue(l);
	  data.addUnitToProof( l ); // might not be DRAT immediately
	}
      }

      // propagate implied(necessary) literals inside solver
      if( solver.propagate() != CRef_Undef )
	data.setFailed();
      
      // tell coprocessor about equivalent literals
      if( data.lits.size() > 1 )
	data.addEquivalences( data.lits );
      
    }
    globalModify = globalModify || modifiedFormula;
  } while( config.pr_repeat && modifiedFormula );
  
  modifiedFormula = globalModify;
  
  // take care of clauses that have been added during probing!
  if( config.pr_keepLearnts != 2 ) {
    for( int i = 0 ; i < l2conflicts.size(); ++ i ) {
      Clause& c = ca[ l2conflicts[i] ];
      if( config.pr_keepLearnts == 0 ) {
	if( config.pr_debug_out > 0 ) cerr << "c delete clause [" << l2conflicts[i] << "] : " << c << endl;
	if( !c.can_be_deleted()) data.addToProof( ca[ l2conflicts[i] ], true ); // delete from proof
	c.set_delete(true);
	solver.detachClause( l2conflicts[i] ); // remove from solver structures -> to be not available for vivification
      } else {
	c.set_learnt(true);
	c.activity() = 0;
	data.getLEarnts().push( l2conflicts[i] );
      }
    }
  } else {
    for( int i = 0 ; i < l2conflicts.size(); ++ i )
      if( ca[l2conflicts[i]].size() > 1 )
	data.getClauses().push(l2conflicts[i]);
  }
  l2conflicts.clear();
  
  if( config.pr_keepImplied != 2 ) {
    for( int i = 0 ; i < l2implieds.size(); ++ i ) {
      Clause& c = ca[ l2implieds[i] ];
      if( config.pr_keepImplied == 0) {
	if( config.pr_debug_out > 0 ) cerr << "c delete clause [" << l2implieds[i] << "] : " << c << endl;
	if( !c.can_be_deleted()) data.addToProof( ca[ l2implieds[i] ] , true ); // delete from proof
	c.set_delete(true);
	solver.detachClause( l2implieds[i] ); // remove from solver structures -> to be not available for vivification
      } else {
	c.set_learnt(true);
	c.activity() = 0;
	data.getLEarnts().push( l2implieds[i] );
      }
    }
  } else {
    for( int i = 0 ; i < l2implieds.size(); ++ i )
      if( ca[l2implieds[i]].size() > 1 )
	data.getClauses().push(l2implieds[i]);
  }
  l2implieds.clear();
  
  // clean data structures
  solver.watches.cleanAll(); 
}



void Probing::clauseVivification()
{
  MethodTimer vTimer ( &viviTime );
  
  if( config.pr_debug_out ) {
    for( Var v = 0; v < data.nVars(); ++ v )
    {
      for( int p = 0 ; p < 2; ++ p ) 
      {
	const Lit l = mkLit(v, p==1);
	vec<Solver::Watcher>&  ws  = solver.watches[l];
	for ( int j = 0 ; j < ws.size(); ++ j){
		CRef     wcr        = ws[j].cref();
		const Clause& c = ca[wcr];
		if( c[0] != ~l && c[1] != ~l ) cerr << "wrong literals for clause [" << wcr << "] " << c << " are watched. Found in list for " << l << endl;
	    }
      }
    }
    
    cerr << "c formula before vivi: " << endl;
    for( int p = 0 ; p < 2; ++ p ) {
      const vec<CRef>& clList = (p == 0 ? solver.clauses : solver.learnts);
      for( int i = 0 ; i< clList.size(); ++ i ) {
	const CRef cr = clList[i];
	const Clause& c = ca[cr];
	
	if( c.can_be_deleted() )  cerr << "[" << i << "](ign)";
	else cerr << "c [" << i << "]";
	cerr << "(" << cr << ") : " << c << endl;
	if( c.can_be_deleted() ) continue;
	
	if( c.size() == 1 ) cerr << "there should not be unit clauses! [" << cr << "]" << c << endl;
	else {
	  for( int j = 0 ; j < 2; ++ j ) {
	    const Lit l = ~c[j];
	    vec<Solver::Watcher>&  ws  = solver.watches[l];
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
  }
  
  uint32_t maxSize = 0;
  if( (data.unlimited() || viviLimit > viviChecks) ) {
    if( config.pr_debug_out ) cerr << "c calculate maxSize based on " << data.getClauses().size() << " clauses" << endl;
    for( uint32_t i = 0 ; i< data.getClauses().size(); ++ i ) {
      const CRef ref = data.getClauses()[i];
      const Clause& clause = ca[ ref ];
      if( clause.can_be_deleted() ) continue;
      maxSize = clause.size() > maxSize ? clause.size() : maxSize;
    }
  }
  if( config.pr_debug_out ) cerr << "c calculated maxSize: " << maxSize << endl;
  
  maxSize = (maxSize * config.pr_viviPercent) / 100;
  maxSize = maxSize > 2 ? maxSize : 3;	// do not process binary clauses, because they are used for propagation
  viviSize = maxSize;
  
  if( config.pr_debug_out )cerr << "c final viviSize: " << viviSize << endl;
  
  for( uint32_t i = 0 ; i< data.getClauses().size() && (data.unlimited() || viviLimit > viviChecks)  && !data.isInterupted() ; ++ i ) {
    const CRef ref = data.getClauses()[i];
    Clause& clause = ca[ ref ];
    if( clause.can_be_deleted() ) continue;
    if( clause.size() < maxSize ) continue;
    
    assert (clause.size() > 2 && "clauses for vivification have to be larger than 2" );
    assert( solver.decisionLevel() == 0 && "asymmetric branching only at level 0!" );
    
    viviCands ++;
    if( config.pr_debug_out > 1 ) cerr << "c work on clause ("<< ref << ") " << clause << endl;
    bool hasAssigned = false;
    data.lits.clear();
    for( int j = 0 ; j < clause.size(); ++ j ) {
      data.lits.push_back( ~clause[j] );
      if( solver.value( data.lits[j]) != l_Undef ) { hasAssigned = true; break ; }
    }
    if( hasAssigned ) continue; // do not consider those clauses!
    
    if( data.randomized() ) {
        // shuffle!
	for( int j = 0; j + 1 < data.lits.size(); ++ j ) {
	  const unsigned tmp = rand() % data.lits.size() ;
	  const Lit tmpL = data.lits[j];
	  data.lits[j] =  data.lits[tmp];
	  data.lits[tmp] = tmpL;
	}
    } else {
      // TODO: find a nice heuristic here!! e.g. RWH!
    }
    
    // remove one literal, because otherwise this would fail always!
    unsigned subClauseLimit = data.lits.size(); // usually, nothing can be removed
    Lit removedLit = data.lits[ data.lits.size() - 1 ];
    data.lits.pop_back();
    
    // calculate for all propagated literals!
    viviChecks ++;
    
    // detach this clause, so that it cannot be used for unit propagation
    if( config.pr_debug_out > 2 ) cerr << "c available watches for " << clause[0] << " : " << solver.watches[ ~clause[0] ].size()
         << " and " << clause[1] << " : " << solver.watches[ ~clause[1] ].size() << endl;
    
    // take care of the size restriction
    if( config.pr_debug_out > 1 ) cerr << "c detach clause [" << ref << "] : " << ca[ref] << endl;
    solver.detachClause(ref, true);
    
    bool viviConflict = false;
    bool viviNextLit = false;
    solver.newDecisionLevel();
    for( int j = 0; j < data.lits.size(); ++ j ) {
      
      if( config.pr_debug_out > 1 ) {
      cerr << "c literals to work with (curr=" << j << "): ";
      for( int k = 0 ; k < data.lits.size(); ++ k ) 
	cerr << " " << data.lits[k] << " @" << toInt(solver.value(data.lits[k]));
      cerr << endl;
      cerr << "c current trail: ";
      for( int k = 0 ; k < solver.trail.size(); ++ k )
	cerr << " " << solver.trail[k];
      cerr << endl;
      }
      
      // check whether one of the other literals is already "broken"
      for( int k = j; k < data.lits.size(); ++ k ) {
	if( solver.value(data.lits[k]) == l_False ) {
	  if( config.pr_debug_out > 1 ) cerr << "c found failing literal " << data.lits[k] << endl;
	  data.lits[j] = data.lits[k];
	  subClauseLimit = j+1;
	  viviConflict = true;
	  break;
	} else if ( solver.value(data.lits[k]) == l_True ) {
	  if( config.pr_debug_out > 1 ) cerr << "c found satisfied literal " << data.lits[k] << " (" << k << ") " << endl;
	  data.lits[k] = data.lits[ data.lits.size() - 1 ];
	  if( j == k ) --j;
	  --k;
	  data.lits.pop_back();
	  subClauseLimit --;
	  if( config.pr_debug_out > 1 ) cerr << "c continue with lit(" << j << ") and " << data.lits.size() << " lits" << endl;
	  viviNextLit = true;
	  break; // TODO: performance could be improved by analysing literals from back to front! -> quadratic to linear?!
	}
      }
      if( viviConflict ) break; // found a subsuming sub clause -> stop
      else if ( viviNextLit ) continue; // found a tautologic literal -> continue with next literal!
      
      const Lit thisLit = data.lits[j];
      if( config.pr_debug_out > 1 ) cerr << "c enqueue " << thisLit << endl;
      solver.uncheckedEnqueue(thisLit);
      
      if( config.pr_debug_out > 1 ) {
	cerr << "c current trail (after enqueue): ";
	for( int k = 0 ; k < solver.trail.size(); ++ k )
	  cerr << " " << solver.trail[k];
	cerr << endl;
      }
      
      int trailDiff = solver.trail.size();
      CRef confl = solver.propagate(); // careful, can change and re-alloc clause data structures!
      trailDiff = solver.trail.size() - trailDiff;
      viviChecks += trailDiff; // calculate limit!
      
      if( confl != CRef_Undef ) {
	if( config.pr_debug_out > 1 ) {
	  cerr << "c found conflict [" << confl << "]" << ca[confl] << endl;
	  cerr << "c current trail (after propagate): ";
	  for( int k = 0 ; k < solver.trail.size(); ++ k )
	    cerr << " " << solver.trail[k];
	  cerr << endl;
	}
	// clauselits[0] AND ... AND data.lits[j] -> false => new sub clause!
	subClauseLimit = j+1;
	if( config.pr_debug_out > 1 )cerr << "c propagation resulted in conflict -> set lits set to " << j << endl;
	viviConflict = true;
	break;
      }
    } // stop such that there is nothing to be done with the clause any more!
    
    // jump back to clean trail
    solver.cancelUntil(0);
    
    Clause& sameClause = ca[ ref ]; // update the reference, because it could have changed in the mean time!
    if( subClauseLimit != sameClause.size() ) {
      // TODO: remove clause and data structures so that they meet the sub clause! 
      viviLits += sameClause.size() - subClauseLimit;
      viviCls ++;
      
      data.lits.resize(subClauseLimit);
      
      if( !viviConflict ) data.lits.push_back(removedLit);
      
      if( config.pr_debug_out > 1 ) {
      cerr << "c replace clause " << sameClause << " with ";
      for( int j = 0 ; j < data.lits.size(); ++ j ) 
	cerr << " " << ~data.lits[j];
      cerr << endl;
      }
      data.addCommentToProof("shrinked by vivification"); // delete clause that has been shrinked by vivification
      if( data.outputsProof() ) {
	for( int j = 0 ; j < data.lits.size(); ++ j ) data.lits[j] = ~data.lits[j];
	data.addToProof( data.lits ); // delete clause that has been shrinked by vivification
	for( int j = 0 ; j < data.lits.size(); ++ j ) data.lits[j] = ~data.lits[j];
      }
      data.addToProof( sameClause, true ); // delete clause that has been shrinked by vivification
      
      data.ma.nextStep();
      for( int j = 0 ; j < data.lits.size(); ++ j )
	data.ma.setCurrentStep( toInt( ~data.lits[j] ) );
      
      int keptLits = 0;
      for( int j = 0 ; j < sameClause.size(); ++ j ) {
	// if literal is not there any more, remove clause index from structure
	if( !data.ma.isCurrentStep( toInt(sameClause[j]) ) ) {
	  data.removeClauseFrom(ref, sameClause[j]) ;
	} else {
	  // otherwise, keep literal inside clause
	  sameClause[keptLits++] = sameClause[j]; 
	}
      }
      sameClause.shrink( sameClause.size() - keptLits );
      sameClause.sort();
      modifiedFormula = true;
      if( config.pr_debug_out > 1 ) cerr << "c new clause: " << sameClause << endl;
    }
    
    // detach this clause, so that it cannot be used for unit propagation
    if( sameClause.size() == 0 ) {
      data.setFailed();
    } else if ( sameClause.size() == 1 ) {
      data.enqueue( sameClause[0] );
    } else solver.attachClause(ref);

    if( !data.ok() ) break;
  } // end for clause in data.getClauses()
 
    if( config.pr_debug_out > 0 ) {
      cerr << "c formula after vivi: " << endl;
      for( int i = 0 ; i< solver.clauses.size(); ++ i ) {
	const CRef cr = solver.clauses[i];
	const Clause& c = ca[cr];
	if( c.can_be_deleted() ) continue;
	cerr << "[" << cr << "] : " << c << endl;
      }
    }
}

void Probing::destroy()
{
  vector<Var>().swap( variableHeap );
  prPositive.clear(true);
  prL2Positive.clear(true);
  learntUnits.clear(true);
  vector<Lit>().swap( doubleLiterals );
  vector<CRef>().swap( l2conflicts );
  vector<CRef> ().swap(l2implieds );
}

