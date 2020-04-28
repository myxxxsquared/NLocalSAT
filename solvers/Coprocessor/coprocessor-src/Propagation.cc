/**********************************************************************************[Propagation.cc]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Propagation.h"

using namespace Coprocessor;

static int upLevel = 1;

Propagation::Propagation( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller )
: Technique( _config, _ca, _controller )
, lastPropagatedLiteral( 0 )
, removedClauses(0)
, removedLiterals(0)
, processTime(0)
{
}

void Propagation::reset(CoprocessorData& data)
{
  lastPropagatedLiteral = 0;
  data.getSolver()->qhead = 0;
}


lbool Propagation::process(CoprocessorData& data, bool sort, Heap<VarOrderBVEHeapLt> * heap, const Var ignore)
{
  modifiedFormula = false;
  // not for UP! // if( !performSimplification() ) return l_Undef; // do not execute simplification?
  processTime = cpuTime() - processTime;
  if( !data.ok() ) return l_False;
  Solver* solver = data.getSolver();
  // propagate all literals that are on the trail but have not been propagated
  if (config.up_debug_out > 0) cerr << "c call propagate. already propagated: " << lastPropagatedLiteral << ", total to proapgate: " << solver->trail.size() << endl;
  for( ; lastPropagatedLiteral < solver->trail.size(); lastPropagatedLiteral ++ )
  {
    const Lit l = solver->trail[lastPropagatedLiteral];
    if (config.up_debug_out > 0) cerr << "c UP propagating " << l << endl;
    data.log.log(upLevel,"propagate literal",l);
    // remove positives
    vector<CRef> & positive = data.list(l);
    for( int i = 0 ; i < positive.size(); ++i )
    {

      Clause & satisfied = ca[positive[i]];
      if (ca[ positive[i] ].can_be_deleted()) // only track yet-non-deleted clauses
          continue; // could remove from list, but list is cleared any ways!
      else if( ca[ positive[i] ].size() > 1 ) {  // do not remove the unit clause!
	data.addCommentToProof("removed by positive UP",true );
	data.addToProof( ca[ positive[i] ], true ); // remove this clause, if this has not been done before
      }
      if( config.up_debug_out > 0 ) cerr << "c UP remove " << ca[ positive[i] ] << endl;
      ++removedClauses; // = ca[ positive[i] ].can_be_deleted() ? removedClauses : removedClauses + 1;
      ca[ positive[i] ].set_delete(true);
      modifiedFormula = true;
      data.removedClause( positive[i], heap, ignore);
      // remove clauses from structures?
    }
    vector<CRef>().swap(positive); // free physical space of positive
    
    const Lit nl = ~l;
    int count = 0;
    vector<CRef> & negative = data.list(nl);

    for( int i = 0 ; i < negative.size(); ++i )
    {
      Clause& c = ca[ negative[i] ];
      //what if c can be deleted? -> continue
      if (c.can_be_deleted())  continue;
      // sorted propagation, no!
      
        for ( int j = 0; j < c.size(); ++ j ) {
          if ( c[j] == nl ) 
          { 
	    if( config.up_debug_out > 0 ) cerr << "c UP remove " << nl << " from " << c << endl;
	    const Lit remLit = c[j];
	    if (!sort) c.removePositionUnsorted(j);
            else c.removePositionSorted(j);
	    
	    if( c.size() > 1 ) { // keep unit clauses on the proof!
	      data.addCommentToProof("removed literal by negative UP" );
	      data.addToProof(c);         // tell proof about modified clause
	      data.addToProof(c,true,remLit); // for DRUP store also the old clause, which can be removed now
	    }
	    
	    modifiedFormula = true;
	    count ++;
	    break;
	  }
	}
	      // tell subsumption / strengthening about this modified clause
      data.addSubStrengthClause(negative[i]);

      // proof and extra information
      if( c.size() > 1 ) {
	assert(!c.can_be_deleted() && "clause should not be deleted already" );
      }
      c.updateExtraInformation( data.variableExtraInfo(var(nl)) );
      
      // unit propagation
      if ( c.size() == 0 ) 
      {
        data.setFailed();   // set state to false
        //-> this stops just the inner loop!
        //break;              // abort unit propagation
        if (config.up_debug_out > 0) cerr << "c UNSAT by UP" << endl;
        processTime = cpuTime() - processTime;
        return l_False;
      } else if( c.size() == 1 ) {
         if( solver->value( c[0] ) == l_Undef && config.up_debug_out > 0 )  cerr << "c UP enqueue " << c[0] << " with previous value "  << (solver->value( c[0] ) == l_Undef ? "undef" : (solver->value( c[0] ) == l_False ? "unsat" : " sat ") ) << endl;
	 if( solver->value( c[0] ) == l_Undef ) solver->uncheckedEnqueue(c[0]);
	 else if( solver->value( c[0] ) == l_False ) data.setFailed();
      }
    }
    // update formula data!
    vector<CRef>().swap(negative); // free physical scace of negative
    data.removedLiteral(nl, count, heap, ignore);
    removedLiterals += count;
  }

  solver->qhead = lastPropagatedLiteral;
  
  if( !modifiedFormula ) unsuccessfulSimplification(); // this call did not change anything
  processTime = cpuTime() - processTime;
  return data.ok() ? l_Undef : l_False;
}

void Propagation::initClause( const CRef cr ) {}

void Propagation::printStatistics(ostream& stream)
{
  stream << "c [STAT] UP " << processTime << " s, " << lastPropagatedLiteral << " units, " << removedClauses << " cls, "
			    << removedLiterals << " lits" << endl;
}
