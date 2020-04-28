/**************************************************************************[SolverCommunication.cc]
Copyright (c) 2012, All rights reserved, Norbert Manthey

This file implements the methods that are necessary for communicating among solver threads based
on the Communicator implementation.

**************************************************************************************************/

#ifndef Minisat_SolverCommunication_h
#define Minisat_SolverCommunication_h

#include <math.h>

#include "mtl/Sort.h"
// #include "core/Solver.h"
#include "utils/System.h"

// to avoid cyclic dependencies
#include "core/Communication.h"

// for test_cancel()
#include <pthread.h>

// pick one to enable/disable some debug messages
#define DBG(x)
// #define DBG(x) x

namespace Minisat {

inline
void Solver::setCommunication( Communicator* comm )
{
  assert( communication == 0 && "Will not overwrite already set communication interface" );
  communication = comm;
  initLimits();  // set communication limits
  // copy values from communicator object
  sendSize = communication->sendSize;
  sendLbd = communication->sendLbd;
  sendMaxSize = communication->sendMaxSize;
  sendMaxLbd = communication->sendMaxLbd;
  sizeChange = communication->sizeChange;
  lbdChange = communication->lbdChange;
  sendRatio = communication->sendRatio;
}

inline 
void Solver::resetLastSolve()
{
  clearInterrupt();
  cancelUntil(0);
  budgetOff();
}


/** add a learned clause to the solver
 */
inline
bool Solver::addLearnedClause(vec<Lit>& ps, bool bump)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
        uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, true);
	if( bump ) ca[cr].activity() += cla_inc; // same as in claBumpActivity
        learnts.push(cr);
        attachClause(cr);
    }
    return true;
}

inline
int Solver::updateSleep(vec< Lit >* toSend, bool multiUnits)
{
  if( communication == 0 ) return 0;	// no communication -> do nothing!
  
  // nothing to send, do only receive every reveiceEvery tries!
  if( toSend == 0 && currentTries++ < receiveEvery) return 0;
  currentTries = 0;
  
  // check current state, e.g. wait for master to do something!
  if( !communication->isWorking() )
  {
    if( communication->isAborted() ) {
      interrupt();
      if (verbosity > 0)
        cerr << "c [THREAD] " << communication->getID()
             << " aborted current search due to flag by master" << endl;
      return -1;
    }

    /* not working -> master interrupted thread
     * tell master that we reached this state
     * sleep until master changed something
     * wake up afterwards
     */
    communication->ownLock->lock();
    communication->setState(Communicator::waiting);
    // not unlock (avoid same error as in master!)

    communication->awakeMaster();

    cerr << "c [THREAD] " << communication->getID() << " wait for master to do something (sleep)" << endl;
    // wait until master changes the state again to working!

    while( ! communication->isWorking() ){
      if( communication->isDoReceive() ) {
        // goto level 0
        if( decisionLevel() != 0 ) cancelUntil(0);
        // add unit clauses from master as clauses of the formula!!
        communication->data->receiveUnits( receiveClause );
        for( int i = 0 ; i < receiveClause.size(); ++ i ) {
          if( !addClause (receiveClause[i]) ) {	// this methods adds the units to the proof as well!
            assert( false && "case that send unit clause makes the whole formula unsatisfiable is not handled - can this happen?");
            break;                                  // Add a unit clause to the solver.
          }
        }
        // sleep again, so that master can make sure everybody saw the units!
        communication->setState(Communicator::finishedReceiving);
      }
      if( communication->isAborted() ) break;
      communication->ownLock->sleep();
    }
    communication->ownLock->unlock();
    if( communication->isAborted() ) {
      interrupt();
      return -1;
    }
  }

  // if there should not be communication
  if( ! communication->getDoSend() && ! communication->getDoReceive() ) return 0;

  if( communication->getDoSend() && toSend != 0 )      // send
  {
    // clause: 
    int levels [ toSend->size() ];

    // calculated size of the send clause    
    int s = 0;
    if( communication->variableProtection() ) {  // check whether there are protected literals inside the clause!
      for( int i = 0 ; i < toSend->size(); ++ i )
        s = communication->isProtected( (*toSend)[i] ) ? s : s+1;
    } else s = toSend->size();
      
    // filter sending:
    if( toSend->size() > currentSendSizeLimit ) {
      updateDynamicLimits ( true ); // update failed limits!
      communication->nrRejectSendSizeCls++;
      return 0; // TODO: parameter, adaptive?
    }

    if( s > 0 ) {
      // calculate LBD value
#if 0	// if variables should be protected
      if( communication->variableProtection() ) {
        int j = 0;
	for( int i = 0 ; i < toSend->size(); ++ i )
	  if( !communication->isProtected( (*toSend)[i] ) )
            levels[j++] = level( var((*toSend)[i]));  // just consider the variable that are not protected!
      } else {
        for( int i = 0 ; i < toSend->size(); ++ i )
          levels[i] = level( var((*toSend)[i]));
      }
      // insertionsort
      for( int i = 1; i < s; ++i ) {
        unsigned p = i; int l = levels[i];
        for( int j = i+1; j < s; ++ j ) {
          if( levels[j] > l ) {
            p = j; l = levels[j];
          }
        }
        int ltmp = levels[i]; levels[i] = levels[p]; levels[p] = ltmp;
      }
      int lbd = 1;
      for( int i = 1; i < s; ++ i ) {
        lbd = ( levels[i-1] == levels[i] ) ? lbd : lbd + 1;
      }
#endif 
      int lbd = computeLBD( *toSend );
      
      if( lbd > currentSendLbdLimit ) {
	updateDynamicLimits ( true ); // update failed limits!
	communication->nrRejectSendLbdCls++;
	return 0; //TODO: parameter (adaptive?)
      }
    }
    communication->addClause(*toSend);
    updateDynamicLimits(false); // a clause could be send
    communication->nrSendCls++;

  } else if( communication->getDoReceive() ) {        // receive (only at level 0)

    // TODO: add parameter that forces to restart!
    // if( communication->

    // not at level 0? nothing to do
    if( decisionLevel() != 0 ) return 0; // receive clauses only at level 0!

    receiveClauses.clear();
    communication->receiveClauses( ca, receiveClauses );
    // if( receiveClauses.size()  > 5 ) cerr << "c [THREAD] " << communication->getID() << " received " << receiveClauses.size() << " clauses." << endl;
    succesfullySend += receiveClauses.size();
    for( unsigned i = 0 ; i < receiveClauses.size(); ++ i ) {
      Clause& c = ca[ receiveClauses[i] ]; // take the clause and propagate / enqueue it
      
      if (c.size() < 2) {
	if( c.size() == 0 ) {
	  cerr << "c empty clause has been shared!" << endl;
	  ok = false; return 1; 
	}
	// has to be unit clause!
	addUnitToProof(c[0]); // add the clause to the proof
	if( value( c[0] ) == l_Undef ) uncheckedEnqueue(c[0]); 
	else if(value( c[0] ) == l_False ) {
	  ok = false; return 1; 
	}
	c.mark();
        ok = (propagate() == CRef_Undef);
	if( !ok ) { // adding this clause failed?
          cerr << "c adding received clause failed" << endl;
          return 1; 
	}
      } else {
	for( int j = 0 ; j < c.size(); ++ j ) { // propagate inside the clause!
          if( var(c[j]) > nVars() ) {
	    cerr << "c shared variable " << var( c[j] ) << "[" << j << "] is greater than " << nVars() << endl;
	   assert( false && "received variables have to be smaller than maximum!" );
	  }
	  if( value( c[j] ) == l_True ) { c.mark(1); break; } // this clause is already satisfied -> remove it! (we are on level 0!)
	  else if ( value( c[j] ) == l_False ) { c[j] = c[ c.size() -1 ]; c.shrink(1); } // this literal is mapped to false -> remove it!
	}
	// TODO: here could be more filters for received clauses to be rejected (e.g. PSM?!)
	if( !c.mark() ) {
	  communication->nrReceivedCls ++;
	  if( c.size() == 0 ) { ok = false; return 1; }
	  else if ( c.size() == 1 ) {
	    addUnitToProof(c[0]); // add the clause to the proof
	    if( value( c[0] ) == l_Undef ) uncheckedEnqueue(c[0]);
	    else if(value( c[0] ) == l_False ) {
	      ok = false; return 1; 
	    }
	    c.mark();
	    ok = (propagate() == CRef_Undef);
	    if( !ok ) return 1; 
	  } else { // attach the clause, if its not a unit clause!
	    addToProof( ca[receiveClauses[i]] ); // the shared clause stays in the solver, hence add this clause to the proof!
	    learnts.push(receiveClauses[i]);
	    if( communication->doBumpClauseActivity )
	      ca[receiveClauses[i]].activity() += cla_inc; // increase activity of clause
	    attachClause(receiveClauses[i]);
	  }
	}
      }
    }
  }
  // everything worked nicely
  return 0;
}

inline
void Solver::updateDynamicLimits( bool failed, bool sizeOnly )
{
  if( ! failed ) succesfullySend ++;
  
  bool fulfillRatio = (double) conflicts * sendRatio < succesfullySend; // send more than ratio clauses?
  
  // fail -> increase geometrically, success, decrease geometrically!
  currentSendSizeLimit = (failed ? currentSendSizeLimit * (1.0 + sizeChange) : currentSendSizeLimit - currentSendSizeLimit * sizeChange );
  // check bound
  currentSendSizeLimit = currentSendSizeLimit < sendSize    ? sendSize    : currentSendSizeLimit;
  currentSendSizeLimit = currentSendSizeLimit > sendMaxSize ? sendMaxSize : currentSendSizeLimit;
  
  if( fulfillRatio ) initLimits(); // we have hit the ratio, tigthen limits again!
  
//   if( sizeOnly ) {
//     currentSendLbdLimit = currentSendLbdLimit < sendLbd    ? sendLbd    : currentSendLbdLimit;  
//     currentSendLbdLimit = currentSendLbdLimit > sendMaxLbd ? sendMaxLbd : currentSendLbdLimit;  
//     return;
//   }
  
  // fail -> increase geometrically, success, decrease geometrically!
  currentSendLbdLimit = (failed ? currentSendLbdLimit * (1.0 + lbdChange) : currentSendLbdLimit - currentSendLbdLimit * lbdChange );
  // check bound
  currentSendLbdLimit = currentSendLbdLimit < sendLbd    ? sendLbd    : currentSendLbdLimit;  
  currentSendLbdLimit = currentSendLbdLimit > sendMaxLbd ? sendMaxLbd : currentSendLbdLimit;  
  
  return;
}

inline
void Solver::initVariableProtection() {
  if( communication != 0 )
      communication->initProtect( assumptions, nVars() );
}

inline
void Solver::initLimits() {
  currentSendSizeLimit = communication->sendSize;
  currentSendLbdLimit  = communication->sendLbd;
}

}

#endif