/**************************************************************************************[librissc.cc]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Coprocessor.h"
using namespace Minisat;

/** struct that stores the necessary data for a preprocessor */
struct libriss {
  Minisat::vec<Minisat::Lit> currentClause;
  Minisat::vec<Minisat::Lit> assumptions;
  Minisat::CoreConfig* solverconfig;
  Minisat::Solver* solver;
  Coprocessor::CP3Config* cp3config;
  Minisat::lbool lastResult;
  libriss () : lastResult(l_Undef) {} // default constructor to ensure everything is set to 0
};

// #pragma GCC visibility push(hidden)
// #pragma GCC visibility push(default)
// #pragma GCC visibility pop // now we should have default!

//#pragma GCC visibility push(default)

extern "C" {
  

/** initialize a solver instance, and return a pointer to the maintain structure 
* @param presetConfig name of a configuration that should be used
*/
void* 
riss_init(const char* presetConfig)
{
    libriss* riss = new libriss;
    riss->solverconfig = new Minisat::CoreConfig(presetConfig == 0 ? "" : presetConfig);
    riss->cp3config = new Coprocessor::CP3Config(presetConfig == 0 ? "" : presetConfig);
    riss->solver = new Minisat::Solver (*(riss->solverconfig));
    riss->solver->setPreprocessor( riss->cp3config );
    return riss;
}
  
/** free the resources of the solver, set the pointer to 0 afterwards */
void 
riss_destroy(void*& riss)
{
  libriss* solver = (libriss*) riss;
  delete solver->solver;
  delete solver->cp3config;
  delete solver->solverconfig;
  delete solver;
  riss = 0;
}
  
/** add a literal to the solver, if lit == 0, end the clause and actually add it */
int riss_add (void* riss, const int& lit) 
{
  libriss* solver = (libriss*) riss;
  bool ret = false;
  if( lit != 0 ) solver->currentClause.push( lit > 0 ? mkLit( lit-1, false ) : mkLit( -lit-1, true ) );
  else { // add the current clause, and clear the vector
    // reserve variables in the solver
    for( int i = 0 ; i < solver->currentClause.size(); ++i ) {
      const Lit l2 = solver->currentClause[i];
      const Var v = var(l2);
      while ( solver->solver->nVars() <= v ) solver->solver->newVar();
    }
    ret = solver->solver->addClause_( solver->currentClause );
    solver->currentClause.clear();
  }
  return ret ? 1 : 0;
}

/** add the given literal to the assumptions for the next solver call */
void 
riss_assume (void* riss, const int& lit)
{
  libriss* solver = (libriss*) riss;
  solver->assumptions.push( lit > 0 ? mkLit( lit-1, false ) : mkLit( -lit-1, true )  );
}
  
/** solve the formula that is currently present (riss_add) under the specified assumptions since the last call
 * Note: clears the assumptions after the solver run finished
 * @param nOfConflicts number of conflicts that are allowed for this SAT solver run (-1 = infinite)
 * @return status of the SAT call: 10 = satisfiable, 20 = unsatisfiable, 0 = not finished within number of conflicts
 */
int 
riss_sat (void* riss, const int& nOfConflicts)
{
  libriss* solver = (libriss*) riss;
  if( nOfConflicts == -1 ) solver->solver->budgetOff();
  else solver->solver->setConfBudget( nOfConflicts );
  
  // make sure the assumptions fit into the memory of the solver!
  for( int i = 0 ; i < solver->assumptions.size(); ++ i ) {
    while( var(solver->assumptions[i]) >= solver->solver->nVars() ) solver->solver->newVar();
  }
  
  lbool ret = solver->solver->solveLimited( solver->assumptions );
  solver->assumptions.clear();		// clear assumptions after the solver call finished
  solver->lastResult = ret;		// store last solver result
  return ret == l_False ? 20 : ( ret == l_Undef ? 0 : 10); // return UNSAT, UNKNOWN or SAT, depending on solver result
}

/** return the polarity of a variable in the model of the last solver run (if the result was sat) */
int 
riss_deref (const void* riss, const int& lit) 
{
  const Var v = lit > 0 ? lit - 1 : -lit - 1;
  libriss* solver = (libriss*) riss;
  assert( solver->lastResult == l_True && "can deref literals only after SAT result" );
  lbool vValue = l_Undef;
  if( v < solver->solver->model.size() ) vValue = solver->solver->model[v];
  return ( lit < 0 ) ? (vValue == l_False ? 1 : (vValue == l_True ? -1 : 0) ) : (vValue == l_False ? -1 : (vValue == l_True ? 1 : 0) );
}

  
}

// #pragma GCC visibility pop

//#pragma GCC visibility pop