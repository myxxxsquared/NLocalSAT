/******************************************************************************************[rate.h]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef RATE_HH
#define RATE_HH

#include "core/Solver.h"
#include "coprocessor-src/Technique.h"
#include "coprocessor-src/CoprocessorTypes.h"
#include "coprocessor-src/Propagation.h"

using namespace Minisat;

namespace Coprocessor {

/** this class is used for blocked clause elimination procedure
 */
class RATElimination : public Technique  {
    
  CoprocessorData& data;
  Solver& solver;
  Coprocessor::Propagation& propagation;
  
  /// compare two literals
  struct LitOrderRATEHeapLt { // sort according to number of occurrences of complement!
        CoprocessorData & data; // data to use for sorting
	bool useComplements; // sort according to occurrences of complement, or actual literal
        bool operator () (int& x, int& y) const {
	  if( useComplements ) return data[ ~toLit(x)] > data[ ~toLit(y) ]; 
	  else return data[ toLit(x)] > data[ toLit(y) ]; 
        }
        LitOrderRATEHeapLt(CoprocessorData & _data, bool _useComplements) : data(_data), useComplements(_useComplements) {}
  };
  
  // attributes
  int64_t rateSteps;
  int rateCandidates; // number of clauses that have been checked for cle
  int remRAT, remAT, remHRAT, remBCE; // how many clauses 
  Clock rateTime; // clocks for the two methods
  
public:
  RATElimination( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data,  Solver& _solver, Coprocessor::Propagation& _propagation  );

  void reset();
  
  /** applies (hidden) resolution asymmetric tautology elimination algorithm
  * @return true, if something has been altered
  */
  bool process();
    
  void printStatistics(ostream& stream);

  void giveMoreSteps();
  
  void destroy();
  
protected:

  /** resolve clause D, ~l \in D, with existing literals in resolvent on literal l */
  bool resolveUnsortedStamped( const Lit l, const Clause& d, MarkArray& ma, vector<Lit>& resolvent );

  /** add all clauses to solver object -- code taken from @see Preprocessor::reSetupSolver, but without deleting clauses */
  void reSetupSolver();
  
  /** remove all clauses from the watch lists inside the solver */
  void cleanSolver();
};

}

#endif