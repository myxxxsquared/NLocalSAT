/**************************************************************************************[Entailed.h]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef ENTAILED_HH
#define ENTAILED_HH

#include "core/Solver.h"
#include "coprocessor-src/Technique.h"
#include "coprocessor-src/CoprocessorTypes.h"

using namespace Minisat;

namespace Coprocessor {

/** this class is used for checking whether clauses are entailed by the remaining formula cheaply
 *  (so far, check whether resolving two other clauses produces this clause)
 */
class EntailedRedundant : public Technique  {
    
  CoprocessorData& data;
  
  double processTime;
  int subsumed;
  int removedClauses;
  int extraSubs;
  
public:
  EntailedRedundant( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data );

  void reset();
  
  /** check whether a clause is a resolvent of two other clauses in the formula, if yes - remove it
  * @return true, if something has been altered
  */
  bool process();
    
  void printStatistics(ostream& stream);

  void giveMoreSteps();
  
  void destroy();
};

}

#endif