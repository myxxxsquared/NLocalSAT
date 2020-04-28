/****************************************************************************************[TwoSAT.h]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef TWOSAT_HH
#define TWOSAT_HH

#include "core/Solver.h"

#include "coprocessor-src/CoprocessorTypes.h"

#include "coprocessor-src/Technique.h"

#include <vector>
#include <deque>

using namespace Minisat;
using namespace std;

namespace Coprocessor {

 /** perform 2-SAT checking */
class TwoSatSolver : public Technique
{
  CoprocessorData& data;
  BIG big;
  
  vector<char> tempVal, permVal;
  deque<Lit> unitQueue, tmpUnitQueue;
  int lastSeenIndex;
  
  double solveTime;		// number of seconds for solving
  int touchedLiterals;		// number of literals that have been touched during search
  int permLiterals;		// number of permanently fixed literals
  int calls;			// number of calls to twosat solver
  
  public:
    TwoSatSolver(CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data);
    ~TwoSatSolver();
    
  bool solve();
  
  char getPolarity( const Var v ) const;
  
  bool isSat( const Lit& l ) const;
  
  bool isPermanent( const Var v ) const;
  
  /** This method should be used to print the statistics of the technique that inherits from this class
  */
  void printStatistics( ostream& stream );
  
  void destroy();
  
  void giveMoreSteps();
  
protected:
  
  bool unitPropagate();
  
  bool tmpUnitPropagate(  );
  
  bool hasDecisionVariable();

  Lit getDecisionVariable();
};

};

#endif