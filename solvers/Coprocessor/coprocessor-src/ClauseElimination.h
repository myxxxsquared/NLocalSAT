/*****************************************************************************[ClauseElimination.h]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef CLAUSEELIMINATION_HH
#define CLAUSEELIMINATION_HH

#include "core/Solver.h"

#include "coprocessor-src/CoprocessorTypes.h"

#include "coprocessor-src/Technique.h"
#include "coprocessor-src/Propagation.h"

#include <vector>

using namespace Minisat;
using namespace std;

namespace Coprocessor {

/** This class implement subsumption and strengthening, and related techniques
 */
class ClauseElimination : public Technique {
  
  Propagation& propagation;            /// object that takes care of unit propagation
  
  vector<CRef> clause_processing_queue;
  
  int steps;		// performed clause comparisons (loading a clause)
  double processTime;  // required time
  int removedClauses;  // number of removed clauses
  int removedBceClauses; // number of clauses that have been removed without changing equivalence
  unsigned removedNonEEClauses; // number of clauses that have been removed without preserving equivalence
  unsigned cceSize;		 // clause size for which cce is applied
  unsigned candidates;		 // number of candidates for which cce was tested
  
public:
  
  class WorkData {
  public:
    vector<Lit> cla;       // literals that have been added by cla
    MarkArray array;       // literals that have been marked by ala or cla
    MarkArray helpArray;   // literals that will be inside CLA(F,C) per step
    vector<Lit> toProcess; // literals that still need to be processed
    vector<Lit> toUndo;    // literals that have to be out to the undo information, if a cla clause is removed by ATE or ABCE
    int nextAla;           // position from which ala needs to be continued

    int steps;
    int removedClauses;
    int removedBceClauses;
    unsigned removedNonEEClauses;  // number of clauses that have been removed without preserving equivalence
    
    WorkData(int vars) : nextAla(0), steps(0), removedClauses(0), removedBceClauses(0), removedNonEEClauses(0) { array.create(2*vars); helpArray.create(2*vars);}
    ~WorkData() {array.destroy();helpArray.destroy();}
    void reset () { cla.clear(); array.nextStep(); toProcess.clear(); toUndo.clear(); nextAla=0; }
  };
  
  ClauseElimination( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, Propagation& _propagation );

  bool process(Coprocessor::CoprocessorData& data);
  
  void initClause(const CRef cr); // inherited from Technique
  
  void printStatistics(ostream& stream);
  
  void destroy();
  
  void giveMoreSteps();
  
protected:
  
  /** try to run CCE on clause cr, return true if clause has been removed */
  bool eliminate(Coprocessor::CoprocessorData& data, Coprocessor::ClauseElimination::WorkData& wData, Minisat::CRef cr);

  /** check whether all clauses with literal ~l result in a tautology when resolved with l based on the mark-array
   * @return true, if l is blocking literal wrt. array
   */
  bool markedBCE(const Coprocessor::CoprocessorData& data, const Lit& l, const MarkArray& array);
  
  /** check whether the clause resolved with the array results in a tautology */
  bool markedBCE(const Lit& l, const Clause& c, const MarkArray& array);

  
  /*
   *  Parallel Stuff later!!
   */
  
  /** data for parallel execution */
  struct EliminationWorkData {
    ClauseElimination*     subsumption; // class with code
    CoprocessorData* data;        // formula and maintain lists
    unsigned int     start;       // partition of the queue
    unsigned int     end;
  };

  /** run parallel subsumption with all available threads */
  void parallelElimination(CoprocessorData& data);
  
public:

  /** converts arg into SubsumeWorkData*, runs subsumption of its part of the queue */
  static void* runParallelElimination(void* arg);

};

}

#endif