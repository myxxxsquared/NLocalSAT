/***************************************************************************************[Rewriter.h]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef REWRITER_HH
#define REWRITER_HH

#include "core/Solver.h"
#include "coprocessor-src/Technique.h"
#include "coprocessor-src/CoprocessorTypes.h"

#include "coprocessor-src/Subsumption.h"

using namespace Minisat;

namespace Coprocessor {

/** this class is used for bounded variable addition (replace patterns by introducion a fresh variable)
 */
class Rewriter : public Technique  {
    
  CoprocessorData& data;
  
  // statistics
  double processTime;		// seconds of process time
  double rewAmoTime, rewImplTime; // time per procedure
  double amoTime;	// seconds of process time
  double rewTime;	// seconds of process time
  unsigned rewLimit; // upper limit of steps
  unsigned steps;  //current number of steps

  // TODO: initialize these ones!
  unsigned detectedDuplicates;     // how many clauses after rewriting detected as duplicate
  unsigned createdClauses;
  unsigned droppedClauses;
  unsigned enlargedClauses;
  unsigned sortCalls;
  unsigned reuses;
  unsigned processedAmos,processedChains;
  unsigned foundAmos;
  unsigned exoAMOs;
  unsigned maxAmo;
  unsigned addedVariables;
  unsigned removedVars;
  unsigned removedViaSubsubption;
  unsigned maxChain, minChain, foundChains;
  
  Subsumption& subsumption;		/// object that takes care of subsumption and strengthening
  
  // work data
  /// compare two literals
  struct LitOrderHeapLt {
        CoprocessorData & data;
        bool operator () (int& x, int& y) const {
	    return data[ toLit(x)] > data[toLit(y)]; 
        }
        LitOrderHeapLt(CoprocessorData & _data) : data(_data) {}
  };
  Heap<LitOrderHeapLt> rewHeap; // heap that stores the variables according to their frequency
  
public:
  
  Rewriter( CP3Config &_config, ClauseAllocator& _ca, Coprocessor::ThreadController& _controller, Coprocessor::CoprocessorData& _data, Coprocessor::Subsumption& _subsumption );
  
  void reset();
  
  /** applies bounded variable addition algorithm
  * @return true, if something has been altered
  */
  bool process();
    
  void printStatistics(ostream& stream);

  void destroy();
  
    void giveMoreSteps();
  
protected:
  
  /** take care of creating a new variable */
  Var nextVariable(char type);
  
  /** method responsible for rewriting AMO constraints */
  bool rewriteAMO() ;
  /** method responsible for rewriting implication chains constraints */
  bool rewriteImpl() ;
  
  /** check whether the clause represented in the vector c has duplicates, and remove clauses that are subsumed by c */
  bool hasDuplicate(vector<CRef>& list, const vec<Lit>& c);
  bool hasDuplicate(vector<CRef>& list, const Clause& c);
  
  bool checkPush(vec<Lit> & ps, const Lit l);
  bool ordered_subsumes (const Clause& c, const Clause & other) const;
  bool ordered_subsumes (const vec<Lit>& c, const Clause & other) const;
  bool ordered_subsumes (const Clause & c, const vec<Lit>& other) const;
  
public:
  
  
};

};

#endif