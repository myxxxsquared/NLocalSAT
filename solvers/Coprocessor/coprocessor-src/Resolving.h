/*************************************************************************************[Resolving.h]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef RESOLVING_H
#define RESOLVING_H

#include "coprocessor-src/CoprocessorTypes.h"

#include "coprocessor-src/Technique.h"
#include "coprocessor-src/Propagation.h"

using namespace Minisat;
using namespace std;

namespace Coprocessor {

class Resolving  : public Technique
{
  CoprocessorData& data;
  Propagation& propagation;            /// object that takes care of unit propagation
  
  vector<int> seen; // remembers how many clauses per variable have been processed already
  
public:
  Resolving(CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Propagation& _propagation);

  bool process( bool post = false);

  /** inherited from @see Technique */
  void printStatistics( ostream& stream );
  
  void destroy();
  
  void giveMoreSteps();
  
protected:
  
  /** resolve ternary clauses */
  void ternaryResolve();
  
  /** add redundant binary clauses */
  void addRedundantBinaries();

  /** check whether this clause already exists in the occurence list */
  bool hasDuplicate(vector< Minisat::CRef >& list, const vec< Lit >& c);
  
  /**
  * expects c to contain v positive and d to contain v negative
  * @return true, if resolvent is satisfied
  *         else, otherwise
  */
  bool resolve(const Clause & c, const Clause & d, const int v, vec<Lit> & resolvent);
  
  // check whether a vector of lits subsumes a given clause
  bool ordered_subsumes (const vec<Lit>& c, const Clause & other) const;
  bool ordered_subsumes (const Clause & c, const vec<Lit>& other) const;
  
  bool checkPush(vec<Lit> & ps, const Lit l);
  
  double processTime;
  unsigned addedTern2;
  unsigned addedTern3;
  unsigned addedBinaries;
  unsigned res3steps;
  unsigned add2steps;
  unsigned removedViaSubsubption;
  unsigned detectedDuplicates;
  
  /// compare two literals
  struct VarOrderHeapLt {
        CoprocessorData & data;
        bool operator () (const Var& x, const Var& y) const {
	    return data[ x] < data[y]; 
        }
        VarOrderHeapLt(CoprocessorData & _data) : data(_data) {}
  };
  Heap<VarOrderHeapLt> resHeap; // heap that stores the variables according to their frequency (dedicated for BVA)
  
};


}

#endif // RESOLVING_H
