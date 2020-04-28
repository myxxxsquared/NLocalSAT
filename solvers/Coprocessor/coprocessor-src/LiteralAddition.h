/*******************************************************************************[LiteralAddition.h]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef LITERALADDITION_HH
#define LITERALADDITION_HH

#include "core/Solver.h"
#include "coprocessor-src/Technique.h"
#include "coprocessor-src/CoprocessorTypes.h"
#include "coprocessor-src/Propagation.h"

using namespace Minisat;

namespace Coprocessor {

/** this class is used for blocked clause elimination procedure
 */
class LiteralAddition : public Technique  {
    
  CoprocessorData& data;
  Coprocessor::Propagation& propagation;
  
  /// compare two literals
  struct LitOrderLAHeapLt { // sort according to number of occurrences of complement!
        CoprocessorData & data; // data to use for sorting
	bool useComplements; // sort according to occurrences of complement, or actual literal
        bool operator () (int& x, int& y) const {
	  if( useComplements ) return data[ ~toLit(x)] > data[ ~toLit(y) ]; 
	  else return data[ toLit(x)] > data[ toLit(y) ]; 
        }
        LitOrderLAHeapLt(CoprocessorData & _data, bool _useComplements) : data(_data), useComplements(_useComplements) {}
  };
  
  // attributes
  Clock laTime, claTime, alaTime; // clocks for the methods
  
  int claTestedLits, claSteps, claExtendedClauses, claExtensions;
  int64_t possibleClaExtensions; // cla stats
  
  int alaSteps,alaTestedLits, alaExtensions;
  
public:
  LiteralAddition( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Coprocessor::Propagation& _propagation  );

  void reset();
  
  /** applies blocked clause elimination algorithm
  * @return true, if something has been altered
  */
  bool process();
    
  void printStatistics(ostream& stream);

  void giveMoreSteps();
  
  void destroy();
  
protected:
  /** check whether resolving c and d on literal l results in a tautology 
   * Note: method assumes c and d to be sorted
   */
  bool tautologicResolvent( const Clause& c, const Clause& d, const Lit l );
  
  /** run a covered literal addition to increase the size of clauses */
  void coverdLiteralAddition();
  
  
  /** run a asymmetric literal addition to increase the size of clauses */
  void asymemtricLiteralAddition();
};

}

#endif