/*******************************************************************************************[sls.h]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/



#ifndef SLS_H
#define SLS_H

#include "coprocessor-src/CoprocessorTypes.h"
#include "coprocessor-src/Technique.h"

namespace Coprocessor {

/** implements a simple walksat solver that can be executed on the formula */
class Sls : public Technique
{

public:
  Sls(CP3Config &_config, CoprocessorData& _data, ClauseAllocator& _ca, ThreadController& _controller);
  ~Sls();

  /** run sls algorithm on formula 
  * @param model vector that can contain a model for the formula afterwards
  * @return true, if a model has been found
  */
  bool solve(  const vec< Minisat::CRef >& formula, uint64_t stepLimit  );

  /** if search succeeded, return polarity for variable v (1 = positive, -1 = negative) */
  char getModelPolarity( const Var v ) { return varData[v].polarity ? -1 : 1; }

  /** This method should be used to print the statistics of the technique that inherits from this class
  */
  void printStatistics( ostream& stream );

  void destroy();
  
  void giveMoreSteps();
  
private:
  
  CoprocessorData& data;	// reference to coprocessor data object
  ClauseAllocator& ca;	// reference to clause allocator
  double solveTime;		// number of seconds for solving
  
  // keep track of unsat clauses
  vector<CRef> unsatClauses; // data
  vector<int> indexes; // indexes
  
  uint64_t flips;
  
  struct VarData {
    int breakCount;
    bool polarity; // true = false!
    VarData() : breakCount(0),polarity(false) {}
  };
  
  vector<VarData> varData;
  
  // data per variable
  struct ClsData {
    Var watch1;
    Var watch2;
    int satLiterals;
    
    ClsData() : watch1(1 << 30), watch2(1 << 30), satLiterals(0){}
  };
  
  vector< ClsData > clsData;
  
  vector< vector< int > > occ;
	
  void addHeap(int index) {
    assert( indexes[ index ] == -1 && "cannot be in already" );
    indexes[ index ] = unsatClauses.size();
    unsatClauses.push_back(index);
  }
  
  void delHeap( int index ) {
    unsatClauses[ indexes[index] ] = unsatClauses[ unsatClauses.size() -1 ];
    indexes[ unsatClauses[ indexes[index] ] ] = indexes[index];
    unsatClauses.pop_back();
    indexes[index] = -1;
  }
  
  bool contains( int index ) const {
    return indexes[index] != -1; 
  }
    
  bool isSat( const Lit& l ) const {
    return (sign(l) && varData[var(l)].polarity == false) 
       || (!sign(l) && varData[var(l)].polarity == true);
  }
  
  bool isUnsat( const Lit& l ) const {
    return !isSat(l);
  }
  
  /** heuristic implementations
  */
  Lit heuristic();

  /** fill the assignment with random values
  */
  void createRandomAssignment();
  
  unsigned unsats;
};

}; // end namespace

#endif // SLS_H
