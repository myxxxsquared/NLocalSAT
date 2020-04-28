/*******************************************************************************************[xor.h]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef XOR_HH
#define XOR_HH

#include "core/Solver.h"
#include "coprocessor-src/Technique.h"
#include "coprocessor-src/CoprocessorTypes.h"

#include "coprocessor-src/Propagation.h"
#include "coprocessor-src/EquivalenceElimination.h"

#include <vector>

using namespace Minisat;
using namespace std;

namespace Coprocessor {

/** this class is used forthe gauss elimination algorithm
 */
class XorReasoning : public Technique  {
    
  CoprocessorData& data;
  Propagation& propagation;	/// object that takes care of unit propagation
  EquivalenceElimination& ee;	/// object that takes care of equivalent literal elimination
  
  double processTime,parseTime,reasonTime;
  int findChecks;
  int xors;			// number of found xors
  int xorClauses;		// count how many clauses have been used to encode the xors
  int resolvedInCls,subsFound,resFound;
  int resTauts,resStrength;
  
  int xorLimit,xorSteps;
  int foundEmptyLists,xorUnits,allUsed,xorDeducedUnits,eqs;
  
  /// compare two literals
  struct VarLt {
        vector< vector <int> > & data;
        bool operator () (int& x, int& y) const {
	    return data[ x ].size() > data[ y].size(); 
        }
        VarLt(vector<vector< int> > & _data) : data(_data) {}
  };
  
  /** structure to use during simple gauss algorithm */
  class GaussXor {
  public:
    vector<Var> vars;
    bool k; // polarity of XOR has to be true or false
    bool used; // indicate whether this constraint has been used for simplification already
    bool eq() const { return vars.size() == 2 ; }
    bool unit() const { return vars.size() == 1; }
    Lit getUnitLit() const { return unit() ? mkLit(vars[0],!k) : lit_Undef; }
    bool failed() const { return vars.size() == 0 && k; }
    GaussXor( const Clause& c ) : k(true),used(false) { // build xor from clause
      vars.resize(c.size());
      for( int i = 0 ; i < c.size(); ++ i ){
	vars[i] = var( c[i] );
	k = sign(c[i]) ? !k : k ; // change polarity of k, if literal is negative!
      }
    }
    GaussXor() : k(false),used(false) {} // create an empty xor
    
    int size() const { return vars.size(); }
    
    /** add the other xor to this xor 
     * @param removed list of variables that have been removed from the xor
     * @param v1 temporary vector
     */
    void add ( const GaussXor& gx, vector<Var>& removed, vector<Var>& v1) {
      k = (k != gx.k); // set new k!
      v1 = vars; // be careful here, its a copy operation!
      vars.clear();
      const vector<Var>& v2 = gx.vars;
      // generate new vars!
      int n1 = 0,n2=0;
      while( n1 < v1.size() && n2 < v2.size() ) {
	if( v1[n1] == v2[n2] ) {
	  removed.push_back(v2[n2]); // variables that appear in both XORs will be removed!
	  n1++;n2++;
	} else if( v1[n1] < v2[n2] ) {
	  vars.push_back(v1[n1++]);
	} else {
	  vars.push_back(v2[n2++]);
	}
      }
      for(;n1<v1.size();++n1) vars.push_back(v1[n1]);
      for(;n2<v2.size();++n2) vars.push_back(v2[n2]);
    }
    
  };
  
public:

  XorReasoning( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data,  Propagation& _propagation, EquivalenceElimination& _ee  );

  void reset();
  
  /** apply the gauss elimination algorithm
  * @return true, if something has been altered
  */
  bool process();
    
  void printStatistics(ostream& stream);

  void giveMoreSteps();
  
  void destroy();
  
  // remove index from all variable lists that are listed in x
  void dropXor(int index, std::vector< Var >& x, vector< std::vector< int > >& occs);
  
  /** propagate found units in all related xors 
   * @return true if no conflict was found, false if a conflict was found
   */
  bool propagate(vector< Lit >& unitQueue, MarkArray& ma, vector< std::vector< int > >& occs, vector< GaussXor >& xorList);

protected:
  
  /** find xors in the formula, with given max size */
  bool findXor(vector< Coprocessor::XorReasoning::GaussXor >& xorList);
  
};

}

#endif
struct Gauss;