/*******************************************************************************************[BVA.h]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef BVA_HH
#define BVA_HH

#include "core/Solver.h"
#include "coprocessor-src/Technique.h"
#include "coprocessor-src/CoprocessorTypes.h"
#include "coprocessor-src/Propagation.h"

using namespace Minisat;

namespace Coprocessor {

/** this class is used for bounded variable addition (replace patterns by introducion a fresh variable)
 */
class BoundedVariableAddition : public Technique  {
    
  CoprocessorData& data;
  Propagation propagation;
  
  // attributes for current run
  bool doSort;			// ensure that all clauses are sorted afterwards (assume, they are sorted before)
  
  // statistics
  double processTime;		// seconds of process time
  double andTime,iteTime,xorTime;	// seconds per technique
  
  uint32_t andDuplicates;		// how many duplicate clauses have been found
  uint32_t andComplementCount;	// how many complementary literals have been found (strengthening)
  uint32_t andReplacements;	// how many new variables could be introduced
  uint32_t andTotalReduction;	// how many clauses have been reduced
  uint32_t andReplacedOrs;		// how many disjunctions could be replaced by the fresh variable
  uint32_t andReplacedMultipleOrs;	// how many times could multiple or gates be replaced
  int64_t andMatchChecks;
  
  int xorfoundMatchings;
  int xorMultiMatchings;
  int xorMatchSize;
  int xorMaxPairs;
  int xorFullMatches;
  int xorTotalReduction;
  int64_t xorMatchChecks;
  
  int iteFoundMatchings;
  int iteMultiMatchings;
  int iteMatchSize;
  int iteMaxPairs ;
  int iteTotalReduction;
  int64_t iteMatchChecks;
  
  
  // work data
  /// compare two literals
  struct LitOrderBVAHeapLt {
        CoprocessorData & data;
        bool operator () (int& x, int& y) const {
	    return data[ toLit(x)] > data[toLit(y)]; 
        }
        LitOrderBVAHeapLt(CoprocessorData & _data) : data(_data) {}
  };
  
  // structures that would be created on during functions again and again
  vector< vector< CRef > > bvaMatchingClauses; // found pairs of clauses
  vector< Lit > bvaMatchingLiterals; // literals that stay in the match
  // use general mark array!
  vector< Lit > bvaCountMark;	// mark literal candidates (a) for the current literal(b)
  vector< uint32_t > bvaCountCount; // count occurence of a together with b
  vector< uint64_t > bvaCountSize; // count occurence of a together with b
  vec<Lit> clauseLits;			// vector that is added for clause definitions
 
public:
  BoundedVariableAddition( Coprocessor::CP3Config& _config, ClauseAllocator& _ca, Coprocessor::ThreadController& _controller, Coprocessor::CoprocessorData& _data, Coprocessor::Propagation& _propagation );
  
  void reset();
  
  /** applies bounded variable addition algorithm
  * @return true, if something has been altered
  */
  bool process();
    
  void printStatistics(ostream& stream);

  void giveMoreSteps();
  
  void destroy();
  
protected:
  
  /** perform AND-bva */
  bool andBVA();

  /** perform ITE-bva */
  bool iteBVAhalf();
  bool iteBVAfull();
  
  /** perform XOR-bva */
  bool xorBVAhalf();
  bool xorBVAfull();
  
  /** prototype implementation of a BVA version that can replace multiple literals
  */
  bool variableAddtionMulti(bool sort = true);
  
  /** sub-routine of BVA to handle complementary literals
  * @param right literal that represents the right side
  * @return false, if shrinking a clause to unit led to a failed enqueue (UNSAT)
  */
  bool bvaHandleComplement( const Lit right, Heap< Coprocessor::LitOrderHeapLt >& bvaHeap );

  /** introduce a fresh variable, update the size of all required structures*/
  Var nextVariable(char type, Heap<LitOrderHeapLt>& bvaHeap);

  /** check data structures */
  bool checkLists(const string& headline);
  
  /** pair of literals and clauses, including sort operator */
  struct xorHalfPair {
    Lit l1,l2;
    CRef c1,c2;
    xorHalfPair( Lit _l1, Lit _l2, CRef _c1, CRef _c2) : l1(_l1),l2(_l2),c1(_c1),c2(_c2){}
    xorHalfPair() : l1(lit_Undef),l2(lit_Undef),c1(CRef_Undef),c2(CRef_Undef){}
    
    /** generate an order, so that pairs that belong to the same XOR gate are placed behind each other */
    bool operator>(const xorHalfPair& other ) const {
      return ( toInt(l2) > toInt( other.l2 ));
    }
    bool operator<(const xorHalfPair& other ) const {
      return ( toInt(l2) < toInt( other.l2 ));
    }
    
  };

  struct iteHalfPair {
    Lit l1,l2,l3;
    CRef c1,c2;
    iteHalfPair( Lit _l1, Lit _l2, Lit _l3, CRef _c1, CRef _c2)
      : l1(_l1),l2(_l2),l3(_l3),c1(_c1),c2(_c2){}
      
    iteHalfPair() : l1(lit_Undef),l2(lit_Undef),l3(lit_Undef),c1(CRef_Undef),c2(CRef_Undef){}

      /** generate an order, so that pairs that belong to the same ITE gate are placed behind each other */
    bool operator>(const iteHalfPair& other) const {
	const Var iv2 = var(l2); const Var jv2 = var(other.l2);
	const Var iv3 = var(l3); const Var jv3 = var(other.l3);
	const bool signDiff = (sign(l2));
	return (   iv2 > jv2
	   || (iv2 == jv2 &&  iv3 > jv3)
	   || (iv2 == jv2 &&  iv3 == jv3 && signDiff )
	);
    }
    bool operator<(const iteHalfPair& other) const {
      return other > *this; 
    }
  };
  
  /** remove duplicate clauses from the clause list of the given literal*/
  void removeDuplicateClauses( const Lit literal );
  
public:
  // parameters
  bool bvaComplement;		/// treat found complements special?
  uint32_t bvaPush;		/// which literals to push to queue again (0=none,1=original,2=all)
  bool bvaRewEE;		/// run rewEE after BVA found new gates?
  int64_t bvaALimit;		/// number of checks until and-bva is aborted
  int64_t bvaXLimit;		/// number of checks until xor-bva is aborted
  int64_t bvaILimit;		/// number of checks until ite-bva is aborted
  bool bvaRemoveDubplicates;	/// remove duplicate clauses from occurrence lists
  bool bvaSubstituteOr;	/// when c = (a AND b) is found, also replace (-a OR -b) by -c
};

};

#endif