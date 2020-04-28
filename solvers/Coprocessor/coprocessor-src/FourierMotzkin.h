/********************************************************************************[FourierMotzkin.h]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef FOURIERMOTZKIN_HH
#define FOURIERMOTZKIN_HH

#include "core/Solver.h"
#include "coprocessor-src/Technique.h"
#include "coprocessor-src/CoprocessorTypes.h"

#include "coprocessor-src/Propagation.h"

using namespace Minisat;

namespace Coprocessor {

/** this class is used for the fourier motzkin procedure on extracted cardinality constraints
 */
class FourierMotzkin : public Technique  {
    
  CoprocessorData& data;
  Propagation& propagation;
  Solver& solver;
  
  double processTime,amoTime,amtTime,fmTime,twoPrTime,deduceAloTime,semTime;
  int64_t steps, searchSteps;
  int fmLimit;
  int foundAmos,foundAmts,newAmos,newAlos,newAlks;
  int sameUnits,deducedUnits,propUnits;
  int addDuplicates;
  int irregular, pureAmoLits;
  int usedClauses;
  int cardDiff, discardedCards, discardedNewAmos;
  int removedCards, newCards;
  int addedBinaryClauses,addedClauses;
  int detectedDuplicates;
  int garbageCollects;
  
  int twoPrAmos, twoPrAmoLits; // stats for two pr amo lits
  int dedAlos;
  
  int semExtendedCards, semFailedExtendTries, semExtendLits, semReducedDegrees, 
  semTotalProbes, semTotalFailedProbes, semNrDisabledClauses, semNrPreDisabledClauses, semUnits;
  uint64_t semSteps;
  
  
  vec<Lit> unitQueue; // store literals that should be propagated on the card constraints
  
  /// compare two literals
  struct LitOrderHeapLt {
        CoprocessorData & data;
        bool operator () (int& x, int& y) const {
	    return data[ toLit(x)] > data[toLit(y)]; 
        }
        LitOrderHeapLt(CoprocessorData & _data) : data(_data) {}
  };
  
  /// struct to handle ternary clauses efficiently
  struct Ternary {
    Lit lit [3];
    Ternary ( const Lit a, const Lit b, const Lit c )
    {
      lit[0] = ( a > b ? ( b > c ? c : b ) : ( a > c ? c : a ) ); // min
      lit[2] = ( a > b ? ( a > c ? a : c ) : ( b > c ? b : c)  ); // max
      lit[1] = toLit( toInt(a) ^ toInt(b) ^ toInt(c) ^ toInt( lit[0] ) ^ toInt( lit[2] ) ); // xor all three lits and min and max (the middle remains)
    }
    Lit operator[](const int position) const {
      return lit[position];
    }
  };

  /** represent a (mixed) cardinality constraint*/
  public:
  class CardC {
  public:
    vector<Lit> ll;
    vector<Lit> lr;
    int k;
    CardC( vector<Lit>& amo ) : ll(amo), k(1) {}; // constructor to add amo constraint
    CardC( vector<Lit>& amk, int _k ) : ll(amk), k(_k) {}; // constructor to add amk constraint
    CardC( const Clause& c ) :k(-1) { lr.resize(c.size(),lit_Undef); for(int i = 0 ; i < c.size(); ++i ) lr[i] = c[i]; }// constructor for usual clauses
    bool amo() const { return k == 1 && lr.size() == 0 ; }
    bool amt() const { return k == 2 && lr.size() == 0 ; }
    bool amk() const { return k >= 0 && lr.size() == 0 ; }
    bool alo() const { return k == -1 && ll.size() == 0; }
    bool alk() const { return k < 0 && ll.size() == 0; }
    bool isUnit() const { return (k + (int)lr.size()) == 0; } // all literals in ll have to be false, and all literals in lr have to be true
    bool failed() const { return (((int)lr.size() + k) < 0) ; }
    bool taut() const { return k >= (int)ll.size(); } // assume no literal appears both in ll and lr
    bool invalid() const { return k==0 && ll.size() == 0 && lr.size() == 0; } // nothing stored in the constraint any more
    void invalidate() { k=0;vector<Lit>().swap(ll);vector<Lit>().swap(lr);}
    CardC() : k(0) {} // default constructor
    void swap( CardC& other ) { /// swap with other constraint
      const int t = other.k; other.k = k; k = t;
      ll.swap( other.ll );
      lr.swap( other.lr );
    }
  };
  
public:
  FourierMotzkin( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Propagation& _propagation, Solver& _solver );

  void reset();
  
  /** extractes cardinality constraints and applies the fourier motzkin algorithm
  * @return true, if something has been altered
  */
  bool process();
    
  void printStatistics(ostream& stream);

  void giveMoreSteps();
  
  void destroy();
  
  
protected:
  /** propagate the literals in unitQueue over all constraints*/
  bool propagateCards( vec<Lit>& unitQueue, vector< vector<int> >& leftHands, vector< vector<int> >& rightHands, vector<CardC>& cards,MarkArray& inAmo);
  
  /** check whether the given clause is already present in the given list */
  bool hasDuplicate(const vector<Lit>& c);

  /** given a set of cardinality constraints, and a BIG, try to deduce more AMOs following the two product encoding */
  void findTwoProduct(vector< CardC >& cards, BIG& big, vector< vector<int> >& leftHands);

  /** return whether a current set of literals already exists as AMO, or is subsumed by an existing one 
   * Note: assumes the literal lits to be sorted, and all AMOs inside cards as well
   */
  bool amoExistsAlready(const vector< Lit >& lits, vector< std::vector< int > >& leftHands, vector<CardC>& cards);

  /** try to deduce ALO constraints
   *  if something like a board is encoded, then try to add additional ALO constraints (from dangerous reductions paper)
   */
  void deduceALOfromAmoAloMatrix(vector< CardC >& cards, vector< std::vector< int > >& leftHands);
  
  /** remove all the AMOs, whose effect is already covered by some other AMO */
  void removeSubsumedAMOs(vector< CardC >& cards, vector< std::vector< int > >& leftHands);
  
  /** given a formula, try to extract cardinality constraints semantically */
  void findCardsSemantic( vector<CardC>& cards,  vector< vector<int> >& leftHands );
  
  /** given a number x with n bits set, then the procedure returns the next number */
  LONG_INT nextNbitNumber(LONG_INT x) const;
  
  /** add all clauses to solver object -- code taken from @see Preprocessor::reSetupSolver, but without deleting clauses */
  void reSetupSolver();
  
  /** remove all clauses from the watch lists inside the solver */
  void cleanSolver();
};

//   inline ostream& operator<<( ostream& stream, const FourierMotzkin::CardC& card ) {
//       stream << "(" << card.ll << " <= " << card.k << " + " << card.lr << ")";
//       return stream;
//   }

}

#endif