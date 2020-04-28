/**************************************************************************************[Symmetry.h]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef SYMMETRY_HH
#define SYMMETRY_HH

#include "core/Solver.h"
#include "coprocessor-src/CoprocessorTypes.h"
#include "coprocessor-src/Technique.h"

using namespace Minisat;
using namespace std;

namespace Coprocessor {
 
// forward declaration
  
/** class that implements local symmetry detection */
class Symmetry : public Technique {
  
  CoprocessorData& data;
  Solver& solver;
  
  double processTime;
  int addPairs;
  int maxEq;
  int maxOcc;
  int eqs;
  int replaces;
  int totalConflicts;
  
public:
  Symmetry( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Solver& _solver);
  
  /** perform local symmetry detection
   * @return false, if formula is UNSAT
   */
  bool process();
  
  /** This method should be used to print the statistics of the technique that inherits from this class
   */
  void printStatistics( ostream& stream );
  
  void destroy();
  
  void giveMoreSteps();
  
protected:
  
  struct ScorePair {
     Var v1,v2;
     float score;
     ScorePair( Var _v1, Var _v2, float _score ) : v1(_v1), v2(_v2),score(_score) {}
     
    ScorePair() : v1(0),v2(0),score(0) {} 
     
    bool operator<( const ScorePair& other ) const {
      return score < other.score;
    }
  };

  class Symm {
    
  public:
    int v;
    uint64_t c2,c3,c4,c5,c6,c7,cl;
    Symm() : v(0),c2(0),c3(0),c4(0),c5(0),c6(0),c7(0),cl(0) {}
    
    bool operator<( const Symm& other ) const {
      return c2 < other.c2 ||
	     ( c2 == other.c2 && c3 < other.c3 ) ||
	     ( c2 == other.c2 && c3 == other.c3 && c4 < other.c4) ||
	     ( c2 == other.c2 && c3 == other.c3 && c4 == other.c4 && c5 < other.c5) ||
	     ( c2 == other.c2 && c3 == other.c3 && c4 == other.c4 && c5 == other.c5 && c6 < other.c6) ||
	     ( c2 == other.c2 && c3 == other.c3 && c4 == other.c4 && c5 == other.c5 && c6 == other.c6 && c7 < other.c7) ||
	     ( c2 == other.c2 && c3 == other.c3 && c4 == other.c4 && c5 == other.c5 && c6 == other.c6 && c7 == other.c7 && cl < other.cl);
    }

//     Symm( Symm& other ) {
//       v = other.v; c2 = other.c2; c3 = other.c3; c4 = other.c4; c5 = other.c5; c6 = other.c6; c7 = other.c7; cl = other.cl;
//       //printf("re-build Symm\n");
//       //printf("c %3d -- %3d %3d %3d %3d %3d %3d %3d \n", v+1,c2,c3,c4,c5,c6,c7,cl);
//     }
//     
//      Symm& operator=( const Symm& other ) {
//        v = other.v; c2 = other.c2; c3 = other.c3; c4 = other.c4; c5 = other.c5; c6 = other.c6; c7 = other.c7; cl = other.cl;
//        //printf("re-copy Symm\n");
//        //printf("c %3d -- %3d %3d %3d %3d %3d %3d %3d \n", v+1,c2,c3,c4,c5,c6,c7,cl);
//        return *this;
//      }
    
    bool operator==( const Symm& other ) const {
      return c2 == other.c2 && c3 == other.c3 && c4 == other.c4 &&  c5 == other.c5 && c6 == other.c6 && c7 == other.c7 && cl == other.cl;
    }
    
    Symm& operator+( const Symm& other ) {
      c2 += other.c2;
      c3 += other.c3;
      c4 += other.c4;
      c5 += other.c5;
      c6 += other.c6;
      c7 += other.c7;
      cl += other.cl;
      return *this;
    }
    
    
    Symm& operator*( const int64_t factor ) {
      c2 *= factor;
      c3 *= factor;
      c4 *= factor;
      c5 *= factor;
      c6 *= factor;
      c7 *= factor;
      cl *= factor;
      return *this;
    }

    Symm inv() {
      Symm s;
      s.c2 = -c2; s.c3 = -c3; s.c4 = -c4; s.c5 = -c5; s.c6 = -c6; s.c7 = -c7; s.cl = -cl; 
      s.v = v;
      return s;
    }
    
    void add( int i ) {
      switch( i ) {
	case 2:  c2 ++; break;
	case 3:  c3 ++; break;
	case 4:  c4 ++; break;
	case 5:  c5 ++; break;
	case 6:  c6 ++; break;
	case 7:  c7 ++; break;
	default: cl ++; break;
      }
    }
    
    void sub( int i ) {
      switch( i ) {
	case 2:  c2 --; break;
	case 3:  c3 --; break;
	case 4:  c4 --; break;
	case 5:  c5 --; break;
	case 6:  c6 --; break;
	case 7:  c7 --; break;
	default: cl --; break;
      }
    }
    
  };
  
  bool notYetAnalyzed;		// indicate whether the method hack has been called already
  int symmAddClause;		// number of added clauses
  
};
  
};

#endif