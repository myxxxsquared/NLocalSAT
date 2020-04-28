/******************************************************************************[CoprocessorTypes.h]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef COPROCESSORTYPES_HH
#define COPROCESSORTYPES_HH

#include "core/Solver.h"

#include "utils/System.h"
#include "mtl/Sort.h"

#include "utils/LockCollection.h"
#include "utils/AutoDelete.h"

#include <vector>
#include <iostream>

using namespace Minisat;
using namespace std;

namespace Coprocessor {

  /// temporary Boolean flag to quickly enable debug output for the whole file
  const bool global_debug_out = false;
  
  //forward declaration
  class VarGraphUtils;

typedef std::vector<std::vector <CRef> > ComplOcc;

/** class that measures the time between creation and destruction of the object, and adds it*/
class MethodTimer {
  double* pointer;
public:
  MethodTimer( double* timer ) : pointer( timer ) { *pointer = cpuTime() - *pointer;}
  ~MethodTimer() { *pointer = cpuTime() - *pointer; }
};  


/** class responsible for debug output */
class Logger
{
  int outputLevel; // level to output
  bool useStdErr;  // print to stderr, or to stdout?
public:
  Logger(int level, bool err = true);

  void log( int level, const string& s );
  void log( int level, const string& s, const int i);
  void log( int level, const string& s, const Clause& c);
  void log( int level, const string& s, const Lit& l);
  void log( int level, const string& s, const Clause& c, const Lit& l);
};

struct VarOrderBVEHeapLt;

/** Data, that needs to be accessed by coprocessor and all the other classes
 */
class CoprocessorData
{
  // friend for VarGraph
  friend class Coprocessor::VarGraphUtils;

  ClauseAllocator& ca;
  Solver* solver;
  /* TODO to add here
   * occ list
   * counters
   * methods to update these structures
   * no statistical counters for each method, should be provided by each method!
   */
  uint32_t numberOfVars;                // number of variables
  uint32_t numberOfCls;                 // number of clauses during initialization
  uint32_t numberOfTotalLiterals;       // number of total literals in the formula during initialization
  ComplOcc occs;                        // list of clauses, per literal
  vector<int32_t> lit_occurrence_count; // number of literal occurrences in the formula

  bool hasLimit;                        // indicate whether techniques should be executed limited
  bool randomOrder;                     // perform preprocessing with random execution order within techniques
  bool currentlyInprocessing;           // current simplification is during search
  bool debugging;                       // current version works in debugging mode
  
  Lock dataLock;                        // lock for parallel algorithms to synchronize access to data structures

  MarkArray deleteTimer;                // store for each literal when (by which technique) it has been deleted

  vector<Lit> undo;                     // store clauses that have to be undone for extending the model
  int lastCompressUndoLits;             // number of literals when the last compression took place
  int decompressedUndoLits;             // number of literals on the decompressedUndoLits stack

private:
  vector<Lit> equivalences;             // stack of literal classes that represent equivalent literals
  vector<CRef> subsume_queue; // queue of clause references that potentially can subsume other clauses
  vector<CRef> strengthening_queue;     // vector of clausereferences, which potentially can strengthen

  int countLitOcc(Lit l){
    int count = 0;
    vector<CRef> & list = occs[toInt(l)];
    for (int i = 0; i < list.size(); ++i)
    {
        CRef cr = list[i];
        if (cr == CRef_Undef) continue;
        Clause & c = ca[cr];
        if (c.can_be_deleted()) continue;
        bool occurs = false;
        for (int j = 0; j < c.size(); ++j) 
            if (c[j] == l) 
            {
                occurs = true; break;
            }
        if (occurs) ++count;
        else assert(false && "dirty occurrence list!!!");
    }
    return count;
  }  
  
  // TODO decide whether a vector of active variables would be good!

public:

  Logger& log;                           // responsible for logs

  MarkArray ma;                          // temporary markarray, that should be used only inside of methods
  vector<Lit> lits;                      // temporary literal vector
  vector<CRef> clss;                     // temporary literal vector

  CoprocessorData(ClauseAllocator& _ca, Solver* _solver, Coprocessor::Logger& _log, bool _limited = true, bool _randomized = false, bool _debug = false);

  // init all data structures for being used for nVars variables
  void init( uint32_t nVars );

  /** tell preprocessor to use randomized search now */
  void randomize() { randomOrder = true; }
  
  void preprocessing() { currentlyInprocessing = false; }
  void inprocessing() { currentlyInprocessing = true; }
  bool isInprocessing() const { return currentlyInprocessing; }
  
  // free all the resources that are used by this data object,
  void destroy();

  int32_t& operator[] (const Lit l ); // return the number of occurrences of literal l
  int32_t operator[] (const Var v ) const; // return the number of occurrences of variable v
  vector<CRef>& list( const Lit l ); // return the list of clauses, which have literal l
  const vector< CRef >& list( const Lit l ) const; // return the list of clauses, which have literal l

  vec<CRef>& getClauses();           // return the vector of clauses in the solver object
  vec<CRef>& getLEarnts();           // return the vector of learnt clauses in the solver object
  vec<Lit>&  getTrail();             // return trail
  void clearTrail();                 // remove all variables from the trail, and reset qhead in the solver
  void resetPPhead();                // set the pointer to the next element to be propagated to 0

  uint32_t nCls()  const { return numberOfCls; }
  uint32_t nVars() const { return numberOfVars; }
  uint32_t nTotLits() const { return solver->nTotLits(); }
  Var nextFreshVariable(char type);
  
  /** overwrite data of variable to with data of variable from 
   * Note: does not work on watches
   * @param final if true, decision heap will be re-build, and the set of variables will be shrinked to the given to variable
   */
  void moveVar( Var from, Var to, bool final = false );
  
  /** merge the solver data from one literal to another literal
   * two variants, one for two literals, one for many literals
   * @param final if true, decision heap will be re-build, and the set of variables will be shrinked to the given to variable
   */
  void mergeVar( Lit from, Lit to, bool final = false );
  void mergeVar( vector<Lit>& from, Lit to, bool final = false );

  /// notify about variable renaming
  void didCompress() {
    if( lastCompressUndoLits != -1 &&  // if there has been a  compression,
      decompressedUndoLits != undo.size() ) { // then the complete undo-stack has to be adopted
      cerr << "c variable renaming went wrong - abort. lastCom: " << lastCompressUndoLits << " decomp: " << decompressedUndoLits << " undo: " << undo.size() << endl;
      exit(14);
    }
    lastCompressUndoLits = undo.size();
  }
  
  /// memorize that the undo info has been adopted until this size already
  void didDecompressUndo() {
    decompressedUndoLits = undo.size();
  }
  
  /** return number of literals that have already been uncompressed 
   * will return -1, if no compression took place yet
   */
  int getLastCompressUndoLits() const { return lastCompressUndoLits; }
  int getLastDecompressUndoLits() const { return decompressedUndoLits; }
  
// semantic:
  bool ok();                                             // return ok-state of solver
  void setFailed();                                      // found UNSAT, set ok state to false
  lbool enqueue( const Lit l, const uint64_t extraInfo = 0); // enqueue literal l to current solver structures, adopt to extraInfo of solver, if needed
  lbool value( const Lit l ) const ;                     // return the assignment of a literal
  void resetAssignment( const Var v );                   // set the polarity of a variable to l_Undef -- Note: be careful with this!
  
  Solver* getSolver();                                   // return the pointer to the solver object
  bool hasToPropagate();                                 // signal whether there are new unprocessed units
  
  bool unlimited();                                      // do preprocessing without technique limits?
  bool randomized();                                     // use a random order for preprocessing techniques
  bool isInterupted();					  // has received signal from the outside

// adding, removing clauses and literals =======
  void addClause (      const CRef cr, bool check = false );                 // add clause to data structures, update counters
  void addClause (      const CRef cr , Heap<VarOrderBVEHeapLt> * heap, const bool update = false, const Var ignore = var_Undef, SpinLock * data_lock = NULL, SpinLock * heap_lock = NULL);     // add clause to data structures, update counters
  bool removeClauseFrom (const CRef cr, const Lit l); // remove clause reference from list of clauses for literal l, returns true, if successful
  void removeClauseFrom (const CRef cr, const Lit l, const int index); // remove clause reference from list of clauses for literal l, returns true, if successful
  inline bool removeClauseFromThreadSafe (const CRef cr, const Lit l); // replaces clause reference from clause list by CRef_Undef, returns true, if successful
  inline void cleanUpOccurrences(const MarkArray & dirtyOccs, const uint32_t timer); // removes CRef_Undef from all dirty occurrences
  void cleanOccurrences();				// remove all clauses and set counters to 0

  // Garbage Collection
  void garbageCollect(vector<CRef> ** updateVectors = 0, int size = 0);
  void relocAll(ClauseAllocator & to, vector<CRef> ** updateVectors = 0, int size = 0);
  void checkGarbage(vector<CRef> ** updateVectors = 0, int size = 0) { return checkGarbage(solver->garbage_frac, updateVectors, size); }
  void checkGarbage(double gf, vector<CRef> ** updateVectors = 0, int size = 0){  if (ca.wasted() > ca.size() * gf) garbageCollect(updateVectors, size); }

  void updateClauseAfterDelLit(const Clause& clause)
  { if( global_debug_out ) cerr << "what to update in clause?! " << clause << endl; }
  
  // sort
  void sortClauseLists(bool alsoLearnts = false);
  
// delete timers
  /** gives back the current times, increases for the next technique */
  uint32_t getMyDeleteTimer();
  /** tell timer system that variable has been deleted (thread safe!) */
  void deletedVar( const Var v );
  /** fill the vector with all the literals that have been deleted after the given timer */
  void getActiveVariables(const uint32_t myTimer, vector< Var >& activeVariables );
  /** fill the heap with all the literals that have been deleted afetr the given timer */
  template <class Comp>  
  void getActiveVariables(const uint32_t myTimer, Heap < Comp > & heap );

  /** resets all delete timer */
  void resetDeleteTimer();

// mark methods
  void mark1(Var x, MarkArray& array);
  void mark2(Var x, MarkArray& array, MarkArray& tmp);

// locking
  void lock()   { dataLock.lock();   } // lock and unlock the data structure
  void unlock() { dataLock.unlock(); } // lock and unlock data structure

// formula statistics with HeapUpdate and LockHandling
  
  void addedLiteral( const Lit l, const int32_t diff = 1, Heap<VarOrderBVEHeapLt> * heap = NULL, const bool update = false, const Var ignore = var_Undef, SpinLock * data_lock = NULL, SpinLock * heap_lock = NULL); // update counter for literal
  void removedLiteral( const Lit l, const int32_t diff = 1, Heap<VarOrderBVEHeapLt> * heap = NULL, const bool update = false, const Var ignore = var_Undef, SpinLock * data_lock = NULL, SpinLock * heap_lock = NULL); // update counter for literal
  void addedClause (   const CRef cr, Heap<VarOrderBVEHeapLt> * heap = NULL, const bool update = false, const Var ignore = var_Undef, SpinLock * data_lock = NULL, SpinLock * heap_lock = NULL );			// update counters for literals in the clause
  
  void removedClause ( const CRef cr, Heap<VarOrderBVEHeapLt> * heap = NULL, const bool update = false, const Var ignore = var_Undef, SpinLock * data_lock = NULL, SpinLock * heap_lock = NULL );			// update counters for literals in the clause
  void removedClause ( const Lit l1, const Lit l2 );		// update counters for literals in the clause

  bool removeClauseThreadSafe (const CRef cr);
  void correctCounters();

  // extending model after clause elimination procedures - l will be put first in list to be undone if necessary!
  void addToExtension( const CRef cr, const Lit l = lit_Error );
  void addToExtension( vec< Lit >& lits, const Lit l = lit_Error );
  void addToExtension( vector< Lit >& lits, const Lit l = lit_Error );
  void addToExtension( const Lit dontTouch, const Lit l = lit_Error );
  
  /// add already created vector to extension vector
  void addExtensionToExtension(vec< Lit >& lits);
  void addExtensionToExtension(vector< Lit >& lits);

  void extendModel(vec<lbool>& model);
  /// careful, should not be altered other than be the Dense object
  vector<Lit>& getUndo() { return undo; }

  /// for DRUP / DRAT proofs
#ifdef DRATPROOF
  template <class T>
  void addToProof(   T& clause, bool deleteFromProof=false, const Lit remLit = lit_Undef); // write the given clause/vector/vec to the output, if the output is enabled
  void addUnitToProof(const  Lit& l, bool deleteFromProof=false);    // write a single unit clause to the proof
  void addCommentToProof(const char* text, bool deleteFromProof=false);
  bool outputsProof() const { return solver->outputsProof(); } // return whether the solver outputs the drup proof!
#else // no DRAT proofs
  template <class T>
  void addToProof(   T& clause, bool deleteFromProof=false, const Lit remLit = lit_Undef) const {}; // write the given clause/vector/vec to the output, if the output is enabled
  void addUnitToProof(const  Lit& l, bool deleteFromProof=false) const {};    // write a single unit clause to the proof
  void addCommentToProof(const char* text, bool deleteFromProof=false) const {};
  bool outputsProof() const { return false; } // return whether the solver outputs the drup proof!
#endif
  
  // handling equivalent literals
  void addEquivalences( const std::vector<Lit>& list );
  void addEquivalences( const Lit& l1, const Lit& l2 );
  vector<Lit>& getEquivalences();

  /** add a clause to the queues, so that this clause will be checked by the next call to subsumeStrength 
   * @return true, if clause has really been added and was not in both queues before
   */
  bool addSubStrengthClause( const CRef cr , bool isNew = false);
  vector<CRef>& getSubsumeClauses();
  vector<CRef>& getStrengthClauses();
  
  // checking whether a literal can be altered - TODO: use the frozen information from the solver object!
  void setNotTouch(const Var& v);
  bool doNotTouch (const Var& v) const ;
  
  // TODO: remove after debug
  void printTrail(ostream& stream) {
    for( int i = 0 ; i < solver->trail.size(); ++ i ) cerr << " " << solver->trail[i]; 
  }
  
  /** for solver extensions, which rely on extra informations per clause (including unit clauses), e.g. the level of the solver in a partition tree*/
  bool usesExtraInfo() const { return solver->usesExtraInfo(); } 
  uint64_t defaultExtraInfo() const { return solver->defaultExtraInfo(); }
  uint64_t variableExtraInfo( const Var& v ) const { return solver->variableExtraInfo(v); }
};

/** class representing the binary implication graph of the formula */
class BIG 
{
  // TODO implement a weak "implies" check based on the implication graph sampling!
  Lit* storage;
  int* sizes;
  Lit** big;

  /** these two arrays can be used to check whether a literal l implies another literal l'
   *  Note: this is not a complete check!
   */
  uint32_t *start; // when has to literal been touch when scanning the BIG
  uint32_t *stop;  // when has to literal been finished during scanning
  
  uint32_t duringCreationVariables; // number of variables for the last construction call

  uint32_t stampLiteral( const Lit literal, uint32_t stamp, int32_t* index, deque< Lit >& stampQueue );
  void shuffle( Lit* adj, int size ) const;

public:
  BIG();
  ~BIG();

  /** adds binary clauses */
  void create( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list);
  void create( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list1, vec< CRef >& list2);

  /** recreate the big after the formula changed */
  void recreate( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list);
  void recreate( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list1, vec< CRef >& list2);
  
  /** return the number of variables that are known by the BIG */
  uint32_t getVars() const { return duringCreationVariables; }
  
  /** removes an edge from the graph again */
  void removeEdge(const Lit l0, const Lit l1 );

  /** check all implication lists for duplicates and remove the duplicates 
   * Note: side effect, the arrays are sorted
   */
  void removeDuplicateEdges(const uint32_t nVars);
  
  /** sort all the arrays */
  void sort(const uint32_t nVars);
  
  Lit* getArray(const Lit l);
  const Lit* getArray(const Lit l) const;
  int getSize(const Lit l) const;

  /** will travers the BIG and generate the start and stop indexes to check whether a literal implies another literal
   * @return false, if BIG is not initialized yet
   */
  void generateImplied(Coprocessor::CoprocessorData& data);
  void generateImplied( uint32_t nVars, vec<Lit>& tmpLits ); // alternative interface, to be able to use it during search!
  
  /** fill the literals in the order they would appear in a BFS in the big, starting with root nodes 
   *  NOTE: will pollute the data.ma MarkArray
   * @param rootsOnly: fill the vector only with root literals
   */
  void fillSorted( vector< Lit >& literals, Coprocessor::CoprocessorData& data, bool rootsOnly = true, bool getAll=false);
  void fillSorted(vector<Var>& variables, CoprocessorData& data, bool rootsOnly = true, bool getAll=false);

  /** return true, if the condition "from -> to" holds, based on the stochastic scanned data */
  bool implies(const Lit& from, const Lit& to) const;

  /** return whether child occurs in the adjacence list of parent (and thus implied) */
  bool isChild(const Lit& parent, const Lit& child) const ;

  /** return whether one of the two literals is a direct child of parent (and thus implied)  */
  bool isOneChild( const Lit& parent, const Lit& child1, const Lit& child2 ) const ;
  
  /** get indexes of BIG scan algorithm */
  uint32_t getStart( const Lit& l ) { return start != 0 && var(l) < duringCreationVariables ? start[ toInt(l) ] : 0; }
  /** get indexes of BIG scan algorithm */
  uint32_t getStop( const Lit& l ) { return stop != 0 && var(l) < duringCreationVariables  ? stop[ toInt(l) ] : 0; }
};

/** Comperator for Variable Heap of BVE */
struct VarOrderBVEHeapLt 
{
        CoprocessorData & data;
        const int heapOption;
        bool operator () (Var x, Var y) const 
        {/* assert (data != NULL && "Please assign a valid data object before heap usage" );*/ 
	  if( heapOption == 0 ) { return data[x] < data[y]; 
	  } else if( heapOption == 1 ) { return data[x] > data[y]; 
	  } else if( heapOption > 2 && heapOption < 11 ) {
	    const double xp =data[ mkLit(x,false) ];
	    const double xn =data[ mkLit(x,true)  ];
	    const double yp =data[ mkLit(y,false) ];
	    const double yn =data[ mkLit(y,true)  ];
	    double rx = 0;
	    if( xp != 0 || xn != 0 ) rx = xp > xn ?  ( xn != 0 ? xp / xn : xp * 1000 ) : ( xp != 0 ? xn  / xp : xn * 1000 );
	    double ry = 0;
	    if( yp != 0 || yn != 0 ) ry = yp > yn ?  ( yn != 0 ? yp / yn : yp * 1000 ) : ( yp != 0 ? yn  / yp : yn * 1000 );
	    
	    if( heapOption == 3 ) {
	      return ( rx < ry )
		    || ( rx == ry && data[x] < data[y] );
	    }
	    else if( heapOption == 4 )  {
	      return ( rx < ry )
		    || (rx == ry &&  data[x] > data[y] );
	    } 
	    else if( heapOption == 5 )  {
	      return ( rx > ry )
		    || (rx == ry &&  data[x] < data[y] );
	    } 
	    else if( heapOption == 6 )  {
	      return ( rx > ry )
		    || (rx == ry &&  data[x] > data[y] );
	    } 
	    else if( heapOption == 7 ) {
	      return ( data[x] < data[y] )
		    || ( rx < ry && data[x] == data[y] );
	    }
	    else if( heapOption == 8 )  {
	      return ( data[x] > data[y] )
		    || (rx < ry &&  data[x] == data[y] );
	    } 
	    else if( heapOption == 9 )  {
	      return ( data[x] < data[y] )
		    || (rx > ry &&  data[x] == data[y] );
	    } 
	    else if( heapOption == 10 )  {
	      return ( data[x] > data[y] )
		    || (rx > ry &&  data[x] == data[y] );
	    } 
	    else {
	      assert( false && "forgot to update all parameter checks!" ); 
	      return false;
	    }
	  } else {
	    assert(false && "In case of random order no heap should be used"); return false;
	  }
	  return false;
        }
        VarOrderBVEHeapLt(CoprocessorData & _data, int _heapOption) : data(_data), heapOption(_heapOption) { }
    };
    
struct LitOrderHeapLt 
{
        CoprocessorData & data;
        const int heapOption;
        bool operator () (int ix, int iy) const 
        {/* assert (data != NULL && "Please assign a valid data object before heap usage" );*/ 
          const Lit x = toLit(ix); const Lit y = toLit(iy);
	  if( heapOption == 0 ) { return data[x] < data[y]; 
	  } else if( heapOption == 1 ) { return data[x] > data[y]; 
	  } else if( heapOption > 2 && heapOption < 11 ) {
	    const double xp =data[x];
	    const double xn =data[~x];
	    const double yp =data[y];
	    const double yn =data[~y];
	    double rx = 0;
	    if( xp != 0 || xn != 0 ) rx = xp > xn ?  ( xn != 0 ? xp / xn : xp * 1000 ) : ( xp != 0 ? xn  / xp : xn * 1000 );
	    double ry = 0;
	    if( yp != 0 || yn != 0 ) ry = yp > yn ?  ( yn != 0 ? yp / yn : yp * 1000 ) : ( yp != 0 ? yn  / yp : yn * 1000 );
	    
	    if( heapOption == 3 ) {
	      return ( rx < ry )
		    || ( rx == ry && data[x] < data[y] );
	    }
	    else if( heapOption == 4 )  {
	      return ( rx < ry )
		    || (rx == ry &&  data[x] > data[y] );
	    } 
	    else if( heapOption == 5 )  {
	      return ( rx > ry )
		    || (rx == ry &&  data[x] < data[y] );
	    } 
	    else if( heapOption == 6 )  {
	      return ( rx > ry )
		    || (rx == ry &&  data[x] > data[y] );
	    } 
	    else if( heapOption == 7 ) {
	      return ( data[x] < data[y] )
		    || ( rx < ry && data[x] == data[y] );
	    }
	    else if( heapOption == 8 )  {
	      return ( data[x] > data[y] )
		    || (rx < ry &&  data[x] == data[y] );
	    } 
	    else if( heapOption == 9 )  {
	      return ( data[x] < data[y] )
		    || (rx > ry &&  data[x] == data[y] );
	    } 
	    else if( heapOption == 10 )  {
	      return ( data[x] > data[y] )
		    || (rx > ry &&  data[x] == data[y] );
	    } 
	    else {
	      assert( false && "forgot to update all parameter checks!" ); 
	    }
	  } else {
	    assert(false && "In case of random order no heap should be used"); return false;
	  }
	  return false;
        }
        LitOrderHeapLt(CoprocessorData & _data, int _heapOption) : data(_data), heapOption(_heapOption) { }
    };

inline CoprocessorData::CoprocessorData(ClauseAllocator& _ca, Solver* _solver, Coprocessor::Logger& _log, bool _limited, bool _randomized,  bool _debug)
: ca ( _ca )
, solver( _solver )
, numberOfVars(0)
, numberOfCls(0)
, numberOfTotalLiterals( _solver->tot_literals )
, hasLimit( _limited )
, randomOrder(_randomized)
, currentlyInprocessing(false)
, debugging( _debug )
, lastCompressUndoLits(-1)
, decompressedUndoLits(-1)
, log(_log)
{
}

inline void CoprocessorData::init(uint32_t nVars)
{
  occs.resize( nVars * 2 );
  lit_occurrence_count.resize( nVars * 2, 0 );
  numberOfVars = nVars;
  deleteTimer.create( nVars );
  
  //if there is still something in the queues, get rid of it!
  getStrengthClauses().clear();
  getSubsumeClauses().clear();
}

inline void CoprocessorData::destroy()
{
  ComplOcc().swap(occs); // free physical space of the vector
  vector<int32_t>().swap(lit_occurrence_count);
  deleteTimer.destroy();
}

inline vec< CRef >& CoprocessorData::getClauses()
{
  return solver->clauses;
}

inline vec< CRef >& CoprocessorData::getLEarnts()
{
  return solver->learnts;
}

inline vec< Lit >& CoprocessorData::getTrail()
{
  return solver->trail;
}

inline void CoprocessorData::clearTrail()
{
  solver->trail.clear();
  solver->qhead = 0;
}

inline void CoprocessorData::resetPPhead()
{
  solver->qhead = 0;  
}


inline Var CoprocessorData::nextFreshVariable(char type)
{
  // be careful here
  Var nextVar = solver->newVar(true,true,type);
  numberOfVars = solver->nVars();
  ma.resize( 2*nVars() );
  
  deleteTimer.resize( 2*nVars() );
  
  occs.resize( 2*nVars() );
  // cerr << "c resize occs to " << occs.size() << endl;
  lit_occurrence_count.resize( 2 * nVars() );
  
  // cerr << "c new fresh variable: " << nextVar+1 << endl;
  return nextVar;
}

inline void CoprocessorData::moveVar(Var from, Var to, bool final)
{
  if( from != to ) { // move data only if necessary
    solver->varFlags[to].assigns = solver->varFlags[from].assigns; solver->varFlags[from].assigns = l_Undef;
    solver->vardata[to] = solver->vardata[from]; solver->vardata[from] = Solver::VarData();
    solver->activity[to] = solver->activity[from]; solver->activity[from] = 0;
    solver->varFlags[to].seen = solver->varFlags[to].seen; solver->varFlags[to].seen = 0;
    solver->varFlags[to].polarity = solver->varFlags[from].polarity; solver->varFlags[from].polarity = 0;
    solver->varFlags[to].decision = solver->varFlags[from].decision; solver->varFlags[from].decision = false;
    solver->varFlags[to].frozen = solver->varFlags[from].frozen; solver->varFlags[from].frozen = false;
    
    // cp3 structures
    lit_occurrence_count[toInt( mkLit(to, false ))] = lit_occurrence_count[toInt( mkLit(from, false ))];
    lit_occurrence_count[toInt( mkLit(to, true  ))] = lit_occurrence_count[toInt( mkLit(from, true  ))];
    occs[toInt( mkLit(to, false ))].swap( occs[toInt( mkLit(from, false ))] );
    occs[toInt( mkLit(to, true  ))].swap( occs[toInt( mkLit(from, true  ))] );
  }
  if( final == true ) {
  
    // cerr << "c compress variables to " << to+1 << endl;
//     solver->assigns.shrink( solver->assigns.size() - to - 1);
    solver->vardata.shrink( solver->vardata.size() - to - 1);
    solver->activity.shrink( solver->activity.size() - to - 1);
//    solver->seen.shrink( solver->seen.size() - to - 1);
    solver->varFlags.shrink( solver->varFlags.size() - to - 1);
    
    solver->rebuildOrderHeap();
    
    // set cp3 variable representation!
    numberOfVars = solver->nVars();
    lit_occurrence_count.resize( nVars() * 2 );
    occs.resize(nVars() * 2);
  }
}

inline void CoprocessorData::mergeVar( Lit from, Lit to, bool final ){
  
}

inline void CoprocessorData::mergeVar( vector<Lit>& from, Lit to, bool final ){
  
}

inline bool CoprocessorData::ok()
{
  return solver->ok;
}

inline void CoprocessorData::setFailed()
{
  solver->ok = false;
}

inline bool CoprocessorData::unlimited()
{
  return !hasLimit;
}

inline bool CoprocessorData::randomized()
{
  return randomOrder;
}

inline bool CoprocessorData::isInterupted()
{
  return solver->asynch_interrupt;
}


inline lbool CoprocessorData::enqueue(const Lit l, const uint64_t extraInfo)
{
  if( false || global_debug_out ) cerr << "c enqueue " << l << " with previous value " << (solver->value( l ) == l_Undef ? "undef" : (solver->value( l ) == l_False ? "unsat" : " sat ") ) << endl;
  if( solver->value( l ) == l_False) {
    solver->ok = false; // set state to false
    return l_False;
  } else if( solver->value( l ) == l_Undef ) {solver->uncheckedEnqueue(l);
    // if( extraInfo != 0 ) solver.vardata[ var(l) ] ... // make use of extra information!
    return l_True;
  }
  return l_Undef;
}

inline lbool CoprocessorData::value(const Lit l) const
{
 return solver->value( l );
}

inline void CoprocessorData::resetAssignment(const Var v)
{
  solver->varFlags[ v ].assigns = l_Undef;
}


inline Solver* CoprocessorData::getSolver()
{
  return solver;
}


inline bool CoprocessorData::hasToPropagate()
{
  return solver->trail.size() != solver->qhead;
}


inline void CoprocessorData::addClause(const CRef cr, bool check)
{
  const Clause & c = ca[cr];
  if( c.can_be_deleted() ) return;
  for (int l = 0; l < c.size(); ++l)
  {
    // cerr << "c add clause " << cr << " to list for " << c[l] << endl;
    if( check ) {
      for( int i = 0 ; i < occs[toInt(c[l])].size(); ++ i ) {
	if( occs[toInt(c[l])][i] == cr ) {
	  cerr << "c clause " << cr << " is already in list for lit " << c[l] << " clause is: " << ca[cr] << endl; 
	}
      }
    }
    occs[toInt(c[l])].push_back(cr);
    lit_occurrence_count[toInt(c[l])] += 1;
  }
  numberOfCls ++;
}

inline void CoprocessorData::addClause ( const CRef cr , Heap<VarOrderBVEHeapLt> * heap, const bool update, const Var ignore, SpinLock * data_lock, SpinLock * heap_lock) 
{
  const Clause & c = ca[cr];
  if( c.can_be_deleted() ) return;
  if (heap == NULL && data_lock == NULL && heap_lock == NULL)
  {
      for (int l = 0; l < c.size(); ++l)
      {
        occs[toInt(c[l])].push_back(cr);
        lit_occurrence_count[toInt(c[l])] += 1;
      }
      numberOfCls ++;
  }
  else 
  {
      if (data_lock != NULL) data_lock->lock();
      if (heap_lock != NULL) heap_lock->lock();
      for (int l = 0; l < c.size(); ++l)
      {
        occs[toInt(c[l])].push_back(cr);
        lit_occurrence_count[toInt(c[l])] += 1;
        if (heap != NULL) {
            if (heap->inHeap(var(c[l]))) {
                heap->increase(var(c[l]));
	    } else {
	      if (update && var(c[l]) != ignore)
                heap->update(var(c[l]));
	    }
	}
      }	
      if (heap_lock != NULL) heap_lock->unlock();
      numberOfCls ++;
      if (data_lock != NULL) data_lock->unlock();
  }
}

inline bool CoprocessorData::removeClauseFrom(const CRef cr, const Lit l)
{
  vector<CRef>& list = occs[toInt(l)];
  for( int i = 0 ; i < list.size(); ++ i )
  {
    if( list[i] == cr ) {
      list[i] = list[ list.size() - 1 ];
      list.pop_back();
      return true;
    }
  }
  return false;
}

inline void CoprocessorData::removeClauseFrom(const CRef cr, const Lit l, const int index)
{
  vector<CRef>& list = occs[toInt(l)];
  assert( list[index] == cr );
  list[index] = list[ list.size() -1 ];
  list.pop_back();
}

/** replaces clause reference from clause list by CRef_Undef, returns true, if successful
 *  asynchronous list modification
 */
inline bool CoprocessorData::removeClauseFromThreadSafe (const CRef cr, const Lit l) 
{
  assert( cr != CRef_Undef);
  vector<CRef>& list = occs[toInt(l)];
  for( int i = 0 ; i < list.size(); ++ i )
  {
    if( list[i] == cr ) {
      list[i] = CRef_Undef;       
      return true;
    }
  }
  return false;
}

/** removes CRef_Undef from all dirty occurrences
 *  should be used sequentiell or with exclusive occ-access
 *
 *  @param dirtyOccs (on Lits !)
 */
inline void CoprocessorData::cleanUpOccurrences(const MarkArray & dirtyOccs, const uint32_t timer)
{
    for(int l = 0 ; l < dirtyOccs.size() ; ++ l ) {
        if( dirtyOccs.getIndex(l) >= timer ) 
        {
            vector<CRef> & list = occs[l];
            int i = 0; 
            while (i < list.size())
            {
                if (list[i] == CRef_Undef)
                {
                    list[i] = list[list.size() - 1];
                    list.pop_back();
                    continue;
                }
                ++i;
            }
        }
    }
}

inline void CoprocessorData::cleanOccurrences()
{
  for( Var v = 0; v < nVars(); ++v ) {
    list( mkLit(v,false) ).clear(); 
    list( mkLit(v,true) ).clear();
  }
  lit_occurrence_count.assign(0,nVars()*2);
}


inline void CoprocessorData::sortClauseLists(bool alsoLearnts)
{
  for( int p = 0 ; p < (alsoLearnts ? 2 : 1); ++ p ) {
	vec<CRef>& clauseList = (p == 0 ? getClauses() : getLEarnts());
	int32_t n = clauseList.size();
	int32_t m, s;
	// copy elements from vector
	CRef* tmpA = new CRef[ n ];
	CRef* a = tmpA;
	for( int32_t i = 0 ; i < n; i++ ){
		a[i] = clauseList[i];
	}
	CRef *tmpB = new CRef[n];
	CRef *b = tmpB;

	// size of work fields, power of 2	
	for (s=1; s<n; s+=s)
	{
		m = n;
		do {
			m = m - 2*s;	// set begin of working field
			int32_t hi = (m+s > 0) ? m + s : 0;	// set middle of working field
			
			int32_t i = (m > 0) ? m : 0;	// lowest position in field
			int32_t j = hi;
			
			int32_t stopb = m + 2*s;	// upper bound of current work area
			int32_t currentb = i;			// current position in field for copy
			
			// merge two sorted fields into one
			while( i < hi && j < stopb)
			{
				if( ( ca[a[i]] ) < ( ca[a[j]])  )
					b[currentb++] = a[i++];
				else
					b[currentb++] = a[j++];
			}
			// copy rest of the elements
			for( ; i < hi; )
				b[currentb++] = a[i++];
				
			for( ; j< stopb; 	)
				b[currentb++] = a[j++];
				
		} while( m > 0 );
		
		// swap fields!
		CRef* tmp = a;a = b;b = tmp;
	}
	// write data back into vector
	for( int32_t i = 0 ; i < n; i++ ){clauseList[i] = a[i];}
	
	delete [] tmpA;
	delete [] tmpB;
  }
}


inline uint32_t CoprocessorData::getMyDeleteTimer()
{
  return deleteTimer.nextStep();
}

inline void CoprocessorData::deletedVar(const Var v)
{
  deleteTimer.setCurrentStep(v);
}

inline void CoprocessorData::getActiveVariables(const uint32_t myTimer, vector< Var >& activeVariables)
{
  for( Var v = 0 ; v < solver->nVars(); ++ v ) {
    if( deleteTimer.getIndex(v) >= myTimer ) activeVariables.push_back(v);
  }
}


template<class Comp>
inline void CoprocessorData::getActiveVariables(const uint32_t myTimer, Heap< Comp > & heap)
{
  for( Var v = 0 ; v < solver->nVars(); ++ v ) {
    if( deleteTimer.getIndex(v) >= myTimer ) heap.insert(v);
  } 
}

inline void CoprocessorData::resetDeleteTimer()
{
  deleteTimer.reset();
}


inline void CoprocessorData::removedClause(const Lit l1, const Lit l2)
{
  removedLiteral(l1);
  removedLiteral(l2);
  
  const Lit searchLit = lit_occurrence_count[toInt(l1)] < lit_occurrence_count[toInt(l2)] ? l1 : l2;
  const Lit secondLit = toLit(  toInt(l1) ^ toInt(l2) ^ toInt(searchLit) );

  // find the right binary clause and remove it!
  for( int i = 0 ; i < list(searchLit).size(); ++ i ) {
    Clause& cl = ca[list(searchLit)[i]];
    if( cl.can_be_deleted() || cl.size() != 2 ) continue;
    if( cl[0] == secondLit || cl[1] == secondLit ) {
      cl.set_delete(true);
      addCommentToProof("remove binary clause");
      addToProof( cl, true );
      break;
    }
  }
}

inline void CoprocessorData::addedLiteral( const Lit l, const int32_t diff, Heap<VarOrderBVEHeapLt> * heap, const bool update, const Var ignore, SpinLock * data_lock, SpinLock * heap_lock)
{
    if (heap == NULL && data_lock == NULL && heap_lock == NULL)
    {
        lit_occurrence_count[toInt(l)] += diff; 
    }
    else 
    {
        if (data_lock != NULL)
            data_lock->lock();
        if (heap_lock != NULL)
            heap_lock->lock();
        lit_occurrence_count[toInt(l)] += diff;
        if (heap != NULL)
        {
            if (heap->inHeap(var(l)))
                heap->increase(var(l));
            else if (update && var(l) != ignore)
                heap->update(var(l));
        }    
        if (heap_lock != NULL)
            heap_lock->unlock();
        if (data_lock != NULL)
            data_lock->unlock();
    }
}
inline void CoprocessorData::removedLiteral( const Lit l, const int32_t diff, Heap<VarOrderBVEHeapLt> * heap, const bool update, const Var ignore, SpinLock * data_lock, SpinLock * heap_lock) // update counter for literal
{
  if (heap == NULL && data_lock == NULL && heap_lock == NULL)
  {
    deletedVar(var(l));
    lit_occurrence_count[toInt(l)] -= diff;
    ca.freeLit();
    //assert(lit_occurrence_count[toInt(l)] == countLitOcc(l)); 
  }
  else
  {
    if (data_lock != NULL)
        data_lock->lock();
    if (heap_lock != NULL)
        heap_lock->lock();
    deletedVar(var(l));
    lit_occurrence_count[toInt(l)] -= diff;
    ca.freeLit();
    //assert(lit_occurrence_count[toInt(l)] == countLitOcc(l)); 
    if (heap != NULL)
    {
        if (heap->inHeap(var(l)))
            heap->decrease(var(l));
        else if (update && var(l) != ignore)
            heap->update(var(l));
    }
    if (heap_lock != NULL)
        heap_lock->unlock();
    if (data_lock != NULL)
        data_lock->unlock();
  }
}
inline void CoprocessorData::addedClause (   const CRef cr, Heap<VarOrderBVEHeapLt> * heap, const bool update , const Var ignore, SpinLock * data_lock, SpinLock * heap_lock)			// update counters for literals in the clause
{
  const Clause & c = ca[cr];
  if (heap == NULL && data_lock == NULL && heap_lock == NULL)
  {
      for (int l = 0; l < c.size(); ++l)
      {
        lit_occurrence_count[toInt(c[l])] += 1;
      }
      numberOfCls++;
  }
  else 
  {
      if (data_lock != NULL)
        data_lock->lock();
      if (heap_lock != NULL)
        heap_lock->lock();
      for (int l = 0; l < c.size(); ++l)
      {
        lit_occurrence_count[toInt(c[l])] += 1;
        if (heap != NULL)
        {
            if (heap->inHeap(var(c[l])))
                heap->increase(var(c[l]));
            else if (update && var(c[l]) != ignore)
                heap->update(var(c[l]));
        }
      }
      numberOfCls++;
      if (heap_lock != NULL)
          heap_lock->unlock();
      if (data_lock != NULL)
          data_lock->unlock();
  }
}
inline void CoprocessorData::removedClause ( const CRef cr, Heap< Coprocessor::VarOrderBVEHeapLt >* heap, const bool update, const Var ignore, SpinLock* data_lock, SpinLock* heap_lock)			// update counters for literals in the clause
{
  const Clause & c = ca[cr];
  if (heap == NULL && data_lock == NULL && heap_lock == NULL)
  {
      for (int l = 0; l < c.size(); ++l)
      {
        deletedVar(var(c[l]));
        --lit_occurrence_count[toInt(c[l])];
        //assert(lit_occurrence_count[toInt(c[l])] == countLitOcc(c[l]));
      }
      numberOfCls --;
      ca.free(cr);
  }
  else
  {
      if (data_lock != NULL)
        data_lock->lock();
      if (heap_lock != NULL)
        heap_lock->lock();
      for (int l = 0; l < c.size(); ++l)
      {
        deletedVar(var(c[l]));
        --lit_occurrence_count[toInt(c[l])];
        //assert(lit_occurrence_count[toInt(c[l])] == countLitOcc(c[l]));
        
        if (heap != NULL)
        {
            if (heap->inHeap(var(c[l])))
                heap->decrease(var(c[l]));
            else if (update && var(c[l]) != ignore)
                heap->update(var(c[l]));
        }
      }
      numberOfCls --;
      ca.free(cr);
      if (heap_lock != NULL)
          heap_lock->unlock();
      if (data_lock != NULL)
          data_lock->unlock();
  }
} 

inline int32_t& CoprocessorData::operator[](const Lit l)
{
  return lit_occurrence_count[toInt(l)];
}

inline int32_t CoprocessorData::operator[](const Var v) const
{
  return lit_occurrence_count[toInt(mkLit(v,0))] + lit_occurrence_count[toInt(mkLit(v,1))];
}

inline vector< CRef >& CoprocessorData::list(const Lit l)
{
   return occs[ toInt(l) ];
}

inline const vector< CRef >& CoprocessorData::list(const Lit l) const
{
   return occs[ toInt(l) ];
}

inline void CoprocessorData::correctCounters()
{
  numberOfVars = solver->nVars();
  numberOfCls = 0;
  // reset to 0
  for (int v = 0; v < solver->nVars(); v++)
    for (int s = 0; s < 2; s++)
      lit_occurrence_count[ toInt(mkLit(v,s)) ] = 0;
  // re-calculate counters!
  for( int i = 0 ; i < solver->clauses.size(); ++ i ) {
    const Clause & c = ca[ solver->clauses[i] ];
    if( c.can_be_deleted() ) continue;
    numberOfCls ++;
    for( int j = 0 ; j < c.size(); j++) lit_occurrence_count[ toInt(c[j]) ] ++; // increment all literal counters accordingly
  }
  for( int i = 0 ; i < solver->learnts.size(); ++ i ) {
    const Clause & c = ca[ solver->learnts[i] ];
    if( c.can_be_deleted() ) continue;
    numberOfCls ++;
    for( int j = 0 ; j < c.size(); j++) lit_occurrence_count[ toInt(c[j]) ] ++; // increment all literal counters accordingly
  }
}

inline void CoprocessorData::garbageCollect(vector<CRef> ** updateVectors, int size) 
{
  if( debugging ) {
    cerr << "c check garbage collection [REJECTED DUE TO DEBUGGING] " << endl;
    return;
  }
    ClauseAllocator to((ca.size() >= ca.wasted()) ? ca.size() - ca.wasted() : 0);  //FIXME just a workaround
                                                                                   // correct add / remove would be nicer
    
    cerr << "c garbage collection ... " << endl;
    relocAll(to, updateVectors);
    cerr << "c Garbage collection: " << ca.size()*ClauseAllocator::Unit_Size 
         << " bytes => " << to.size()*ClauseAllocator::Unit_Size <<  " bytes " << endl; 
    
    to.moveTo(ca);
}

inline void CoprocessorData::relocAll(ClauseAllocator& to, vector<CRef> ** updateVectors, int size)
{
    // Update Vectors
    if (size > 0 && updateVectors != 0)
    {
        for (int v_ix = 0; v_ix < size; ++v_ix)
        {
            if (updateVectors[v_ix] == 0)
                continue;
            vector<CRef> & list = *(updateVectors[v_ix]);
            int i, j;
            for (i = j = 0; i < list.size(); ++i){
                Clause & c = ca[list[i]];
                if (c.can_be_deleted()) {
                    // removeClause(list[i]);
                }
                else
                {
                    ca.reloc(list[i], to);
                    list[j++] = list[i];
                }
            }
            list.resize(j);
        }    
    }

    // Subsume Queue
    {
        int i, j;
        for (i = j = 0; i < subsume_queue.size(); ++i){
            Clause & c = ca[subsume_queue[i]];
            if (c.can_be_deleted()) {
                // removeClause(subsume_queue[i]);
            }
            else
            {
                ca.reloc(subsume_queue[i], to);
                subsume_queue[j++] = subsume_queue[i];
            }
        }
        subsume_queue.resize(j);
    }
    // Strength Queue
    {
        int i, j;
        for (i = j = 0; i < strengthening_queue.size(); ++i){
            Clause & c = ca[strengthening_queue[i]];
            if (c.can_be_deleted()) {
                // removeClause(strength_queue[i]);
            }
            else
            {
                ca.reloc(strengthening_queue[i], to);
                strengthening_queue[j++] = strengthening_queue[i];
            }
        }
        strengthening_queue.resize(j);
    }

    // All Occurrences
    for (int v = 0 ; v < nVars(); ++ v)
    {
        for (int i = 0 ; i < 2; ++i)
        {
            vector<CRef> & litOccs = list(mkLit(v, ((i == 0) ? false : true)));
            int j, k;
            for (j = k = 0; j < litOccs.size(); ++j)
            {
                if (litOccs[j] == CRef_Undef)
                    continue;
                Clause & c = ca[litOccs[j]];
                if (c.can_be_deleted()) {
                    //removeClause(litOccs[j]);
                } 
                else
                {
                    ca.reloc(litOccs[j], to);
                    litOccs[k++] = litOccs[j];
                }
            }
            litOccs.resize(k);
        }
    }
    // Watches are clean!

    // All reasons:
    //
    for (int i = 0; i < solver->trail.size(); i++){
        Var v = var(solver->trail[i]);
	// FIXME TODO: there needs to be a better workaround for this!!
	if ( solver->level(v) == 0 ) solver->vardata[v].reason = CRef_Undef; // take care of reason clauses for literals at top-level
        else
        if (solver->reason(v) != CRef_Undef && (ca[solver->reason(v)].reloced() || solver->locked(ca[solver->reason(v)])))
            ca.reloc(solver->vardata[v].reason, to);
    }

    vec<CRef> & clauses = solver->clauses;
    vec<CRef> & learnts = solver->learnts;

    // All original:
    //
    {
        int i, j;
        for (i = j = 0; i < clauses.size(); ++i){
            Clause & c = ca[clauses[i]];
            if (c.can_be_deleted()) {
                // removeClause(clauses[i]);
            }
            else
            {
                ca.reloc(clauses[i], to);
                clauses[j++] = clauses[i];
            }
        }
        clauses.shrink(i - j);
    }
    // All learnt:
    //
    {
        int i, j;
        for (i = j = 0; i < learnts.size(); ++i){
            Clause & c = ca[learnts[i]];
            if (c.can_be_deleted()) {
                // removeClause(learnts[i]);
            }
            else if (!c.learnt())
            {
                ca.reloc(learnts[i], to);
                clauses.push(learnts[i]);
            }
            else
            {
                ca.reloc(learnts[i], to);
                learnts[j++] = learnts[i];
            }
        }
        learnts.shrink(i - j);
    }
}

/** Mark all variables that occure together with _x_.
 *
 * @param x the variable to start with
 * @param array the mark array in which the marks are set
 */
inline void CoprocessorData::mark1(Var x, MarkArray& array)
{
  std::vector<CRef> & clauses = occs[toInt( mkLit(x,true))];
  for( int i = 0; i < clauses.size(); ++i)
  {
    CRef cr = clauses[i];
    Clause &c = ca[cr];
    for (int j = 0; j < c.size(); ++j)
    {
      array.setCurrentStep(var(c[j]));
    }
  }
  clauses = occs[toInt( mkLit(x,false) )];
  for( int i = 0; i < clauses.size(); ++i)
  {
    CRef cr = clauses[i];
    Clause &c = ca[cr];
    for (int j = 0; j < c.size(); ++j)
    {
      array.setCurrentStep(var(c[j]));
    }
  }
}

/** Marks all variables that occure together with x or with one of x's direct neighbors.
 *
 * mark2 marks all variables in two steps from x. That means, all variables that can be reched
 * in the adjacency graph of variables within two steps.
 *
 * @param x the variable to start from
 * @param array the mark array which contains the marks as result
 * @param tmp an array used for internal compution (temporary)
 */
inline void CoprocessorData::mark2(Var x, MarkArray& array, MarkArray& tmp)
{
  tmp.nextStep();
  // for negative literal
  std::vector<CRef> & clauses = occs[toInt( mkLit(x,true))];
  for( int i = 0; i < clauses.size(); ++i)
  {
    Clause &c = ca[clauses[i]];
    // for l in C
    for (int l = 0; l < c.size(); ++l)
    {
      if( !tmp.isCurrentStep(var(c[l])) )
      {
        mark1(var(c[l]), array);
      }
      tmp.setCurrentStep(var(c[l]));
    }
  }
  // for positive literal
  clauses = occs[toInt( mkLit(x,false))];
  for( int i = 0; i < clauses.size(); ++i)
  {
    Clause &c = ca[clauses[i]];
    for (int l = 0; l < c.size(); ++l)
    {
      if( !tmp.isCurrentStep(var(c[l])) )
      {
        mark1(var(c[l]), array);
      }
      tmp.setCurrentStep(var(c[l]));
    }
  }
}

inline void CoprocessorData::addToExtension(const CRef cr, const Lit l)
{
  const Clause& c = ca[cr];
  if( undo.size() > 0 ) assert( undo[ undo.size() - 1] != lit_Undef && "an empty clause should not be put on the undo stack" );
  undo.push_back(lit_Undef);
  if( l != lit_Error ) undo.push_back(l);
  for( int i = 0 ; i < c.size(); ++ i ) {
    if( c[i] != l ) undo.push_back(c[i]);
  }
}

inline void CoprocessorData::addToExtension(vec< Lit >& lits, const Lit l)
{
  if( undo.size() > 0 ) assert( undo[ undo.size() - 1] != lit_Undef && "an empty clause should not be put on the undo stack" );
  undo.push_back(lit_Undef);
  if( l != lit_Error ) undo.push_back(l);
  for( int i = 0 ; i < lits.size(); ++ i ) {
    if( lits[i] != l ) undo.push_back(lits[i]);
  }
}

inline void CoprocessorData::addToExtension(vector< Lit >& lits, const Lit l)
{
  if( undo.size() > 0 ) assert( undo[ undo.size() - 1] != lit_Undef && "an empty clause should not be put on the undo stack" );
  undo.push_back(lit_Undef);
  if( l != lit_Error ) undo.push_back(l);
  for( int i = 0 ; i < lits.size(); ++ i ) {
    if( lits[i] != l ) undo.push_back(lits[i]);
  }
}

inline void CoprocessorData::addToExtension(const Lit dontTouch, const Lit l)
{
  if( undo.size() > 0 ) assert( undo[ undo.size() - 1] != lit_Undef && "an empty clause should not be put on the undo stack" );
  undo.push_back(lit_Undef);
  if( l != lit_Error) undo.push_back(l);
  undo.push_back(dontTouch);
}

// TODO: use template!
inline void CoprocessorData::addExtensionToExtension(vec< Lit >& lits)
{
  for( int i = 0 ; i < lits.size(); ++ i ) {
    undo.push_back(lits[i]);
  }
}

inline void CoprocessorData::addExtensionToExtension(vector< Lit >& lits)
{
  for( int i = 0 ; i < lits.size(); ++ i ) {
    undo.push_back(lits[i]);
  }
}

inline void CoprocessorData::extendModel(vec< lbool >& model)
{
  if( lastCompressUndoLits != -1 &&  // if there has been a  compression,
      decompressedUndoLits != undo.size() ) { // then the complete undo-stack has to be adopted
    cerr << "c variable renaming went wrong - abort. lastCom: " << lastCompressUndoLits << " decomp: " << decompressedUndoLits << " undo: " << undo.size() << endl;
    exit(13);
  }
  
  for( int j = 0 ; j < model.size(); ++ j ) {
	  if( model[j] == l_Undef ) model[j] = l_True; // set free variables to some value
  }
  
  const bool local_debug = false;
  if( true && (global_debug_out || local_debug) ) {
    cerr << "c extend model of size " << model.size() << " with undo information of size " << undo.size() << endl;
    cerr << "c in model: ";
	for( int j = 0 ; j < model.size(); ++ j ) {
	  if( model[j] == l_Undef ) cerr << "? ";
	  else {
	    const Lit satLit = mkLit( j, model[j] == l_True ? false : true );
	    cerr << satLit << " ";
	  }
	}
	cerr << endl;
  }
  
  if( false && local_debug ) {
    cerr << "extend Stack: " << endl; 
    for( int i = undo.size() - 1; i >= 0 ; --i ) {
      if( undo[i] == lit_Undef ) cerr << endl;
      else cerr << " " << undo[i];
    }
    
    
    cerr << "next clause: ";
    for( int j = undo.size() - 1; j >= 0 ; --j ) if( undo[j] == lit_Undef ) break; else cerr << " " << undo[j];
    cerr << endl;

  }

  // check current clause for being satisfied
  bool isSat = false; // FIXME: this bool is redundant!
  for( int i = undo.size() - 1; i >= 0 ; --i ) {
    
     isSat = false; // init next clause - redundant!
     const Lit c = undo[i]; // check current literal
     if( global_debug_out  || local_debug) cerr << "c read literal " << c << endl;
     if( c == lit_Undef ) {  // found clause delimiter, without jumping over it in the SAT case (below)
       if( !isSat ) {        // this condition is always satisfied -- the current clause has to be unsatisfied (otherwise, would have been ignored below!)
         // if clause is not satisfied, satisfy last literal!
         const Lit& satLit = undo[i+1];
	 assert( satLit != lit_Undef && "there should not be an empty clause on the undo stack" );
         log.log(1, "set literal to true",satLit);
	 if( local_debug ) cerr << "c set literal " << undo[i+1] << " to true " << endl;
         model[ var(satLit) ] = sign(satLit) ? l_False : l_True;
       }
       
       // finished this clause!
       if( local_debug ) { // print intermediate state!
       cerr << "c current model: ";
	for( int j = 0 ; j < model.size(); ++ j ) {
	  if( model[j] == l_Undef ) cerr << "? ";
	  else {
	    const Lit satLit = mkLit( j, model[j] == l_True ? false : true );
	    cerr << satLit << " ";
	  }
	}
	cerr << endl;
        cerr << "next clause: ";
	for( int j = i - 1; j >= 0 ; --j ) if( undo[j] == lit_Undef ) break; else cerr << " " << undo[j];
	cerr << endl;
       }
       continue;
     }
     if( var(c) >= model.size() ) model.growTo( var(c) + 1, l_True ); // model is too small? this will also take care of extended resolution variables!
     if (model[var(c)] == (sign(c) ? l_False : l_True) ) // satisfied
     {
       isSat = true; // redundant -- will be reset in the next loop iteration immediately
       while( undo[i] != lit_Undef ){ // skip literal until hitting the delimiter - for loop will decrease i once more
	 if( global_debug_out  || local_debug) cerr << "c skip because SAT: " << undo[i] << endl; 
	 --i;
       }
       if( local_debug ) { // print intermediate state!
        cerr << "next clause: ";
	for( int j = i - 1; j >= 0 ; --j ) if( undo[j] == lit_Undef ) break; else cerr << " " << undo[j];
	cerr << endl;
       }
     }
  }

  if( global_debug_out  || local_debug) {
    cerr << "c out model: ";
    for( int i = 0 ; i < model.size(); ++ i ) {
      const Lit satLit = mkLit( i, model[i] == l_True ? false : true );
      cerr << satLit << " ";
    }
    cerr << endl;
  }
}

#ifdef DRATPROOF
template <class T>
inline void CoprocessorData::addToProof(T& clause, bool deleteFromProof, const Lit remLit)
{
  solver->addToProof(clause,deleteFromProof,remLit);
}

inline void CoprocessorData::addUnitToProof(const Lit& l, bool deleteFromProof)
{
  solver->addUnitToProof(l,deleteFromProof);
}

inline void CoprocessorData::addCommentToProof(const char* text, bool deleteFromProof)
{
  solver->addCommentToProof(text,deleteFromProof);
}
#endif

inline void CoprocessorData::addEquivalences(const vector< Lit >& list)
{
  assert( (list.size() != 2 || list[0] != list[1]) && "do not allow to add a pair of the same literals" );
  for( int i = 0 ; i < list.size(); ++ i ) equivalences.push_back(list[i]);
  equivalences.push_back( lit_Undef ); // termination symbol!
}

inline void CoprocessorData::addEquivalences(const Lit& l1, const Lit& l2)
{
  assert( l1 != l2 && "do not state that the same literal is equivalent to itself" );
  if( global_debug_out ) cerr << "c [DATA] set equi: " << l1 << " == " << l2 << endl;
  equivalences.push_back(l1);
  equivalences.push_back(l2);
  equivalences.push_back( lit_Undef ); // termination symbol!
}

inline vector< Lit >& CoprocessorData::getEquivalences()
{
  return equivalences;
}

inline bool CoprocessorData::addSubStrengthClause(const CRef cr, bool isNew)
{
  bool ret = false;
  Clause& c = ca[cr];
  if( !c.can_strengthen() || isNew ) {
    c.set_strengthen(true); 
    strengthening_queue.push_back(cr);
    ret = true;
  }
  if( !c.can_subsume() || isNew) {
    c.set_subsume(true); 
    subsume_queue.push_back(cr);
    ret = true;
  }
  return ret;
}

inline vector< CRef >& CoprocessorData::getSubsumeClauses()
{
  return subsume_queue;
}


inline vector<CRef>& CoprocessorData::getStrengthClauses()
{
  return strengthening_queue; 
}


inline void CoprocessorData::setNotTouch(const Var& v)
{
  solver->freezeVariable(v,true);
}

inline bool CoprocessorData::doNotTouch(const Var& v) const
{
  return solver->isFrozen(v);
}

bool inline CoprocessorData::removeClauseThreadSafe (const CRef cr)
{
    Clause & c = ca[cr];
    c.spinlock();
    if (!c.can_be_deleted())
    {
        c.set_delete(true);
        while ( __sync_bool_compare_and_swap(&numberOfCls, numberOfCls, numberOfCls-1) == false) {};
        for (int l = 0; l < c.size(); ++l)
        {
            int32_t old_count, new_count;
            Lit lit = c[l];
            do {
                old_count = lit_occurrence_count[toInt(lit)];
                new_count = old_count - 1;  
            } while ( __sync_bool_compare_and_swap(&lit_occurrence_count[toInt(lit)], old_count, new_count) == false);
        }
        c.unlock();
        return true;
    } 
    else
    {
        c.unlock();
        return false;
    }
}

inline BIG::BIG()
: storage(0), sizes(0), big(0), start(0), stop(0), duringCreationVariables(0)
{}

inline BIG::~BIG()
{
 if( big != 0 )    { free( big ); big = 0; }
 if( storage != 0 ){ free( storage ); storage = 0; }
 if( sizes != 0 )  { free( sizes ); sizes = 0 ; }
 if( start != 0 ) { free( start ); start = 0; }
 if( stop != 0 ) { free( stop ); stop = 0; }
 
}

inline void BIG::create(ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list)
{
  duringCreationVariables = nVars; // memorize the number of present variables
  sizes = (int*) malloc( sizeof(int) * nVars * 2 );
  memset(sizes,0, sizeof(int) * nVars * 2 );

  int sum = 0;
  // count occurrences of literals in binary clauses of the given list
  for( int i = 0 ; i < list.size(); ++i ) {
    const Clause& c = ca[list[i]];
    if(c.size() != 2 || c.can_be_deleted() ) continue;
    sizes[ toInt( ~c[0] )  ] ++;
    sizes[ toInt( ~c[1] )  ] ++;
    sum += 2;
  }
  storage = (Lit*) malloc( sizeof(Lit) * sum );
  big =  (Lit**)malloc ( sizeof(Lit*) * nVars * 2 );
  // memset(sizes,0, sizeof(Lit*) * nVars * 2 );
  // set the pointers to the right location and clear the size
  sum = 0 ;
  for ( int i = 0 ; i < nVars * 2; ++ i )
  {
    big[i] = &(storage[sum]);
    sum += sizes[i];
    sizes[i] = 0;
  }

  // add all binary clauses to graph
  for( int i = 0 ; i < list.size(); ++i ) {
    const Clause& c = ca[list[i]];
    if(c.size() != 2 || c.can_be_deleted() ) continue;
    const Lit l0 = c[0]; const Lit l1 = c[1];
    
    ( big[ toInt(~l0) ] )[ sizes[toInt(~l0)] ] = l1;
    ( big[ toInt(~l1) ] )[ sizes[toInt(~l1)] ] = l0;
    sizes[toInt(~l0)] ++;
    sizes[toInt(~l1)] ++;
  }
}

inline void BIG::create(ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list1, vec< CRef >& list2)
{
  duringCreationVariables = nVars; // memorize the number of present variables
  sizes = (int*) malloc( sizeof(int) * nVars * 2 );
  memset(sizes,0, sizeof(int) * nVars * 2 );

  int sum = 0;
  // count occurrences of literals in binary clauses of the given list
  for( int p = 0 ; p < 2; ++ p ) {
    const vec<CRef>& list = (p==0 ? list1 : list2 );
    for( int i = 0 ; i < list.size(); ++i ) {
      const Clause& c = ca[list[i]];
      if(c.size() != 2 || c.can_be_deleted() ) continue;
      sizes[ toInt( ~c[0] )  ] ++;
      sizes[ toInt( ~c[1] )  ] ++;
      sum += 2;
    }
  }
  storage = (Lit*) malloc( sizeof(Lit) * sum );
  big =  (Lit**)malloc ( sizeof(Lit*) * nVars * 2 );
  // memset(sizes,0, sizeof(Lit*) * nVars * 2 );
  // set the pointers to the right location and clear the size
  sum = 0 ;
  for ( int i = 0 ; i < nVars * 2; ++ i )
  {
    big[i] = &(storage[sum]);
    sum += sizes[i];
    sizes[i] = 0;
  }

  // add all binary clauses to graph
  for( int p = 0 ; p < 2; ++ p ) {
    const vec<CRef>& list = (p==0 ? list1 : list2 );
    for( int i = 0 ; i < list.size(); ++i ) {
      const Clause& c = ca[list[i]];
      if(c.size() != 2 || c.can_be_deleted() ) continue;
      const Lit l0 = c[0]; const Lit l1 = c[1];
      ( big[ toInt(~l0) ] )[ sizes[toInt(~l0)] ] = l1;
      ( big[ toInt(~l1) ] )[ sizes[toInt(~l1)] ] = l0;
      sizes[toInt(~l0)] ++;
      sizes[toInt(~l1)] ++;
    }
  }
}


inline void BIG::recreate( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list)
{
  duringCreationVariables = nVars; // memorize the number of present variables
  sizes = sizes == 0 ? (int*) malloc( sizeof(int) * nVars * 2 ) : (int*) realloc( sizes, sizeof(int) * nVars * 2 );
  memset(sizes,0, sizeof(int) * nVars * 2 );

  int sum = 0;
  // count occurrences of literals in binary clauses of the given list
  for( int i = 0 ; i < list.size(); ++i ) {
    const Clause& c = ca[list[i]];
    if(c.size() != 2 || c.can_be_deleted() ) continue;
    sizes[ toInt( ~c[0] )  ] ++;
    sizes[ toInt( ~c[1] )  ] ++;
    sum += 2;
  }
  storage = storage == 0 ? (Lit*) malloc( sizeof(Lit) * sum ) : (Lit*) realloc( storage, sizeof(Lit) * sum )  ;
  big = big == 0 ? (Lit**)malloc ( sizeof(Lit*) * nVars * 2 ) : (Lit**)realloc ( big, sizeof(Lit*) * nVars * 2 );
  // should not be necessary!
  memset(storage,0, sizeof(Lit) * sum );
  memset(big, 0, sizeof(Lit*) * nVars * 2 ); 
  
  // set the pointers to the right location and clear the size
  sum = 0 ;
  for ( int i = 0 ; i < nVars * 2; ++ i )
  {
    big[i] = &(storage[sum]);
    sum += sizes[i];
    sizes[i] = 0;
  }

  // add all binary clauses to graph
  for( int i = 0 ; i < list.size(); ++i ) {
    const Clause& c = ca[list[i]];
    if(c.size() != 2 || c.can_be_deleted() ) continue;
    const Lit l0 = c[0]; const Lit l1 = c[1];
    ( big[ toInt(~l0) ] )[ sizes[toInt(~l0)] ] = l1;
    ( big[ toInt(~l1) ] )[ sizes[toInt(~l1)] ] = l0;
    sizes[toInt(~l0)] ++;
    sizes[toInt(~l1)] ++;
  }
}

inline void BIG::recreate( ClauseAllocator& ca, uint32_t nVars, vec< CRef >& list1, vec< CRef >& list2)
{
  duringCreationVariables = nVars; // memorize the number of present variables
  sizes = sizes == 0 ? (int*) malloc( sizeof(int) * nVars * 2 ) : (int*) realloc( sizes, sizeof(int) * nVars * 2 );
  memset(sizes,0, sizeof(int) * nVars * 2 );

  int sum = 0;
  // count occurrences of literals in binary clauses of the given list
  for( int p = 0 ; p < 2; ++ p ) {
    const vec<CRef>& list = (p==0 ? list1 : list2 );
    for( int i = 0 ; i < list.size(); ++i ) {
      const Clause& c = ca[list[i]];
      if(c.size() != 2 || c.can_be_deleted() ) continue;
      sizes[ toInt( ~c[0] )  ] ++;
      sizes[ toInt( ~c[1] )  ] ++;
      sum += 2;
    }
  }
  storage = storage == 0 ? (Lit*) malloc( sizeof(Lit) * sum ) : (Lit*) realloc( storage, sizeof(Lit) * sum )  ;
  big = big == 0 ? (Lit**)malloc ( sizeof(Lit*) * nVars * 2 ) : (Lit**)realloc ( big, sizeof(Lit*) * nVars * 2 );
  // should not be necessary!
  memset(storage,0, sizeof(Lit) * sum );
  memset(big, 0, sizeof(Lit*) * nVars * 2 ); 
  
  // set the pointers to the right location and clear the size
  sum = 0 ;
  for ( int i = 0 ; i < nVars * 2; ++ i )
  {
    big[i] = &(storage[sum]);
    sum += sizes[i];
    sizes[i] = 0;
  }

  // add all binary clauses to graph
  for( int p = 0 ; p < 2; ++ p ) {
    const vec<CRef>& list = (p==0 ? list1 : list2 );
    for( int i = 0 ; i < list.size(); ++i ) {
      const Clause& c = ca[list[i]];
      if(c.size() != 2 || c.can_be_deleted() ) continue;
      const Lit l0 = c[0]; const Lit l1 = c[1];
      ( big[ toInt(~l0) ] )[ sizes[toInt(~l0)] ] = l1;
      ( big[ toInt(~l1) ] )[ sizes[toInt(~l1)] ] = l0;
      sizes[toInt(~l0)] ++;
      sizes[toInt(~l1)] ++;
    }
  }
}

inline void BIG::removeDuplicateEdges(const uint32_t nVars)
{
  const uint32_t maxVar = duringCreationVariables < nVars ? duringCreationVariables : nVars; // use only known variables
  for( Var v = 0 ; v < maxVar; ++v ) {
    for( int p = 0 ;p < 2 ; ++ p ) {
      const Lit l = mkLit(v,p==1);
      if( getSize(l) == 0 ) continue; // not for empty lists!
      ::sort( getArray(l), getSize(l) );
      int j = 0;
      for( int i = 1; i < getSize(l); ++i ) {
	assert( getArray(l)[i-1] <= getArray(l)[i] && "implication list should be ordered" );
	if( getArray(l)[i] != getArray(l)[j] ) getArray(l)[++j] = getArray(l)[i]; // keep elements, if they are not equal to the last element!
      }
      sizes[ toInt(l) ] = j+1; // update size information
    }
  }
}

inline void BIG::sort(const uint32_t nVars){
  const uint32_t maxVar = duringCreationVariables < nVars ? duringCreationVariables : nVars; // use only known variables
  for( Var v = 0 ; v < maxVar; ++v ) {
    for( int p = 0 ;p < 2 ; ++ p ) {
      const Lit l = mkLit(v,p==1);
      if( getSize(l) == 0 ) continue; // not for empty lists!
      ::sort( getArray(l), getSize(l) );
    }
  }
}

inline void BIG::removeEdge(const Lit l0, const Lit l1)
{
  // remove literal from the two lists
  Lit* list = getArray( ~l0 );
  const uint32_t size = getSize( ~l0 );
  for( int i = 0 ; i < size; ++i )
  {
    if( list[i] == l1 ) {
      list[i] = list[ size - 1 ];
      sizes[ toInt(~l0) ] --;
       //cerr << "c removed edge " << ~l0 << " -> " << l1 << endl;
      break;
    }
  }
  Lit* list2 = getArray( ~l1 );
  const uint32_t size2 = getSize( ~l1 );
  for( int i = 0 ; i < size2; ++i )
  {
    if( list2[i] == l0 ) {
      list2[i] = list2[ size2 - 1 ];
      sizes[ toInt(~l1) ] --;
//        //cerr << "c removed edge " << ~l1 << " -> " << l0 << endl;
      break;
    }
  }
}

inline Lit* BIG::getArray(const Lit l)
{
  return var(l) < duringCreationVariables ? big[ toInt(l) ] : 0;
}

inline const Lit* BIG::getArray(const Lit l) const
{
  return var(l) < duringCreationVariables ? big[ toInt(l) ] : 0;
}

inline int BIG::getSize(const Lit l) const
{
  return var(l) < duringCreationVariables ? sizes[ toInt(l) ] : 0;
}

inline void BIG::generateImplied( CoprocessorData& data )
{
    uint32_t stamp = 1 ;
    const uint32_t maxVar = duringCreationVariables < data.nVars() ? duringCreationVariables : data.nVars(); // use only known variables

    if( start == 0 ) start = (uint32_t*) malloc( maxVar * sizeof(uint32_t) * 2 );
    else start = (uint32_t*)realloc( start, maxVar * sizeof(uint32_t) * 2 );

    if( stop == 0 ) stop = (uint32_t*) malloc( maxVar * sizeof(uint32_t) * 2 );
    else stop = (uint32_t*)realloc( stop, maxVar * sizeof(int32_t) * 2 );

    int32_t* index = (int32_t*)malloc( maxVar * sizeof(int32_t) * 2 );

    // set everything to 0!
    memset( start, 0, maxVar * sizeof(uint32_t) * 2 );
    memset( stop, 0, maxVar * sizeof(uint32_t) * 2 );
    memset( index, 0, maxVar * sizeof(int32_t) * 2 );


    deque< Lit > stampQueue;

    data.lits.clear();
    // reset all present variables, collect all roots in binary implication graph
    for ( Var v = 0 ; v < maxVar; ++ v )
    {
      const Lit pos =  mkLit(v,false);
      // a literal is a root, if its complement does not imply a literal
      if( getSize(pos) == 0 ) data.lits.push_back(~pos);
      if( getSize(~pos) == 0 ) data.lits.push_back(pos);
    }

    // do stamping for all roots, shuffle first
    const uint32_t ts = data.lits.size();
    for( uint32_t i = 0 ; i < ts; i++ ) { const uint32_t rnd=rand()%ts; const Lit tmp = data.lits[i]; data.lits[i] = data.lits[rnd]; data.lits[rnd]=tmp; }
    // stamp shuffled data.lits
    for ( uint32_t i = 0 ; i < ts; ++ i )
      stamp = stampLiteral(data.lits[i],stamp,index,stampQueue);

    // stamp all remaining literals, after shuffling
    data.lits.clear();
    for ( Var v = 0 ; v < maxVar; ++ v )
    {
      const Lit pos =  mkLit(v,false);
      if( start[ toInt(pos) ] == 0 ) data.lits.push_back(pos);
      if( start[ toInt(~pos) ] == 0 ) data.lits.push_back(~pos);
    }
    // stamp shuffled data.lits
    const uint32_t ts2 = data.lits.size();
    for( uint32_t i = 0 ; i < ts2; i++ ) { const uint32_t rnd=rand()%ts2; const Lit tmp = data.lits[i]; data.lits[i] = data.lits[rnd]; data.lits[rnd]=tmp; }
    for ( uint32_t i = 0 ; i < ts2; ++ i )
      stamp = stampLiteral(data.lits[i],stamp,index,stampQueue);
    free(index);
}

inline void BIG::generateImplied( uint32_t nVars, vec<Lit>& tmpLits )
{
    uint32_t stamp = 1 ;
    const uint32_t maxVar = duringCreationVariables < nVars ? duringCreationVariables : nVars; // use only known variables
    
    if( start == 0 ) start = (uint32_t*) malloc( maxVar * sizeof(uint32_t) * 2 );
    else start = (uint32_t*)realloc( start, maxVar * sizeof(uint32_t) * 2 );

    if( stop == 0 ) stop = (uint32_t*) malloc( maxVar * sizeof(uint32_t) * 2 );
    else stop = (uint32_t*)realloc( stop, maxVar * sizeof(int32_t) * 2 );

    int32_t* index = (int32_t*)malloc( maxVar * sizeof(int32_t) * 2 );

    // set everything to 0!
    memset( start, 0, maxVar * sizeof(uint32_t) * 2 );
    memset( stop, 0, maxVar * sizeof(uint32_t) * 2 );
    memset( index, 0, maxVar * sizeof(int32_t) * 2 );


    deque< Lit > stampQueue;

    tmpLits.clear();
    // reset all present variables, collect all roots in binary implication graph
    for ( Var v = 0 ; v < maxVar; ++ v )
    {
      const Lit pos =  mkLit(v,false);
      // a literal is a root, if its complement does not imply a literal
      if( getSize(pos) == 0 ) tmpLits.push(~pos);
      if( getSize(~pos) == 0 ) tmpLits.push(pos);
    }

    // do stamping for all roots, shuffle first
    const uint32_t ts = tmpLits.size();
    for( uint32_t i = 0 ; i < ts; i++ ) { const uint32_t rnd=rand()%ts; const Lit tmp = tmpLits[i]; tmpLits[i] = tmpLits[rnd]; tmpLits[rnd]=tmp; }
    // stamp shuffled tmpLits
    for ( uint32_t i = 0 ; i < ts; ++ i )
      stamp = stampLiteral(tmpLits[i],stamp,index,stampQueue);

    // stamp all remaining literals, after shuffling
    tmpLits.clear();
    for ( Var v = 0 ; v < maxVar; ++ v )
    {
      const Lit pos =  mkLit(v,false);
      if( start[ toInt(pos) ] == 0 ) tmpLits.push(pos);
      if( start[ toInt(~pos) ] == 0 ) tmpLits.push(~pos);
    }
    // stamp shuffled tmpLits
    const uint32_t ts2 = tmpLits.size();
    for( uint32_t i = 0 ; i < ts2; i++ ) { const uint32_t rnd=rand()%ts2; const Lit tmp = tmpLits[i]; tmpLits[i] = tmpLits[rnd]; tmpLits[rnd]=tmp; }
    for ( uint32_t i = 0 ; i < ts2; ++ i )
      stamp = stampLiteral(tmpLits[i],stamp,index,stampQueue);
    
    tmpLits.clear(); // clean up
    free(index);
}

inline void BIG::fillSorted(vector<Lit>& literals, CoprocessorData& data, bool rootsOnly, bool getAll)
{
  literals.clear();
  const uint32_t maxVar = duringCreationVariables < data.nVars() ? duringCreationVariables : data.nVars(); // use only known variables
  data.ma.resize( maxVar *2 );
  data.ma.nextStep();
  
  // put root nodes in queue
  for( Var v = 0 ; v < maxVar; ++ v )
  {
    if( getSize( mkLit(v,false) ) == 0 )
      if( getSize( mkLit(v,true) ) == 0 ) continue;
      else { 
	data.ma.setCurrentStep( toInt(mkLit(v,true)) );
	literals.push_back( mkLit(v,true) ); // tthis is a root node
      }
    else if( getSize( mkLit(v,true) ) == 0 ) {
      data.ma.setCurrentStep( toInt(mkLit(v,false)) );
      literals.push_back( mkLit(v,false) ); // tthis is a root node
    }
  }
  
  // shuffle root nodes
  for( int i = 0 ; i + 1 < literals.size(); ++ i )
  {
    const Lit tmp = literals[i];
    const int rndInd = rand() % literals.size();
    literals[i] = literals[ rndInd ];
    literals[ rndInd ] = tmp;
  }
  
  if( rootsOnly ) return;
  
  // perform BFS
  data.ma.nextStep();
  for( int i = 0 ; i < literals.size(); ++ i ) {
    const Lit l = literals[i];
    Lit* lits = getArray(l);
    int s = getSize(l);
    for( int j = 0 ; j < s; ++ j ) {
      const Lit l2 = lits[j];
      // each literal only once!
      if( data.ma.isCurrentStep( toInt(l2) ) ) continue;
      data.ma.setCurrentStep( toInt(l2) );
      literals.push_back(l2);
    }
  }
  
  if( !getAll ) return;
  
  unsigned seenSoFar = literals.size();
  for( Var v = 0 ; v < maxVar; ++ v ) {
    for( int p = 0 ; p < 2; ++ p ) {
      const Lit l = mkLit(v,p==1);
      if( data.ma.isCurrentStep(toInt(l)) ) continue; // literal already in heap
      else literals.push_back(l);
    }
  }
  // shuffle these variables!
  const unsigned diff = literals.size() - seenSoFar;
  for( int i =  seenSoFar; i < literals.size(); ++ i ) {
    const Lit tmp = literals[i];
    const int rndInd = (rand() % diff) + seenSoFar;
    literals[i] = literals[ rndInd ];
    literals[ rndInd ] = tmp;
  }
}

inline void BIG::fillSorted(vector< Var >& variables, Coprocessor::CoprocessorData& data, bool rootsOnly, bool getAll)
{
  // get sorted list of lits
  data.lits.clear();
  fillSorted(data.lits, data, rootsOnly, getAll);
  variables.clear();
  
  // store variables in vector, according to occurrence of first literal in literal vector
  data.ma.nextStep();
  for( int i = 0 ; i < data.lits.size(); ++ i ) {
     const Lit l = data.lits[i];
     if( !data.ma.isCurrentStep( var(l) ) ) {
       variables.push_back(var(l)); 
       data.ma.setCurrentStep( var(l) );
     }
  }
}

inline void BIG::shuffle( Lit* adj, int size ) const
{
  for( uint32_t i = 0 ;  i+1<size; ++i ) {
    const uint32_t rnd = rand() % size;
    const Lit tmp = adj[i];
    adj[i] = adj[rnd];
    adj[rnd] = tmp;
  }
}

inline uint32_t BIG::stampLiteral( const Lit literal, uint32_t stamp, int32_t* index, deque<Lit>& stampQueue)
{
  // do not stamp a literal twice!
  if( start[ toInt(literal) ] != 0 ) return stamp;

  if( global_debug_out ) cerr << "c call STAMP for " << literal << endl;
  
  stampQueue.clear();
  // linearized algorithm from paper
  stamp++;
  // handle initial literal before putting it on queue
  start[toInt(literal)] = stamp; // parent and root are already set to literal
  if( global_debug_out ) cerr << "c start[" << literal << "] = " << stamp << endl;
  stampQueue.push_back(literal);

  shuffle( getArray(literal), getSize(literal) );
  index[toInt(literal)] = 0;

  while( ! stampQueue.empty() )
    {
      const Lit current = stampQueue.back();
      const int adjSize = getSize(current);

      if( index[toInt(current)] == adjSize ) {
	stampQueue.pop_back();
	stamp++;
	stop[toInt(current)] = stamp;
	if( global_debug_out ) cerr << "c stop[" << current << "] = " << stamp << endl;
      } else {
	int32_t& ind = index[ toInt(current) ]; // store number of processed elements
	const Lit impliedLit = getArray( current )[ind]; // get next implied literal
	ind ++;
	if( start[ toInt(impliedLit) ] != 0 ) continue;
	stamp ++;
	start[ toInt(impliedLit) ] = stamp;
	if( global_debug_out ) cerr << "c start[" << impliedLit << "] = " << stamp << endl;
	index[ toInt(impliedLit) ] = 0;
	stampQueue.push_back( impliedLit );
	shuffle( getArray(impliedLit), getSize(impliedLit) );
      }

    }
    return stamp;
}

inline bool BIG::implies(const Lit& from, const Lit& to) const
{
  if( start == 0 || stop == 0 || var(from) >= duringCreationVariables || var(to) >= duringCreationVariables ) return false;
  return ( start[ toInt(from) ] < start[ toInt(to) ] && stop[ toInt(from) ] > stop[ toInt(to) ] )
   || ( start[ toInt(~to) ] < start[ toInt(~from) ] && stop[ toInt(~to) ] > stop[ toInt(~from) ] );
}

inline bool BIG::isChild(const Lit& parent, const Lit& child) const
{
  const Lit * list = getArray(parent);
  const int listSize = getSize(parent);
  for( int j = 0 ; j < listSize; ++ j ) {
    if( list[j] == child )
      return true;
  }
  return false;
}

inline bool BIG::isOneChild(const Lit& parent, const Lit& child1, const Lit& child2) const
{
  const Lit * list = getArray(parent);
  const int listSize = getSize(parent);
  for( int j = 0 ; j < listSize; ++ j ) {
    if( list[j] == child1 || list[j] == child2 ) return true;
  }
  return false;
}


inline Logger::Logger(int level, bool err)
: outputLevel(level), useStdErr(err)
{}

inline void Logger::log(int level, const string& s)
{
  if( level > outputLevel ) return;
  (useStdErr ? std::cerr : std::cout )
    << "c [" << level << "] " << s << endl;
}

inline void Logger::log(int level, const string& s, const Clause& c)
{
  if( level > outputLevel ) return;
  (useStdErr ? std::cerr : std::cout )
    << "c [" << level << "] " << s << " : " ;
  for( int i = 0 ; i< c.size(); ++i ) {
    const Lit& l = c[i];
    (useStdErr ? std::cerr : std::cout )
      << " " << (sign(l) ? "-" : "") << var(l)+1;
  }
  (useStdErr ? std::cerr : std::cout )
    << endl;
}

inline void Logger::log(int level, const string& s, const Lit& l)
{
  if( level > outputLevel ) return;
  (useStdErr ? std::cerr : std::cout )
    << "c [" << level << "] " << s << " : "
    << (sign(l) ? "-" : "") << var(l)+1
    << endl;
}

inline void Logger::log(int level, const string& s, const int i)
{
  if( level > outputLevel ) return;
  (useStdErr ? std::cerr : std::cout )
    << "c [" << level << "] " << s << " " << i << endl;
}


inline void Logger::log(int level, const string& s, const Clause& c, const Lit& l)
{
  if( level > outputLevel ) return;
  (useStdErr ? std::cerr : std::cout )
    << "c [" << level << "] " << s << " : "
    << (sign(l) ? "-" : "") << var(l)+1 << " with clause ";
  for( int i = 0 ; i< c.size(); ++i ) {
    const Lit& l = c[i];
    (useStdErr ? std::cerr : std::cout )
      << " " << (sign(l) ? "-" : "") << var(l)+1;
  }
  (useStdErr ? std::cerr : std::cout )
    << endl;
}

}

#endif
