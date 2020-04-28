/********************************************************************[BoundedVariableElimination.h]
Copyright (c) 2012, Kilian Gebhardt, Norbert Manthey, All rights reserved.
**************************************************************************************************/
#ifndef BVE_HH
#define BVE_HH

#include "core/Solver.h"

#include "coprocessor-src/Technique.h"

#include "coprocessor-src/CoprocessorTypes.h"
#include "coprocessor-src/Subsumption.h"
#include "mtl/Heap.h"

using namespace Minisat;
using namespace std;

namespace Coprocessor {

/** This class implement blocked variable elimination
 */
class BoundedVariableElimination : public Technique {
  
  Coprocessor::Propagation & propagation;
  Coprocessor::Subsumption & subsumption;

  // variable heap comperators
  const int heap_option;
  
  struct PostponeReason {
      Var var, reason;
      PostponeReason ( Var _var, Var _reason) : var(_var), reason(_reason) {}
  };
  // Vector for restarting bve (seq and par)
  vector<Var> touched_variables;
  // variable queue for random variable-order
  vector< Var > variable_queue;

  // sequential member variables
  vec< Lit > resolvent; // vector for sequential resolution
  vec< int32_t > pos_stats;
  vec< int32_t > neg_stats; 
  // parallel member variables
  MarkArray lastTouched;                    //MarkArray to track modifications of parallel BVE-Threads
  MarkArray dirtyOccs;                      // tracks occs that contain CRef_Undef
  vector< Job > jobs;                     
  vector< SpinLock > variableLocks;         // 3 extra SpinLock for data, heap, ca
  vector< deque < CRef > > subsumeQueues;
  vector< deque < CRef > > strengthQueues;
  vector< deque < PostponeReason > > postpones;
  vector< MarkArray > gateMarkArrays;
  deque< CRef > sharedStrengthQueue;
  ReadersWriterLock allocatorRWLock;
  // stats variables
  struct ParBVEStats {
      int removedClauses, removedLiterals, createdClauses, createdLiterals, removedLearnts, learntLits, newLearnts, 
      newLearntLits, testedVars, anticipations, eliminatedVars, removedBC, blockedLits, removedBlockedLearnt, learntBlockedLit, 
      skippedVars, unitsEnqueued, foundGates, usedGates, subsumedClauses, subsumedLiterals, subsumedLearnts, subsumedLearntLiterals,
      subsimpSteps, strengthtLits, strengthtLearntLits;   
      int64_t parBveChecks;
      double processTime, subsimpTime, gateTime, upTime, lockNeighborTime, mereLockingTime;
      char _pad[60];
      ParBVEStats() :   removedClauses(0), removedLiterals(0), createdClauses(0), createdLiterals(0), removedLearnts(0)
                      , learntLits(0), newLearnts(0), newLearntLits(0), testedVars(0), anticipations(0), eliminatedVars(0)
                      , removedBC(0), blockedLits(0), removedBlockedLearnt(0), learntBlockedLit(0), skippedVars(0)
                      , unitsEnqueued(0), foundGates(0), usedGates(0), subsumedClauses(0), subsumedLiterals(0)
                      , subsumedLearnts(0), subsumedLearntLiterals(0), subsimpSteps(0)
                      , strengthtLits(0), strengthtLearntLits(0)
		      , parBveChecks(0)
                      , processTime(0), subsimpTime(0), gateTime(0), upTime(0), lockNeighborTime(0) , mereLockingTime(0){}
  };
  vector<struct ParBVEStats> parStats;

  // stats variables
  int removedClauses, removedLiterals, createdClauses, createdLiterals, removedLearnts, learntLits, newLearnts, 
      newLearntLits, testedVars, anticipations, eliminatedVars, removedBC, blockedLits, removedBlockedLearnt, learntBlockedLit, 
      skippedVars, unitsEnqueued, foundGates, usedGates, 
      initialClauses, initialLits, clauseCount, litCount, unitCount, elimCount, restarts;   
  int64_t seqBveSteps, bveLimit;
  int64_t nClsIncreases,nClsDecreases,nClsKeep,totallyAddedClauses; // number of clauses that have been added by bve
  double processTime, subsimpTime, gateTime;

public:
  
  BoundedVariableElimination( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller , Coprocessor::Propagation & _propagation, Coprocessor::Subsumption & _subsumption);
 
  lbool process(CoprocessorData & data, const bool doStatistics = true) { modifiedFormula = false; return runBVE(data, doStatistics); }

  /** run BVE until completion */
  lbool runBVE(CoprocessorData& data, const bool doStatistics = true);

  void initClause(const CRef cr); // inherited from Technique
  void destroy();
  void giveMoreSteps();
  void printStatistics(ostream& stream);

protected:
  
  void progressStats(CoprocessorData & data, const bool cputime = false);     // prints statistics before/after each BVE-Run
  bool hasToEliminate();                               // return whether there is something in the BVE queue

  // sequential functions:
  void sequentiellBVE(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const bool force = false, const bool doStatistics = true);
  void bve_worker (Coprocessor::CoprocessorData& data, Heap< Coprocessor::VarOrderBVEHeapLt >& heap, int64_t& bveChecks, const bool force = false, const bool doStatistics = true);   
  inline void removeClauses(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const vector<CRef> & list, const Lit l, const int limit, const bool doStatistics = true);
  
  
  /** ths method applies unit propagation during resolution, if possible! */
  inline lbool resolveSet(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, vector<CRef> & positive, vector<CRef> & negative
          , const int v, const int p_limit, const int n_limit, int64_t& bveChecks
          , const bool keepLearntResolvents = false, const bool force = false, const bool doStatistics = true);
  inline lbool anticipateElimination(CoprocessorData & data, vector<CRef> & positive, vector<CRef> & negative
          , const int v, const int p_limit, const int n_limit, vec<int32_t> & pos_stats, vec<int32_t> & neg_stats
          , int & lit_clauses, int & lit_learnts, int& resolvents, int64_t& bveChecks, const bool doStatistics = true); 
  inline void addClausesToSubsumption (const vector<CRef> & clauses);
  void touchedVarsForSubsumption (CoprocessorData & data, const std::vector<Var> & touched_vars);

  
  /** data for parallel execution */
  struct BVEWorkData {
    BoundedVariableElimination*  bve; // class with code
    CoprocessorData* data;        // formula and maintain lists
    vector<SpinLock> * var_locks; // Spin Lock for Variables
    ReadersWriterLock * rw_lock;  // rw-lock for CA
    Heap<VarOrderBVEHeapLt> * heap; // Shared heap with variables for elimination check
    MarkArray * dirtyOccs;
    deque<CRef> * strengthQueue;
    deque<CRef> * sharedStrengthQueue;
    deque< PostponeReason > * postponed;
    ParBVEStats * bveStats;
    MarkArray * gateMarkArray;
    int rwlock_count;
    BVEWorkData () : rwlock_count(0), garbageCounter(0) {}
    int garbageCounter;
  };


  // parallel functions:
  void par_bve_worker 
          ( CoprocessorData& data, Heap<VarOrderBVEHeapLt> & heap
          , deque < CRef > & strengthQueue , deque < CRef > & sharedStrengthQueue, deque < PostponeReason > & postponed 
          , vector< SpinLock > & var_lock, ReadersWriterLock & rwlock
          , ParBVEStats & stats , MarkArray * gateMarkArray, int & rwlock_count
          , int & garbageCounter
	  , int64_t&parBVEchecks
          , const bool force = false, const bool doStatistics = true) ; 

  inline void removeBlockedClauses(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const vector< CRef> & list, const int32_t stats[], const Lit l, const int limit, const bool doStatistics = true );
  
    /** run parallel bve with all available threads */
  void parallelBVE(CoprocessorData& data);
  
  inline void removeClausesThreadSafe(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const vector<CRef> & list, const Lit l, const int limit, SpinLock & data_lock, SpinLock & heap_lock, ParBVEStats & stats, int & garbageCounter, const bool doStatistics);
  inline lbool resolveSetThreadSafe(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, vector<CRef> & positive, vector<CRef> & negative, const int v, const int p_limit, const int n_limit, vec < Lit > & ps, AllocatorReservation & memoryReservation, deque<CRef> & strengthQueue, ParBVEStats & stats, SpinLock & data_lock, SpinLock & heap_lock, int expectedResolvents, int64_t& bveChecks, const bool doStatistics, const bool keepLearntResolvents = false);
  inline lbool anticipateEliminationThreadsafe(CoprocessorData & data, vector<CRef> & positive, vector<CRef> & negative, const int v, const int p_limit, const int n_limit, vec<Lit> & resolvent, vec < int32_t > & pos_stats, vec < int32_t > & neg_stats, int & lit_clauses, int & lit_learnts, int & new_clauses, int & new_learnts, SpinLock & data_lock, ParBVEStats & stats, int64_t& bveChecks, const bool doStatistics);
  inline void removeBlockedClausesThreadSafe(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const vector< CRef> & list, const int32_t _stats[], const Lit l, const int limit, SpinLock & data_lock, SpinLock & heap_lock, ParBVEStats & stats, int & garbageCounter, const bool doStatistics );

  // Special subsimp implementations for par bve:
  void par_bve_strengthening_worker(CoprocessorData& data, Heap<VarOrderBVEHeapLt> & heap, const Var ignore, vector< SpinLock > & var_lock, ReadersWriterLock & rwlock, deque<CRef> & sharedStrengthQueue, deque<CRef> & localQueue, MarkArray & dirtyOccs, ParBVEStats & stats, int & rwlock_count, int & garbageCounter, const bool strength_resolvents, const bool doStatistics);

  // Special propagation for par bve
  lbool par_bve_propagate(CoprocessorData& data, Heap<VarOrderBVEHeapLt> & heap, const Var ignore, vector< SpinLock > & var_lock, ReadersWriterLock & rwlock, MarkArray & dirtyOccs, deque <CRef> & sharedSubsimpQueue, ParBVEStats & stats, int & rwlock_count, int & garbageCounter, const bool doStatistics);

inline lbool strength_check_pos(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const Var ignore, vector < CRef > & list, deque<CRef> & sharedStrengthQueue, deque<CRef> & localQueue, Clause & strengthener, CRef cr, Var fst, vector < SpinLock > & var_lock, MarkArray & dirtyOccs, ParBVEStats & stats, int & garbageCounter, const bool strength_resolvents, const bool doStatistics); 

inline lbool strength_check_neg(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const Var ignore, vector < CRef > & list, deque<CRef> & sharedStrengthQueue, deque<CRef> & localQueue, Clause & strengthener, CRef cr, Lit min, Var fst, vector < SpinLock > & var_lock, MarkArray & dirtyOccs, ParBVEStats & stats, int & garbageCounter, const bool strength_resolvents, const bool doStatistics); 
  // Helpers for both par and seq
  inline bool resolve(const Clause & c, const Clause & d, const int v, vec<Lit> & ps);
  inline int  tryResolve(const Clause & c, const Clause & d, const int v);
  inline bool checkPush(vec<Lit> & ps, const Lit l);
  inline char checkUpdatePrev(Lit & prev, const Lit l);
  bool findGates(CoprocessorData & data, const Var v, int & p_limit, int & n_limit, double & _gateTim, MarkArray * helper = NULL);


public:
  /** converts arg into BVEWorkData*, runs bve of its part of the queue */
  static void* runParallelBVE(void* arg);

};


  /**
   * expects c to contain v positive and d to contain v negative
   * @return true, if resolvent is satisfied
   *         else, otherwise
   */
  inline bool BoundedVariableElimination::resolve(const Clause & c, const Clause & d, const int v, vec<Lit> & resolvent)
  {
    unsigned i = 0, j = 0;
    while (i < c.size() && j < d.size())
    {   
        if (c[i] == mkLit(v,false))      ++i;   
        else if (d[j] == mkLit(v,true))  ++j;
        else if (c[i] < d[j])
        {
           if (checkPush(resolvent, c[i]))
                return true;
           else ++i;
        }
        else 
        {
           if (checkPush(resolvent, d[j]))
              return true;
           else
                ++j; 
        }
    }
    while (i < c.size())
    {
        if (c[i] == mkLit(v,false))    ++i;   
        else if (checkPush(resolvent, c[i]))
            return true;
        else 
            ++i;
    }
    while (j < d.size())
    {
        if (d[j] == mkLit(v,true))     ++j;
        else if (checkPush(resolvent, d[j]))
            return true;
        else                           ++j;

    }
    return false;
  } 
  /**
   * expects c to contain v positive and d to contain v negative
   * @return -1, if resolvent is tautology
   *         number of resolvents literals, otherwise
   */
  inline int BoundedVariableElimination::tryResolve(const Clause & c, const Clause & d, const int v)
  {
    unsigned i = 0, j = 0, r = 0;
    Lit prev = lit_Undef;
    while (i < c.size() && j < d.size())
    {   
        if (c[i] == mkLit(v,false))           ++i;   
        else if (d[j] == mkLit(v,true))       ++j;
        else if (c[i] < d[j])
        {
           char status = checkUpdatePrev(prev, c[i]);
           if (status == -1)
             return -1;
           else 
           {     
               ++i;
               r+=status;;
           }
        }
        else 
        {
           char status = checkUpdatePrev(prev, d[j]);
           if (status == -1)
              return -1;
           else
           {     
               ++j; 
               r+=status;
           }
        }
    }
    while (i < c.size())
    {
        if (c[i] == mkLit(v,false))
            ++i;   
        else
        {   
            char status = checkUpdatePrev(prev, c[i]);
            if (status == -1)
                return -1;
            else 
            {
                ++i;
                r+=status;
            }
        }
    }
    while (j < d.size())
    {
        if (d[j] == mkLit(v,true))              ++j;
        else 
        {
            char status = checkUpdatePrev(prev, d[j]);
            if (status == -1)
                return -1;
            else 
            {
                ++j;
                r+=status;
            }
        }
    }
    return r;
  } 
 
inline bool BoundedVariableElimination::checkPush(vec<Lit> & ps, const Lit l)
  {
    if (ps.size() > 0)
    {
        if (ps.last() == l)
         return false;
        if (ps.last() == ~l)
         return true;
    }
    ps.push(l);
    return false;
  }

inline char BoundedVariableElimination::checkUpdatePrev(Lit & prev, const Lit l)
  {
    if (prev != lit_Undef)
    {
        if (prev == l)
            return 0;
        if (prev == ~l)
            return -1;
    }
    prev = l;
    return 1;
  }
}
#endif 
