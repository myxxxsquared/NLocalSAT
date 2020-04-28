/***********************************************************[BoundedVariableEliminationParallel.cc]
Copyright (c) 2013, Kilian Gebhardt, Norbert Manthey, All rights reserved.
**************************************************************************************************/
#include "coprocessor-src/BoundedVariableElimination.h"
#include "coprocessor-src/Propagation.h"
#include "coprocessor-src/Subsumption.h"
#include <algorithm> // std::sort
#include "mtl/Heap.h"
using namespace Coprocessor;
using namespace std;

static int upLevel = 1;

static inline void printLitErr(const Lit l) 
{
    if (toInt(l) % 2)
           cerr << "-";
        cerr << (toInt(l)/2) + 1 << " ";
}
static void printLitVec(const vec<Lit> & litvec)
{
    cerr <<"c "; 
    for (int i = 0; i < litvec.size(); ++i)
    {   
        printLitErr(litvec[i]);
    }
    cerr << endl;

}

static void printClauses(ClauseAllocator & ca, vector<CRef> & list, bool skipDeleted)
{
    for (unsigned i = 0; i < list.size(); ++i)
    {
        if (list[i] == CRef_Undef || skipDeleted && ca[list[i]].can_be_deleted())
            continue; 
        cerr << ca[list[i]] << (ca[list[i]].can_be_deleted() ? " delete" : " valid") << endl; 
    }

}


/** parallel version of bve worker
 *  TODO update this
 *  Preconditions:
 *  all unit clauses were propagated
 *
 *  Assumptions:
 *  -> occurrence lists are valid, 
 *          i.e. CR in list(l) iff l \in ca[CR]
 *     they may contain deleted clauses (blocked clauses or clauses that were resolved)
 *     resolvents are immediately added to the list
 *     strengthened clauses are removed from the corresponding list
 *     => this is achived by a Readers-Writer-Lock
 *
 *  The locks are acquired in the following order
 *  X     Heap Lock
 *  1.    Locks on Variables (from Low to High)
 *  2.a   Read  Lock on both, clause allocator and occurrences
 *  2.a.1 Write-Lock on data-object (for statistics), enqueuing of Units, extensions
 *  2.b   Write Lock on both, clasue allocates and occurrences
 *
 *  -> i.e. you must not acquire a write and a read lock at the same time
 *          you must not acquire a write lock on the data object, if alread 2.b was acquired
 *          you either hold a heap lock or any of the other locks 
 */
void BoundedVariableElimination::par_bve_worker (CoprocessorData& data, Heap<VarOrderBVEHeapLt> & heap, deque < CRef > & strengthQueue, deque < CRef > & sharedStrengthQueue, deque< PostponeReason > & postponed, vector< SpinLock > & var_lock, ReadersWriterLock & rwlock, ParBVEStats & stats, MarkArray * gateMarkArray, int & rwlock_count, int & garbageCounter, int64_t& parBVEchecks, const bool force, const bool doStatistics)   
{
    if (doStatistics) stats.processTime = wallClockTime() - stats.processTime;

    SpinLock & data_lock = var_lock[data.nVars()]; 
    SpinLock & heap_lock = var_lock[data.nVars() + 1]; // used for variable-heap or queue
    SpinLock & ca_lock   = var_lock[data.nVars() + 2];
    SpinLock & susi_lock = var_lock[data.nVars() + 4];
     
    vector < Var > neighbors;
    vec < int32_t > pos_stats;
    vec < int32_t > neg_stats;
    vec < Lit > ps;
    MarkArray & neighborMA = *gateMarkArray; //reuse gate MA
    int32_t timeStamp;  
    while ( data.ok()
      && ( !data.isInterupted() )
      && ( seqBveSteps + parBVEchecks < bveLimit || data.unlimited() )
    ) // if solver state = false => abort
    {
        // Propagate (rw-locks)
        if (data.hasToPropagate())
        {
            if (doStatistics) stats.upTime = wallClockTime() -  stats.upTime;
            par_bve_propagate(data, heap, var_Undef, var_lock, rwlock, dirtyOccs, sharedStrengthQueue, stats, rwlock_count, garbageCounter, doStatistics);
            if (doStatistics) stats.upTime = wallClockTime() -  stats.upTime;
            continue;
        }
        // Subsimp
        if (sharedStrengthQueue.size() > 0) 
        {
            if (doStatistics) stats.subsimpTime = wallClockTime() -  stats.subsimpTime;
            par_bve_strengthening_worker(data, heap, var_Undef, var_lock, rwlock, sharedStrengthQueue, strengthQueue, dirtyOccs, stats, rwlock_count, garbageCounter, false, doStatistics);
            if (doStatistics) stats.subsimpTime = wallClockTime() -  stats.subsimpTime;
            continue;
        }
       
        // Eliminate
        Var v = var_Undef;
        // lock Heap or Q and acquire variable
        heap_lock.lock();
        if (config.opt_bve_heap != 2)
        {
            // look if the first postponed var is free
            if (postponed.size() > 0 && !var_lock[postponed.front().reason].getValue())
            {
               v = postponed.front().var;
               postponed.pop_front();
            }
            // look for a free heap-var
            while (heap.size() > 0 && v == var_Undef)
            {
                v = heap.removeMin();
                if (var_lock[v].getValue())
                {
                    postponed.push_back(PostponeReason(v, v));
                    v = var_Undef;
                }
            }
            // take the first postponed-var
            if (v == var_Undef && postponed.size() > 0)
            {
                v = postponed.front().var;
                postponed.pop_front();
            }

        }
        else if (variable_queue.size() > 0)
        {
            int rand = data.getSolver()->irand(data.getSolver()->random_seed, variable_queue.size());
            v = variable_queue[rand];
            if (variable_queue.size() > 1)
            {
                variable_queue[rand] = variable_queue[variable_queue.size() - 2];
            }
            variable_queue.pop_back();

        }
        heap_lock.unlock();
        
        // if Heap or Queue was empty, break
        if (v == var_Undef)
            break;
        
    calculate_neighbors:
       // do not work on this variable, if it will be unit-propagated! if all units are eagerly propagated, this is not necessary
       if  (data.value(mkLit(v,true)) != l_Undef || data.value(mkLit(v,false)) != l_Undef)
               continue;
       // if no occurrences of v, continue
       if (data[v] <= 0)
           continue;
       if( data.doNotTouch(v) ) continue; // do not use this variable!
 
        // Heuristic Cutoff
        if (!config.opt_force_gates && !config.opt_unlimited_bve 
                && (data[mkLit(v,true)] > 10 && data[mkLit(v,false)] > 10 || data[v] > 15 && (data[mkLit(v,true)] > 5 || data[mkLit(v,false)] > 5)))
        {
            if (doStatistics) ++stats.skippedVars;
            continue;
        }
           
        // Lock v 
        if (config.opt_bve_heap != 2 && var_lock[v].getValue())
        {
            postponed.push_back(PostponeReason(v,v));
            continue;
        }

        if (doStatistics) stats.lockNeighborTime = wallClockTime() - stats.lockNeighborTime;

        assert(rwlock_count == 0);
        var_lock[v].lock();

        ///////////////////////////////////////////////////////////////////////////////////////////
        //
        //  Begin: read locked part 
        //
        ///////////////////////////////////////////////////////////////////////////////////////////
        
        assert(rwlock_count == 0);
        rwlock_count++;
        rwlock.readLock();
        // Get the clauses with v
        vector<CRef> & pos = data.list(mkLit(v,false)); 
        vector<CRef> & neg = data.list(mkLit(v,true));
        
        int locked_neigbors = 0;
        Var reason = var_Undef;
        
        //neighbor_heap.insert(v);
        neighborMA.nextStep();
        neighborMA.setCurrentStep(v);
        neighbors.push_back(v);
        // Build neighbor-vector
        // expecting valid occurrence-lists, i.e. v really occurs in lists 
        for (int r = 0; r < pos.size() && locked_neigbors <= config.postpone_locked_neighbors; ++r)
        {
            const CRef cr = pos[r];
            if (CRef_Undef == cr)
                continue;
            Clause & c = ca[cr];
            c.spinlock();
            if (c.can_be_deleted())
            {
              c.unlock();
              continue;
            }
            for (int l = 0; l < c.size(); ++ l)
            {
                Var v = var(c[l]);
                if (!neighborMA.isCurrentStep(v))
                {
                    if (config.opt_bve_heap != 2 && var_lock[v].getValue())
                        if (++locked_neigbors > config.postpone_locked_neighbors)
                        {
                            reason = v;
                            break;
                        }
                    neighborMA.setCurrentStep(v);
                    neighbors.push_back(v);
                }
            }
            c.unlock();
        }
        for (int r = 0; r < neg.size() && locked_neigbors <= config.postpone_locked_neighbors; ++r)
        {
            const CRef cr = neg[r];
            if (CRef_Undef == cr)
                continue;
            Clause & c = ca[cr];
            c.spinlock();
            if (c.can_be_deleted())
            {
                c.unlock();
                continue;
            }
            for (int l = 0; l < c.size(); ++ l)
            {
                Var v = var(c[l]);
                //if (! neighbor_heap.inHeap(v))
                if (!neighborMA.isCurrentStep(v))
                {
                    if (config.opt_bve_heap != 2 && var_lock[v].getValue())
                        if (++locked_neigbors > config.postpone_locked_neighbors)
                        {
                            reason = v;
                            break;
                        }
                    //neighbor_heap.insert(v);
                    neighborMA.setCurrentStep(v);
                    neighbors.push_back(v);
                }
            }
            c.unlock();
        }
        timeStamp = lastTouched.getIndex(v); // get last modification of v

        assert(rwlock_count == 1);
        --rwlock_count;
        rwlock.readUnlock();

        ///////////////////////////////////////////////////////////////////////////////////////////
        //
        //  End: read locked part 
        //
        ///////////////////////////////////////////////////////////////////////////////////////////
        
        // unlock v
        var_lock[v].unlock();

        if (locked_neigbors > config.postpone_locked_neighbors)
        {
            assert(reason != var_Undef);
            neighbors.clear();
            //neighbor_heap.clear();
            postponed.push_back(PostponeReason(v, reason));
            if (doStatistics) stats.lockNeighborTime = wallClockTime() - stats.lockNeighborTime;
            continue;
        }

        //while (neighbor_heap.size() > 0)
            //neighbors.push_back(neighbor_heap.removeMin());
        std::sort(neighbors.begin(), neighbors.end());
        // neighbor contains all neighbors in ascending order
       
        // lock all Vars in ascending order 
        if (doStatistics) stats.mereLockingTime = wallClockTime() - stats.mereLockingTime;
        for (int i = 0; i < neighbors.size(); ++i)
        {
           var_lock[neighbors[i]].lock();
        }
        if (doStatistics) stats.mereLockingTime = wallClockTime() - stats.mereLockingTime;
        
        if (doStatistics) stats.lockNeighborTime = wallClockTime() - stats.lockNeighborTime;

        ///////////////////////////////////////////////////////////////////////////////////////////
        //
        //  Begin: read locked part 
        //
        ///////////////////////////////////////////////////////////////////////////////////////////
        assert(rwlock_count == 0);
        rwlock_count++;
        rwlock.readLock(); 
        
        // check if the variable-sub-graph is still valid
        // or UNSAT
        //  or var enqueued
        if (lastTouched.getIndex(v) != timeStamp 
                || !data.ok()
                || data.value(mkLit(v,true)) != l_Undef 
                || data.value(mkLit(v,false)) != l_Undef)
        {
            assert(rwlock_count == 1);
            --rwlock_count;
            rwlock.readUnlock(); // Early Exit Read Lock
            // free all locks on Vars in descending order 
            for (int i = neighbors.size() - 1; i >= 0; --i)
            {
               var_lock[neighbors[i]].unlock();
            }

            // if UNSAT -> return
            if (!data.ok())
                break;

            // Cleanup
            neighbors.clear();
            
            if (   data.value(mkLit(v,true)) != l_Undef 
                || data.value(mkLit(v,false)) != l_Undef)
                continue;
            goto calculate_neighbors;
        }

        ///////////////////////////////////////////////////////////////////////////////////////////
        //
        //  The process now holds all exclusive locks for the current neighbors of v, 
        //  and perhaps some additional, since some Clauses could have 
        //  been removed from pos and neg, but for sure none were added. 
        //
        ///////////////////////////////////////////////////////////////////////////////////////////
        
       // ---Printing all Clauses with v --------------------------//
       if (config.opt_bve_verbose > 2)
       {
           cerr << "c Variable: " << v+1 << endl;
           cerr <<"c before Gates: " << endl;
           cerr <<"c Clauses with Literal  " << v+1 <<":" << endl;
           printClauses(ca, pos, false);
           cerr <<"c Clauses with Literal ¬" << v+1 <<":" << endl;
           printClauses(ca, neg, false); 
       }
       // ---------------------------------------------------------//
       //
        // Search for Gates
        int p_limit = data.list(mkLit(v,false)).size();
	    int n_limit = data.list(mkLit(v,true)).size();
	    bool foundGate = false;
        if ( config.opt_bve_findGate ) {
           foundGate = findGates(data, v, p_limit, n_limit, stats.gateTime, gateMarkArray);
           if (doStatistics) stats.foundGates ++;
        }
    
       // ---Printing all Clauses with v --------------------------//
       if (config.opt_bve_findGate && config.opt_bve_verbose > 2)
       {
           cerr << "c Variable: " << v+1 << endl;
           cerr <<"c after Gates: " << endl;
           cerr <<"c Clauses with Literal  " << v+1 <<":" << endl;
           printClauses(ca, pos, false);
           cerr <<"c Clauses with Literal ¬" << v+1 <<":" << endl;
           printClauses(ca, neg, false); 
       }
       // ---------------------------------------------------------//
        // Heuristic Cutoff if Gate-Search is forced
        if (config.opt_force_gates && !foundGate && !config.opt_unlimited_bve 
                && (data[mkLit(v,true)] > 10 && data[mkLit(v,false)] > 10 || data[v] > 15 && (data[mkLit(v,true)] > 5 || data[mkLit(v,false)] > 5)))
        {
            if (doStatistics) ++stats.skippedVars;
            
            assert(rwlock_count == 1);
            --rwlock_count;
            rwlock.readUnlock(); // Early Exit Read Lock
            // free all locks on Vars in descending order 
            for (int i = neighbors.size() - 1; i >= 0; --i)
            {
               var_lock[neighbors[i]].unlock();
            }

            // if UNSAT -> return
            if (!data.ok())
                break;

            // Cleanup
            neighbors.clear();
            continue;
        }

        if (doStatistics) ++stats.testedVars;

        int pos_count = 0; 
        int neg_count = 0;
        int lit_clauses_old = 0;
        int lit_learnts_old = 0;

        if (config.opt_bve_verbose > 1)
        {
           cerr << "c ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
           cerr << "c Counting Clauses" << endl;
        }
       
        for (int i = 0; i < pos.size(); ++i)
        {
            const CRef cr = pos[i];
            if (CRef_Undef == cr)
                continue;
            Clause & c = ca[cr];
            if (c.can_be_deleted())
                continue;
            if (c.learnt())
                lit_learnts_old += c.size();
            else 
                lit_clauses_old += c.size();
            ++pos_count;
        }      
        for (int i = 0; i < neg.size(); ++i)
        {
            const CRef cr = neg[i];
            if (CRef_Undef == cr)
                continue;
            Clause & c = ca[cr];
            if (c.can_be_deleted())
                continue;
            if (c.learnt())
                lit_learnts_old += c.size();
            else 
                lit_clauses_old += c.size();
            ++neg_count;
        }
        if (config.opt_bve_verbose > 2) cerr << "c ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
        
        // Declare stats variables;        
        pos_stats.growTo(pos.size(), 0);         
        neg_stats.growTo(neg.size(), 0);
        int lit_clauses = 0;
        int lit_learnts = 0;
        int new_clauses = 0; 
        int new_learnts = 0;
        
        // anticipate only, if there are positiv and negative occurrences of var 
        if (pos_count != 0 &&  neg_count != 0)
        {
            if (doStatistics) ++stats.anticipations;
            if (anticipateEliminationThreadsafe(data, pos, neg,  v, p_limit, n_limit, ps, pos_stats, neg_stats, lit_clauses, lit_learnts, new_clauses, new_learnts, data_lock, stats, parBVEchecks, doStatistics) == l_False) 
            {
                // UNSAT: free locks and abort
                assert(rwlock_count == 1);
                --rwlock_count;
                rwlock.readUnlock(); // Early Exit Read Lock
                // free all locks on Vars in descending order 
                for (int i = neighbors.size() - 1; i >= 0; --i)
                {
                    var_lock[neighbors[i]].unlock();
                }
                //return;
                break;  
            }
        }
        if (config.opt_bve_bc)
        { 
            //mark Clauses without resolvents for deletion
            if(config.opt_bve_verbose > 2) cerr << "c ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" << endl;
            if(config.opt_bve_verbose > 1) cerr << "c removing blocked clauses from F_" << v+1 << endl;
            removeBlockedClausesThreadSafe(data, heap, pos, pos_stats, mkLit(v, false), p_limit, data_lock, heap_lock, stats, garbageCounter, doStatistics); 
            if(config.opt_bve_verbose > 1) cerr << "c removing blocked clauses from F_¬" << v+1 << endl;
            removeBlockedClausesThreadSafe(data, heap, neg, neg_stats, mkLit(v, true), n_limit, data_lock, heap_lock, stats, garbageCounter, doStatistics); 
        }
        assert(rwlock_count == 1);
        --rwlock_count;
        rwlock.readUnlock();

        ///////////////////////////////////////////////////////////////////////////////////////////
        //
        //  End: Read locked part 
        //
        ///////////////////////////////////////////////////////////////////////////////////////////
       
        
        // if resolving reduces number of literals in clauses: 
        //    add resolvents
        //    mark old clauses for deletion
        bool doResolve = false;
        bool reducedLits = lit_clauses > 0 && lit_clauses <= lit_clauses_old;
	    bool reducedClss = new_clauses > 0 && pos_count + neg_count >= new_clauses;
             if( config.opt_bve_reduce_lits == 0 ) doResolve = reducedLits;				    // number of literals decreasesd
	    else if( config.opt_bve_reduce_lits == 1 ) doResolve = reducedClss;			        // number of clauses decreasesd
	    else if( config.opt_bve_reduce_lits == 2 ) doResolve = reducedClss || reducedLits;	// number of literals or clauses decreasesd
	    else if( config.opt_bve_reduce_lits == 3 ) doResolve = reducedClss && reducedLits;	// number of literals and clauses decreasesd
        
        if (!config.opt_bce_only && new_clauses > 0 && (force || doResolve) )
        {
        ///////////////////////////////////////////////////////////////////////////////////////////
        //
        //  Reservation of Allocator-Memory 
        //
        ///////////////////////////////////////////////////////////////////////////////////////////
            assert(rwlock_count == 0);
            ca_lock.lock();     
            if (false) 
            {
                cerr << "c want resolve " << new_clauses + new_learnts << " clauses on variable " << v + 1 << " with pos size: " << pos.size() << " negs: " << neg.size() <<endl;
                cerr << "c v " << v + 1 << " neighbors: "; 
                for (int i = 0; i < neighbors.size(); ++i) { cerr << neighbors[i] + 1 << ", " ; }
                cerr << endl;
            }
            AllocatorReservation memoryReservation = ca.reserveMemory( new_clauses + new_learnts, lit_clauses + lit_learnts, new_learnts, rwlock);
            ca_lock.unlock();

        ///////////////////////////////////////////////////////////////////////////////////////////
        //
        //  Begin: read locked part 
        //
        ///////////////////////////////////////////////////////////////////////////////////////////
             assert(rwlock_count == 0);
             rwlock_count++;
             rwlock.readLock(); 
             if (!data.ok())
             {
                 // UNSAT case -> end thread, but first release all locks
                assert(rwlock_count == 1);
                --rwlock_count;
                 rwlock.readUnlock();
                 // free all locks on Vars in descending order 
                 for (int i = neighbors.size() - 1; i >= 0; --i)
                 {
                     var_lock[neighbors[i]].unlock();
                 }
                 //return;
                 break; // break the main-loop, i.e. end of function
             }
             
		     if (doStatistics) stats.usedGates = (foundGate ? stats.usedGates + 1 : stats.usedGates ); // statistics
             if(config.opt_bve_verbose > 1)  cerr << "c resolveSet" <<endl;

             if (resolveSetThreadSafe(data, heap, pos, neg, v, p_limit, n_limit, ps, memoryReservation, strengthQueue, stats, data_lock, heap_lock, new_clauses + new_learnts, parBVEchecks, doStatistics) == l_False) 
             {
                 // UNSAT case -> end thread, but first release all locks
                assert(rwlock_count == 1);
                --rwlock_count;
                 rwlock.readUnlock();
                 // free all locks on Vars in descending order 
                 for (int i = neighbors.size() - 1; i >= 0; --i)
                 {
                     var_lock[neighbors[i]].unlock();
                 }
                 //return;
                 break; // breaks the main-loop, i.e. end of function
             }

             // remove Clauses that were resolved
             // (since write lock, no threadsafe implementation needed)
             removeClausesThreadSafe(data, heap, pos, mkLit(v,false), p_limit, data_lock, heap_lock, stats, garbageCounter, doStatistics);
             removeClausesThreadSafe(data, heap, neg, mkLit(v,true) , n_limit, data_lock, heap_lock, stats, garbageCounter, doStatistics);
             vector<CRef>().swap(pos); // free physical memory of pos-occ
             vector<CRef>().swap(neg); // free physical memory of neg-occ
             if (config.opt_bve_verbose > 0) cerr << "c Resolved " << v+1 <<endl;
             if (doStatistics) ++stats.eliminatedVars;

             // touch variables:
             data_lock.lock();
             lastTouched.nextStep();
             for (int i = 0; i < neighbors.size(); ++i)
             {
                lastTouched.setCurrentStep(neighbors[i]); 
             }
             data_lock.unlock();

             //subsimp with new clauses!!
            if (doStatistics) stats.subsimpTime = wallClockTime() -  stats.subsimpTime;
             par_bve_strengthening_worker(data, heap, v, var_lock, rwlock, sharedStrengthQueue, strengthQueue, dirtyOccs, stats, rwlock_count, garbageCounter, true, doStatistics);
            if (doStatistics) stats.subsimpTime = wallClockTime() -  stats.subsimpTime;
             assert(rwlock_count == 1);
             --rwlock_count;
             rwlock.readUnlock();
        
        ///////////////////////////////////////////////////////////////////////////////////////////
        //
        //  End: read locked part 
        //
        ///////////////////////////////////////////////////////////////////////////////////////////
       
        }
        
        if(config.opt_bve_verbose > 1)   cerr << "c =============================================================================" << endl;

        // free all locks on Vars in descending order 
        for (int i = neighbors.size() - 1; i >= 0; --i)
        {
           var_lock[neighbors[i]].unlock();
        }
        // Cleanup
        neighbors.clear();
        pos_stats.clear();
        neg_stats.clear();
    }

    if (doStatistics) stats.processTime = wallClockTime() - stats.processTime;
}

/**
 * on every clause, that is not yet marked for deletion:
 *      remove it from data-Objects statistics
 *      mark it for deletion
 *
 *      TODO don't use the data_lock, since we already have the global writeLock
 */
inline void BoundedVariableElimination::removeClausesThreadSafe(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const vector<CRef> & list, const Lit l, const int limit, SpinLock & data_lock, SpinLock & heap_lock, ParBVEStats & stats, int & garbageCounter, const bool doStatistics)
{
    const Var ignore = var(l);
    for (int cr_i = 0; cr_i < list.size(); ++cr_i)
    {
        const CRef cr = list[cr_i];
        if (CRef_Undef == cr)
            continue;
        Clause & c = ca[cr];
        if (!c.can_be_deleted())
        {
            c.set_delete(true);
            didChange();
            if (config.opt_minimal_updates)
            {
                for (int i = 0; i < c.size(); ++i) 
                    data.deletedVar(var(c[i]));
                garbageCounter += ca.clauseWord32Size(c.size(), c.has_extra());
            }
            else if (config.heap_updates > 0 && config.opt_bve_heap != 2)
                data.removedClause(cr, &heap, config.heap_updates == 2, ignore, &data_lock, &heap_lock); // updates stats and deleteTimer
            else 
                data.removedClause(cr, NULL, false, ignore, &data_lock, NULL);

            if (! c.learnt() /*&& cr < limit*/) {
                data_lock.lock();
                data.addToExtension(cr, l);
                data_lock.unlock();
            }
            if (doStatistics)
            {
                if (c.learnt())
                {
                    ++stats.removedLearnts;
                    stats.learntLits += c.size();
                }
                else
                {

                    ++stats.removedClauses;
                    stats.removedLiterals += c.size();
                }
            }
            if(config.opt_bve_verbose > 1){
                cerr << "c removed clause: " << c << endl;
                cerr << "c added to extension with Lit " << l << endl;;
            }
        }

        //Delete Clause from all Occ-Lists TODO too much overhead?
        /*for (int j = 0; j < c.size(); ++j)
            if (c[j] != l)
                data.removeClauseFrom(cr,c[j]);
        list[cr_i] = list[list.size() - 1];
        list.pop_back();*/
    }

}

/*
 *  anticipates following numbers:
 *  -> number of resolvents derived from specific clause:       pos_stats / neg_stats
 *  -> total number of literals in clauses after resolution:    lit_clauses
 *  -> total number of literals in learnts after resolution:    lit_learnts
 *
 */
inline lbool BoundedVariableElimination::anticipateEliminationThreadsafe(CoprocessorData& data, vector< Minisat::CRef >& positive, vector< Minisat::CRef >& negative, const int v, const int p_limit, const int n_limit, vec< Lit >& resolvent, vec < int32_t > &  pos_stats, vec < int32_t > & neg_stats, int& lit_clauses, int& lit_learnts, int& new_clauses, int& new_learnts, SpinLock& data_lock, BoundedVariableElimination::ParBVEStats& stats, int64_t& bveChecks, const bool doStatistics)
{
    if(config.opt_bve_verbose > 2)  cerr << "c starting anticipate BVE" << endl;
    // Clean the stats
    lit_clauses=0;
    lit_learnts=0;
   
    const bool hasDefinition = (p_limit < positive.size() || n_limit < negative.size() );
    
    for (int cr_p = 0; cr_p < positive.size(); ++cr_p)
    {
        const CRef crPos = positive[cr_p];
        if (CRef_Undef == crPos)
            continue;
        Clause & p = ca[crPos];
        if (p.can_be_deleted())
        {  
            if(config.opt_bve_verbose > 2) cerr << "c    skipped p " << p << endl;
            continue;
        }
        for (int cr_n = 0; cr_n < negative.size(); ++cr_n)
        {
	    // do not check resolvents, which would touch two clauses out of the variable definition
	    if( cr_p >= p_limit && cr_n >= n_limit ) continue; 
	    if( hasDefinition && cr_p < p_limit && cr_n < n_limit ) continue; // no need to resolve the definition clauses with each other NOTE: assumes that these clauses result in tautologies
            const CRef crNeg = negative[cr_n];
            if (CRef_Undef == crNeg)
                continue;
	    bveChecks ++;
            Clause & n = ca[crNeg];
            if (n.can_be_deleted())
            {   
                if(config.opt_bve_verbose > 2)
                {
                    cerr << "c    skipped n " << n << endl;
                }
                continue;
            }
            int newLits = tryResolve(p, n, v);

            if(config.opt_bve_verbose > 2) cerr << "c    resolvent size " << newLits << endl;
            
            // Clause Size > 1
            if (newLits > 1)
            {
                if(config.opt_bve_verbose > 2)  
                {   
                    cerr << "c    Clause P: " << p << endl; 
                    cerr << "c    Clause N: " << n << endl; 
                    cerr  << "c    Resolvent: "; 
                    vec<Lit> resolvent; 
                    resolve(p,n,v,resolvent); 
                    printLitVec(resolvent);
                }
                if (p.learnt() || !n.learnt()) // don't increment blocking-stats for p,
                    ++pos_stats[cr_p];         // if p is original and n learnt
                                               // goal: detect that p is blocked by all orig. n-clauses
                if (n.learnt() || !p.learnt()) // vice versa 
                    ++neg_stats[cr_n];
                if (p.learnt() || n.learnt())
                {
                    if (    (config.opt_resolve_learnts > 1 
                                || config.opt_resolve_learnts > 0 && !(p.learnt() && n.learnt())
                            ) && newLits <= max(p.size(),n.size()) + config.opt_learnt_growth) {
                        lit_learnts += newLits;
                        ++new_learnts;
                    }
                }
                else 
                {
                    lit_clauses += newLits;
                    ++new_clauses;
                }
            }
            
            // empty Clause
            else if (newLits == 0)
            {
                if(config.opt_bve_verbose > 2) 
                {
                    cerr << "c    empty resolvent" << endl;
                    cerr << "c    Clause P: " << p << endl; 
                    cerr << "c    Clause N: " << n << endl;
                    cerr << "c    finished anticipate_bve by finding empty clause" << endl;
                }
                data.setFailed();
                return l_False; 
            }
            
            // unit Clause
            else if (newLits == 1)
            {
                resolvent.clear();
                resolve(p,n,v,resolvent); 
                assert(resolvent.size() == 1);
                if(config.opt_bve_verbose > 0) 
                {
                    cerr << "c    Unit Resolvent: ";
                    printLitVec(resolvent);
                }   
                if(config.opt_bve_verbose > 2)
                {
                    cerr << "c    Clause P: " << p << endl; 
                    cerr  << "c     Clause N: " << n << endl; 
                }
                data_lock.lock();
                lbool status = data.enqueue(resolvent[0]); //check for level 0 conflict
                data_lock.unlock();
                if (status == l_False)
                {
                    if(config.opt_bve_verbose > 2) cerr << "c finished anticipate_bve with conflict" << endl;
                    return l_False;
                }
                else if (status == l_Undef)
                     ; // variable already assigned
                else if (status == l_True)
                {
                    if (doStatistics)
                        ++stats.unitsEnqueued;
                }
                else 
                    assert (0); //something went wrong
            }

            if(config.opt_bve_verbose > 2) cerr << "c ------------------------------------------" << endl;
        }
    }
    if(config.opt_bve_verbose > 2) 
    {
        for (int i = 0; i < positive.size(); ++i)
            cerr << "c pos stat("<< i <<"): " << (unsigned) pos_stats[i] << endl;;
        for (int i = 0; i < negative.size(); ++i)
            cerr << "c neg stat("<< i <<"): " << (unsigned) neg_stats[i] << endl;;

        cerr << "c finished anticipate_bve normally" << endl;
    }
    return l_Undef;
}

/**
 *   threadsafe variant of resolve set, 
 *   assumption: Write Lock is holded, i.e. exclusive read and write access to data object and clause allocator
 *
 *   performes resolution and 
 *   allocates resolvents c, with |c| > 1, in ClauseAllocator 
 *   as learnts or clauses respectively
 *   and adds them in data object
 *
 *   - resolvents that are tautologies are skipped 
 *   - unit clauses and empty clauses are not handeled here
 *          -> this is already done in anticipateElimination 
 */
lbool BoundedVariableElimination::resolveSetThreadSafe(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, vector<CRef> & positive, vector<CRef> & negative, const int v, const int p_limit, const int n_limit, vec<Lit> & ps, AllocatorReservation & memoryReservation, deque<CRef> & strengthQueue, ParBVEStats & stats, SpinLock & data_lock, SpinLock & heap_lock, int expectedResolvents, int64_t& bveChecks, const bool doStatistics, const bool keepLearntResolvents)
{
    int resolvents = 0;
    const bool hasDefinition = (p_limit < positive.size() || n_limit < negative.size() );
    for (int cr_p = 0; cr_p < positive.size(); ++cr_p)
    {
        const CRef crPos = positive[cr_p];
        if (CRef_Undef == crPos)
            continue;
        Clause & p = ca[crPos];
        if (p.can_be_deleted())
            continue;
        for (int cr_n = 0; cr_n < negative.size(); ++cr_n)
        {
	    // no need to resolve two clauses that are both not within the variable definition
	    if( cr_p >= p_limit && cr_n >= n_limit ) continue;
	    if( hasDefinition && cr_p < p_limit && cr_n < n_limit ) continue; // no need to resolve the definition clauses with each other NOTE: assumes that these clauses result in tautologies
            const CRef crNeg = negative[cr_n];
            if (CRef_Undef == crNeg)
                continue;
	    
	    bveChecks ++;
            Clause & n = ca[crNeg];
            if (n.can_be_deleted())
                continue;

            // Dont compute resolvents for learnt clauses
            if (config.opt_resolve_learnts == 0 && (p.learnt() || n.learnt()))
               continue;
            if (config.opt_resolve_learnts == 1 && (p.learnt() && n.learnt()))
               continue;

            ps.clear();
            if (!resolve(p, n, v, ps))
            {
               // | resolvent | > 1
               if (ps.size()==1)
               {
                data_lock.lock();
                lbool status = data.enqueue(resolvent[0]); //check for level 0 conflict
                data_lock.unlock();
	       } else if (ps.size()>1)
               {
                    if ((p.learnt() || n.learnt()) && ps.size() > max(p.size(),n.size()) + config.opt_learnt_growth)
                        continue;
                    resolvents++;
                    if (false) 
                    {
                        cerr <<  "c on variable " << v + 1 << " with pos size: " << positive.size() << " negs: " << negative.size() <<endl;
                        cerr << "c resolving " << resolvents << " of " << expectedResolvents << " at adress " << memoryReservation.getCurrent() << " with limit " << memoryReservation.getUpperLimit() << endl; 
                    }
                    const CRef cr = ca.allocThreadsafe(memoryReservation, ps, p.learnt() || n.learnt());
                    Clause & resolvent = ca[cr];
                    if (config.opt_minimal_updates)
                    {
                        // just add to occs
                        data_lock.lock();  
                        for (int l = 0; l < resolvent.size(); ++l)
                            data.list(resolvent[l]).push_back(cr);
                        data_lock.unlock();
                    }
                    else if (config.heap_updates > 0 && config.opt_bve_heap != 2)
                        data.addClause(cr, &heap, config.heap_updates == 2, v, &data_lock, &heap_lock);
                    else 
                        data.addClause(cr, NULL, false, var_Undef, &data_lock, NULL);

                    data_lock.lock();
                    if (resolvent.learnt()) 
                        data.getLEarnts().push(cr);
                    else 
                        data.getClauses().push(cr);
                    data_lock.unlock();
                    // add clause to local subsimp queues
                    strengthQueue.push_back(cr);
                    
                    if (doStatistics)
                    {
                        if (resolvent.learnt())
                        {
                            ++stats.newLearnts;
                            ++stats.newLearntLits;

                        } else 
                        {
                            ++stats.createdClauses;
                            stats.createdLiterals += resolvent.size();
                        }
                    }
               }
           }
        }

    }
    return l_Undef;
}

/* this function removes Clauses that have no resolvents, threadsafe version with data_lock
 * i.e. all resolvents are tautologies
 *
 */
inline void BoundedVariableElimination::removeBlockedClausesThreadSafe(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const vector< CRef> & list, const int32_t _stats[], const Lit l, const int limit, SpinLock & data_lock, SpinLock & heap_lock, ParBVEStats & stats, int & garbageCounter, const bool doStatistics)
{
   const Var ignore = var(l);
   for (unsigned ci = 0; ci < list.size(); ++ci)
   {    
        const CRef cr = list[ci];
        if (CRef_Undef == cr)
            continue;
        Clause & c =  ca[cr];
        if (c.can_be_deleted())
            continue;
        if (_stats[ci] == 0)
        {
            didChange();
            c.set_delete(true);
            if (config.opt_minimal_updates)
            {
                for (int i = 0; i < c.size(); ++i) 
                    data.deletedVar(var(c[i]));
                garbageCounter += ca.clauseWord32Size(c.size(), c.has_extra());
            }
            else if (config.heap_updates > 0 && config.opt_bve_heap != 2)
                data.removedClause(cr, &heap, config.heap_updates == 2, ignore, &data_lock, &heap_lock); // updates stats and deleteTimer
            else 
                data.removedClause(cr, NULL, false, var_Undef, &data_lock, NULL);
            if(! c.learnt() /* && cr < limit*/)
            {
                data_lock.lock();
                data.addToExtension(cr, l);
                data_lock.unlock();
            }
            if (doStatistics)
            {
                if (c.learnt())
                {
                    ++stats.removedBlockedLearnt;
                    stats.learntBlockedLit += c.size();
                }
                else
                {
                    ++stats.removedBC; 
                    stats.blockedLits += c.size();
                }
            }
            if(config.opt_bve_verbose > 1 || (config.opt_bve_verbose > 0 && ! c.learnt())) 
            {
                cerr << "c removed clause: " << c << endl;
                cerr << "c added to extension with Lit " << l << endl;;
            }
        }
   }
}

void* BoundedVariableElimination::runParallelBVE(void* arg)
{
  BVEWorkData*      workData = (BVEWorkData*) arg;
  workData->bve->par_bve_worker(*(workData->data), *(workData->heap), *(workData->strengthQueue), *(workData->sharedStrengthQueue), *(workData->postponed), *(workData->var_locks), *(workData->rw_lock), *(workData->bveStats), workData->gateMarkArray, workData->rwlock_count, workData->garbageCounter, workData->bveStats->parBveChecks); 
  return 0;
}

void BoundedVariableElimination::parallelBVE(CoprocessorData& data)
{
  printDRUPwarning(cerr,"parallel BVE"); // warnings that certain things are not supported (yet)
  printExtraInfowarning(cerr,"parallel BVE");
  
  if (data.hasToPropagate()) {
    if (propagation.process(data, true) == l_False)
      return;
    else 
        modifiedFormula = modifiedFormula || propagation.appliedSomething();
  }
  const bool doStatistics = true;
  if (doStatistics) processTime = wallClockTime() - processTime;
  
  lastTouched.resize(data.nVars());
  VarOrderBVEHeapLt comp(data, config.opt_bve_heap);
  Heap<VarOrderBVEHeapLt> newheap(comp);
#ifdef __APPLE__
  BVEWorkData *workData=new BVEWorkData[ controller.size() ];
  MethodFree mf(workData);
#else
  BVEWorkData workData[ controller.size() ];
#endif
  jobs.resize( controller.size() );
  variableLocks.resize(data.nVars() + 5); // 5 extra SpinLock for data, heap, ca, shared subsume-queue, shared strength-queue
  strengthQueues.resize(controller.size());
  postpones.resize(controller.size());
  parStats.resize(controller.size());
  dirtyOccs.resize(data.nVars() * 2);
  // use also for neighbors
  if ( true || config.opt_bve_findGate) 
  {
      gateMarkArrays.resize(controller.size());
      for (int i = 0; i < controller.size(); ++i)
          gateMarkArrays[i].resize(config.opt_bve_findGate ? data.nVars() * 2 : data.nVars());
  }
  
 for ( int i = 0 ; i < controller.size(); ++ i ) 
  {
    workData[i].bve   = this;
    workData[i].data  = &data; 
    workData[i].var_locks = & variableLocks;
    workData[i].rw_lock = & allocatorRWLock;
    workData[i].heap  = &newheap;
    workData[i].strengthQueue = & strengthQueues[i];
    workData[i].sharedStrengthQueue = & sharedStrengthQueue;
    workData[i].postponed = & postpones[i];
    workData[i].bveStats = & parStats[i];
    if (true || config.opt_bve_findGate) workData[i].gateMarkArray = & gateMarkArrays[i];
  }

  if (config.opt_bve_heap != 2)
  {
    data.getActiveVariables(lastDeleteTime(), newheap);
  }
  else 
  {
    data.getActiveVariables(lastDeleteTime(), variable_queue);
  }
  
  bool reachedLimit = false; // indicate if enough steps have been performed
  while ( ((config.opt_bve_heap != 2 && newheap.size() > 0) || (config.opt_bve_heap == 2 && variable_queue.size() > 0))
    && !data.isInterupted()
    && !reachedLimit
  )
  {

    updateDeleteTime(data.getMyDeleteTimer());
    
    uint32_t timer = dirtyOccs.nextStep();

    progressStats(data, false);

    int QSize = ((config.opt_bve_heap != 2) ? newheap.size() : variable_queue.size()); 
    ReadersWriterLock allocatorRWLock;
    if (config.opt_par_bve == 2 || (QSize > config.par_bve_threshold && config.opt_par_bve == 1))
    {
        for ( int i = 0 ; i < controller.size(); ++ i ) 
        {
          jobs[i].function  = BoundedVariableElimination::runParallelBVE;
          workData[i].rw_lock = & allocatorRWLock;
          workData[i].garbageCounter = 0;
          jobs[i].argument  = &(workData[i]);
        }
        if(config.opt_bve_verbose>0) cerr << "c parallel bve with " << controller.size() << " threads on " << QSize << " variables" << endl;
        pthread_rwlock_t mutex = allocatorRWLock.getValue(); // FIXME reicht hier auch eine reference?
#ifndef __APPLE__ // Does not work on OS-X
        assert (mutex.__data.__nr_readers == 0);
        assert (mutex.__data.__readers_wakeup == 0);
        assert (mutex.__data.__writer_wakeup == 0);
        assert (mutex.__data.__nr_readers_queued == 0);
        assert (mutex.__data.__writer == 0);
        assert (mutex.__data.__lock == 0);
#endif
        controller.runJobs( jobs );

        if (!data.ok())
        {
          if (doStatistics) processTime = wallClockTime() - processTime;
          return;
        }
        // clean dirty occs
        data.cleanUpOccurrences(dirtyOccs,timer);
        if (config.opt_minimal_updates)
        {
            for (int i = 0; i < controller.size(); ++i) 
            {
                if (workData[i].garbageCounter > 0) ca.freeLit(workData[i].garbageCounter);
            }
        }
    }
    else
    {
        if (config.opt_bve_findGate) data.ma.resize( data.nVars() * 2 );
        if(config.opt_bve_verbose>0) cerr << "c sequentiel bve on " << QSize << " variables" << endl;
        int parBveStepSum = 0; 
        for (int i = 0; i < controller.size(); ++i)
            parBveStepSum += parStats[i].parBveChecks;
        seqBveSteps += parBveStepSum / controller.size();
        bve_worker (data, newheap,seqBveSteps);
        seqBveSteps -= parBveStepSum / controller.size();
    }
    //propagate units
    if (data.hasToPropagate()) {
      if (l_False == propagation.process(data, true))
      {
        if (doStatistics) processTime = wallClockTime() - processTime;
        return;
      }
      modifiedFormula = modifiedFormula || propagation.appliedSomething();
    }
    for ( int i = 0 ; i < controller.size(); ++ i ) 
    {
        assert(strengthQueues[i].size() == 0);
    }
    assert(sharedStrengthQueue.size() == 0);
    data.checkGarbage();
    
    // add active variables and clauses to variable heap and subsumption queues
    data.getActiveVariables(lastDeleteTime(), touched_variables);
    touchedVarsForSubsumption(data, touched_variables);

    if (doStatistics) subsimpTime = wallClockTime() - subsimpTime;
    subsumption.process();
    if (subsumption.appliedSomething())
        didChange();
    if (doStatistics) subsimpTime = wallClockTime() - subsimpTime;
    modifiedFormula = modifiedFormula || subsumption.appliedSomething();

    if (config.opt_bve_heap != 2)
        newheap.clear();
    else
        variable_queue.clear();
    
    for (int i = 0; i < touched_variables.size(); ++i)
    {
        if (config.opt_bve_heap != 2)
            newheap.insert(touched_variables[i]);
        else 
            variable_queue.push_back(touched_variables[i]);
    }
    touched_variables.clear();
  }

  progressStats(data, false);
  if (doStatistics) processTime = wallClockTime() - processTime;
}

/** lock-based parallel non-naive strengthening-methode
 * @param data object
 * @param start where to start strengthening in strengtheningqueue
 * @param end where to stop strengthening
 * @param var_lock vector of locks for each variable
 *
 * @param strength_resolvents : if activated, strengthener wont be locked
 *                              to use directly after VE when all locks are
 *                              already hold by the thread
 * 
 * Idea of strengthening Lock:
 * -> lock fst variable of strengthener
 * -> lock strengthener
 * -> if fstvar(other) <= fstvar(strengthener)
 *      -> lock other
 */
void BoundedVariableElimination::par_bve_strengthening_worker(CoprocessorData& data, Heap<VarOrderBVEHeapLt> & heap, const Var ignore, vector< SpinLock > & var_lock, ReadersWriterLock & rwlock, deque<CRef> & sharedStrengthQueue, deque<CRef> & localQueue, MarkArray & dirtyOccs, ParBVEStats & stats, int & rwlock_count, int & garbageCounter, const bool strength_resolvents, const bool doStatistics)
{ 
  assert(data.nVars() <= var_lock.size() && "var_lock vector to small");
//  if (doStatistics)
//    stats.strengthTime = cpuTime() - stats.strengthTime;
 
  SpinLock & data_lock = var_lock[data.nVars()];
  SpinLock & strength_lock   = var_lock[data.nVars() + 4];

  while (data.ok() && ((!strength_resolvents && sharedStrengthQueue.size() > 0) || localQueue.size() > 0))
  {
    CRef cr = CRef_Undef;
    if( localQueue.size() == 0 ) {
        assert(!strength_resolvents);
        strength_lock.lock();
        if (sharedStrengthQueue.size() > 0)
        {
            cr = sharedStrengthQueue.back();
            sharedStrengthQueue.pop_back();
        }
        strength_lock.unlock();
    } else {
      // TODO: have a counter for this situation!
      cr = localQueue.back();
      localQueue.pop_back();
    }

    if (cr == CRef_Undef)
    {
        assert( ! strength_resolvents );
        break;
    }

    if (!strength_resolvents){
        assert(rwlock_count == 0);
        rwlock_count++;
        rwlock.readLock();
    }

    Var fst = var(ca[cr][0]);
    
    // No locking if strength_resolvents
    if (!strength_resolvents) 
    {
        lock_strengthener_nn: // readlock @ this point
        if (ca[cr].can_be_deleted() || ca[cr].size() == 0)
        {
             assert(rwlock_count == 1);
             --rwlock_count;
            rwlock.readUnlock();
            continue;
        }
        fst = var(ca[cr][0]);
        assert(rwlock_count == 1);
        --rwlock_count;
        rwlock.readUnlock();

        // lock 1st var 
        var_lock[fst].lock();

        assert(rwlock_count == 0);
        rwlock_count++;
        rwlock.readLock();
        // lock strengthener
        ca[cr].spinlock();

        // assure that clause can still strengthen
        if (ca[cr].can_be_deleted() || ca[cr].size() == 0)
        {
            ca[cr].unlock();
            assert(rwlock_count == 1);
            --rwlock_count;
            rwlock.readUnlock();
            var_lock[fst].unlock();
            continue;
        }
        
        // assure that first var still valid
        if (var(ca[cr][0]) != fst)
        {
            ca[cr].unlock();
            assert(rwlock_count == 1);
            --rwlock_count;
            rwlock.readUnlock();
            var_lock[fst].unlock();
            assert(rwlock_count == 0);
            rwlock_count++;
            rwlock.readLock();
            goto lock_strengthener_nn;
        }
    } 
   
    // readlock @ this point
    Clause& strengthener = ca[cr];

    // handle unit of empty strengthener
    if( strengthener.size() < 2 ) {
        if( strengthener.size() == 1 ) 
        {
            data_lock.lock();
                lbool status = data.enqueue(strengthener[0]); 
            data_lock.unlock();

            if (!strength_resolvents) 
            {
                strengthener.unlock();
                assert(rwlock_count == 1);
                --rwlock_count;
                rwlock.readUnlock();
                var_lock[fst].unlock(); // unlock fst var
            } // no readlock @ this point

            if( l_False == status ) break;
	        else continue;
        }
        else 
        { 
            data.setFailed();  // can be done asynchronously
            if (!strength_resolvents) 
            {
                strengthener.unlock();
                assert(rwlock_count == 1);
                --rwlock_count;
                rwlock.readUnlock();
                var_lock[fst].unlock(); 
            }
            break; 
        }
    }

    assert (strengthener.size() > 1 && "expect strengthener to be > 1");

    //find Lit with least occurrences and its occurrences
    // search lit with minimal occurrences
    Lit min = lit_Undef, nmin = lit_Undef;
    Lit minT = strengthener[0];
    for (int j = 1; j < strengthener.size(); ++j)
    {
       if (data[var(minT)] > data[var(strengthener[j])])
          minT = strengthener[j];
    }
    min = minT;
    nmin = ~minT;
     
    assert(min != nmin && "min and nmin should be different");
    vector<CRef>& list = data.list(min);        // occurrences of minlit from strengthener
    vector<CRef>& list_neg = data.list(nmin);   // occurrences of negated minlit from strengthener
    
    lbool state = strength_check_pos(data, heap, ignore, list, sharedStrengthQueue, localQueue, strengthener, cr,      fst, var_lock, dirtyOccs, stats, garbageCounter, strength_resolvents, doStatistics);
    if (l_False != state)
        strength_check_neg(data, heap, ignore, list_neg,     sharedStrengthQueue, localQueue, strengthener, cr, min, fst, var_lock, dirtyOccs, stats, garbageCounter, strength_resolvents, doStatistics);

    strengthener.set_strengthen(false);
    strengthener.set_subsume(false);

    // No locking if strength_resolvents
    if (!strength_resolvents)
    {
        strengthener.unlock();
        assert(rwlock_count == 1);
        --rwlock_count;
        rwlock.readUnlock();
        // free lock of first variable
        var_lock[fst].unlock();
    }
  }
  //if (doStatistics) stats.strengthTime = cpuTime() - stats.strengthTime;
}


/**
 * strengthening check for parallel non-naive strengthening
 *
 * Preconditions: 
 * fst is locked by this thread
 *
 * Thread-Saftey-Requirements
 * only smaller variables than fst are locked
 * write acces to data only if var_lock[nVars()] is locked
 * no data.list(Lit) are written
 *
 * Postconditions:
 * all locks, that were aquired, are freed
 *
 * @param strengthener 
 * @param list          a list with CRef to check for strengthening
 * @param var_lock      lock for each variable
 *
 */
inline lbool BoundedVariableElimination::strength_check_pos(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const Var ignore, vector < CRef > & list, deque<CRef> & sharedStrengthQueue, deque<CRef> & localQueue, Clause & strengthener, CRef cr, Var fst, vector < SpinLock > & var_lock, MarkArray & dirtyOccs, ParBVEStats & stats, int & garbageCounter, const bool strength_resolvents, const bool doStatistics) 
{
    int si, so;           // indices used for "can be strengthened"-testing
    int negated_lit_pos;  // index of negative lit, if we find one
 
    SpinLock & data_lock = var_lock[data.nVars()];
    SpinLock & heap_lock = var_lock[data.nVars() + 1];
    SpinLock & strength_lock   = var_lock[data.nVars() + 4];
    
    // test every clause, where the minimum is, if it can be strenghtened
    for (unsigned int j = 0; j < list.size(); ++j)
    {
      lock_to_strengthen_nn_pos:
      const CRef crO = list[j];
      if (CRef_Undef == crO) 
          continue;

      Clause& other = ca[crO];
      
      // a clause can not strengthen itself, and a clause can not strengther smaller clauses
      if (other.can_be_deleted() || crO == cr || other.size() < strengthener.size())
        continue;
      Lit other_fst_lit = other[0];
      Var other_fst = var(other[0]);
      

      // if the other_fst > fst, other cannot contain fst, and therefore strengthener cannot strengthen other
      // if other_fst < fst, then other has to be longer 
      if (other_fst > fst || other_fst < fst && other.size() <= strengthener.size())
          continue;

      // lock the other clause (we already tested it for beeing different from cr)
      // if false is returned: the first variable changed, and no lock was performed
      bool locked = other.spinlock(other_fst_lit);
      if (false == locked)
        goto lock_to_strengthen_nn_pos;

      // check if other has been deleted, while waiting for lock
      if (other.can_be_deleted() || other.size() <= strengthener.size())
      {
         other.unlock();
         continue;
      }

      // check if others first lit has changed, while waiting for lock
      if (var(other[0]) != other_fst)
      {
         other.unlock();
         goto lock_to_strengthen_nn_pos;
      }
      
      // now other is locked
      if (doStatistics) ++stats.subsimpSteps;
      // test if we can strengthen other clause
      si = 0;
      so = 0;
      negated_lit_pos = -1;  //the position for neglit cant be 0, so we will use this as "neglit not found"
      while (si < strengthener.size() && so < other.size())
      {
        if(strengthener[si] == other[so])
        {
          // the lits are the same in both clauses
          ++si;
          ++so;
        }
        else if (strengthener[si] == ~other[so])
        {
          // found neglit...
          if (negated_lit_pos == -1)
          {
            // if it's the first neglit found, save its position
            negated_lit_pos = so;
            ++si;
            ++so;
          }
          else
            break;  // found more than 1 negated lit, can't strengthen
        }
        else if (strengthener[si] < other[so])
          break;    // the other clause did not contain this variable => can't strengthen
        else
          ++so;
      }

      // subsumption 
      if (negated_lit_pos == -1 && si == strengthener.size())
      {
         other.set_delete(true);
         if (config.opt_bve_verbose > 2) cerr << "c " << strengthener << " subsumed " << other << endl;
         if (doStatistics) 
         {
             if (!other.learnt())
             {
                ++stats.subsumedClauses;
                stats.subsumedLiterals += other.size();
             }
             else
             {
                ++stats.subsumedLearnts;
                stats.subsumedLearntLiterals += other.size();
             }
         }
         if (strengthener.learnt() && !other.learnt())
             strengthener.set_learnt(false);       
      }
      // if subsumption successful, strengthen
      else if (negated_lit_pos >= 0 && si == strengthener.size())
      {
          if (doStatistics && other.learnt()) ++stats.strengthtLearntLits;
          else if (doStatistics) ++stats.strengthtLits;

          // unit found
          if (other.size() == 2)
          {
              other.set_delete(true);
              didChange();
              data_lock.lock();
              lbool state = data.enqueue(other[(negated_lit_pos + 1) % 2]);
              data_lock.unlock();   
              if (config.opt_minimal_updates)
              {
                for (int i = 0; i < other.size(); ++i) 
                    data.deletedVar(var(other[i]));
                garbageCounter += ca.clauseWord32Size(other.size(), other.has_extra());
              }
              else if (config.heap_updates > 0 && config.opt_bve_heap != 2)
                data.removedClause(crO, &heap, config.heap_updates == 2, ignore, &data_lock, &heap_lock); // updates stats and deleteTimer
              else 
                data.removedClause(crO, NULL, false, var_Undef, &data_lock, NULL);
              if (l_False == state)
              {
                  other.unlock();
                  return l_False;
              }
              if (state == l_True && doStatistics)
              {
                 ++stats.unitsEnqueued;
              }
          }
          //TODO optimize out
          else if (other.size() == 1)
          {
              assert(false && "no unit clauses should be strengthened");
              // empty -> fail
          }
          else
          {
              didChange();
              Lit neg = other[negated_lit_pos];
              if( config.opt_bve_verbose > 2 || global_debug_out ) cerr << "c remove " << neg << " from clause " << other << endl;
              
              //remove from occ-list (by overwriting cr with CRef_Undef
              data.removeClauseFromThreadSafe(crO, neg);
              dirtyOccs.setCurrentStep(toInt(neg));
              other.removePositionSortedThreadSafe(negated_lit_pos);
              if (config.opt_minimal_updates)
              {
                  data.deletedVar(var(neg));
                  ++garbageCounter; // do not update data structure
              }
              else if (config.heap_updates  > 0 && config.opt_bve_heap != 2)
                  data.removedLiteral(neg, 1, &heap, config.heap_updates == 2,ignore, &data_lock, &heap_lock);
              else 
                  data.removedLiteral(neg, 1, NULL, false, var_Undef, &data_lock, NULL);
/*              if ( ! other.can_subsume()) 
              {
                  other.set_subsume(true);
                  subsumeQueue.push_back(crO);
              } 
*/
              // keep track of this clause for further strengthening!
              if( !other.can_strengthen() ) 
              {
                other.set_strengthen(true);
                other.set_subsume(true);
                if (!strength_resolvents)
                    localQueue.push_back(crO);
                else 
                {
                    strength_lock.lock();
                    sharedStrengthQueue.push_back(crO);
                    strength_lock.unlock();
                }
              }          
          }
      }
      // unlock other
      other.unlock();
    }
    return l_Undef;
}

/**
 * strengthening check for the negated literal for parallel non-naive strengthening
 * i.e. the Literal that has to occur negated is already known
 *
 * Preconditions: 
 * fst is locked by this thread
 *
 * Thread-Saftey-Requirements
 * only smaller variables than fst are locked
 * write acces to data only if var_lock[nVars()] is locked
 * no data.list(Lit) are written
 *
 * Postconditions:
 * all locks, that were aquired, are freed
 *
 * @param strengthener 
 * @param list          a list with CRef to check for strengthening
 * @param var_lock      lock for each variable
 *
 */
inline lbool BoundedVariableElimination::strength_check_neg(CoprocessorData & data, Heap<VarOrderBVEHeapLt> & heap, const Var ignore, vector < CRef > & list, deque<CRef> & sharedStrengthQueue, deque<CRef> & localQueue, Clause & strengthener, CRef cr, Lit min, Var fst, vector < SpinLock > & var_lock, MarkArray & dirtyOccs, ParBVEStats & stats, int & garbageCounter, const bool strength_resolvents, const bool doStatistics) 
{
    int si, so;           // indices used for "can be strengthened"-testing
    int negated_lit_pos;  // index of negative lit, if we find one
 
    SpinLock & data_lock = var_lock[data.nVars()];
    SpinLock & heap_lock = var_lock[data.nVars() + 1];
    SpinLock & strength_lock = var_lock[data.nVars() + 4]; 
    // test every clause, where the minimum is, if it can be strenghtened
    for (unsigned int j = 0; j < list.size(); ++j)
    {
      lock_to_strengthen_nn_neg:
      const CRef crO = list[j];
      if (CRef_Undef == crO)
          continue;
      Clause& other = ca[crO];
      
      // a clause can not strengthen itself, and a clause can not strengther smaller clauses
      if (other.can_be_deleted() || crO == cr || other.size() < strengthener.size())
        continue;
      Lit other_fst_lit = other[0];
      Var other_fst = var(other[0]);

      // if the other_fst > fst, other cannot contain fst, and therefore strengthener cannot strengthen other
      // if other_fst < fst, then other has to be longer 
      if (other_fst > fst || other_fst < fst && other.size() <= strengthener.size())
          continue;

      // lock the other clause (we already tested it for beeing different from cr)
      // if false is returned: the first literal changed, and no lock was performed
      bool locked = other.spinlock(other_fst_lit);
      if (false == locked)
        goto lock_to_strengthen_nn_neg;

      // check if other has been deleted, while waiting for lock
      if (other.can_be_deleted() || other.size() < strengthener.size())
      {
         other.unlock();
         continue;
      }

      // check if others first lit has changed, while waiting for lock
      if (var(other[0]) != other_fst)
      {
         other.unlock();
         goto lock_to_strengthen_nn_neg;
      }
      
      // now other is locked
 
      if (doStatistics) ++stats.subsimpSteps;
      // test if we can strengthen other clause
      si = 0;
      so = 0;
      negated_lit_pos = -1;  //the position for neglit cant be -1, so we will use this as "neglit not found"
      while (si < strengthener.size() && so < other.size())
      {
        if(strengthener[si] == other[so])
        {
          // the lits are the same in both clauses
          ++si;
          ++so;
        }
        else if (other[so] == ~min)
        {
            negated_lit_pos = so;
            ++si;
            ++so;
        }
        else if (strengthener[si] < other[so])
          break;    // the other clause did not contain this variable => can't strengthen
        else
          ++so;
      }
      // subsumption TODO -> maybe just in pos strength check!
      // but it doesn't harm at this point (just takes longer?)
      if (negated_lit_pos == -1 && si == strengthener.size())
      {
         other.set_delete(true);
         didChange();
         if (config.opt_bve_verbose > 2) cerr << "c " << strengthener << " subsumed " << other << endl;
         if (doStatistics) 
         {
             if (!other.learnt())
             {
                ++stats.subsumedClauses;
                stats.subsumedLiterals += other.size();
             }
             else
             {
                ++stats.subsumedLearnts;
                stats.subsumedLearntLiterals += other.size();
             }
         }
         if (strengthener.learnt() && !other.learnt())
             strengthener.set_learnt(false);       
      }

      // if subsumption successful, strengthen
      else if (negated_lit_pos >= 0 && si == strengthener.size())
      {
          
          if (doStatistics && other.learnt()) ++stats.strengthtLearntLits;
          else if (doStatistics) ++stats.strengthtLits;

          // unit found
          if (other.size() == 2)
          {
              didChange();
              other.set_delete(true);
              data_lock.lock();
              lbool state = data.enqueue(other[(negated_lit_pos + 1) % 2]);
              data_lock.unlock();   
              if (config.opt_minimal_updates)
              {
                for (int i = 0; i < other.size(); ++i) 
                    data.deletedVar(var(other[i]));
                garbageCounter += ca.clauseWord32Size(other.size(), other.has_extra());
              }
              else if (config.heap_updates > 0 && config.opt_bve_heap != 2)
                data.removedClause(crO, &heap, config.heap_updates == 2,ignore, &data_lock, &heap_lock); // updates stats and deleteTimer
              else 
                data.removedClause(crO, NULL, false, var_Undef, &data_lock, NULL);
              if (l_False == state)
              {
                  other.unlock();
                  return l_False;
              }
              if (state == l_True && doStatistics)
              {
                 ++stats.unitsEnqueued;
              }
          }
          //TODO optimize out
          else if (other.size() == 1)
          {
              assert(false && "no unit clauses should be strengthened");
              // empty -> fail
          }
          else
          {
              Lit neg = other[negated_lit_pos];
              if( config.opt_bve_verbose > 2 || global_debug_out ) cerr << "c remove " << neg << " from clause " << other << endl;
              
              //remove from occ-list (by overwriting cr with CRef_Undef
              data.removeClauseFromThreadSafe( crO, neg );
              dirtyOccs.setCurrentStep(toInt(neg));

              other.removePositionSortedThreadSafe(negated_lit_pos);
              didChange();
              if (config.opt_minimal_updates)
              {
                  data.deletedVar(var(neg));
                  ++garbageCounter; // do not update data structure
              }
              else if (config.heap_updates > 0 && config.opt_bve_heap != 2)
                  data.removedLiteral(neg, 1, &heap, config.heap_updates == 2,ignore, &data_lock, &heap_lock);
              else 
                  data.removedLiteral(neg, 1, NULL, false, var_Undef, &data_lock, NULL);
/*              if ( ! other.can_subsume()) 
              {
                  other.set_subsume(true);
                  subsumeQueue.push_back( crO );
              } */
              // keep track of this clause for further strengthening!
              if( !other.can_strengthen() ) 
              {
                other.set_strengthen(true);
                if (!strength_resolvents)
                    localQueue.push_back( crO );
                else 
                {
                    strength_lock.lock();
                    sharedStrengthQueue.push_back( crO );
                    strength_lock.unlock();
                }
              }
          }
      }
      // unlock other
      other.unlock();
    }
    return l_Undef;
}

lbool BoundedVariableElimination::par_bve_propagate(CoprocessorData& data, Heap<VarOrderBVEHeapLt> & heap, const Var ignore, vector< SpinLock > & var_lock, ReadersWriterLock & rwlock, MarkArray & dirtyOccs, deque < CRef > & sharedSubsimpQueue, ParBVEStats & stats, int & rwlock_count, int & garbageCounter, const bool doStatistics)
{
  //processTime = cpuTime() - processTime;
  SpinLock & data_lock = var_lock[data.nVars()];
  SpinLock & heap_lock = var_lock[data.nVars() + 1];
  SpinLock & strength_lock = var_lock[data.nVars() + 4];
  Solver* solver = data.getSolver();
  // propagate all literals that are on the trail but have not been propagated
  while (data.ok() && data.hasToPropagate())
  {
    data.lock();

    const Lit l = (solver->qhead < solver->trail.size()) ? solver->trail[solver->qhead] : lit_Undef;
    if (lit_Undef == l)
    {
      data.unlock();
      break;
    }
    else
    { 
      ++(solver->qhead);
      data.unlock();
    }
    
    const Var v = var(l);

    // Lock variable
    var_lock[v].lock();
    
    if (config.opt_bve_verbose > 2 || global_debug_out) cerr << "c UP propagating " << l << endl;

    data_lock.lock();
    data.log.log(upLevel,"propagate literal",l);
    data_lock.unlock();
    
    // Readlock on CA
    assert(rwlock_count == 0);
    rwlock_count++;
    rwlock.readLock();

    // remove positives
    vector<CRef> & positive = data.list(l);
    for( int i = 0 ; i < positive.size(); ++i )
    {
      const CRef cr = positive[i];
      if (CRef_Undef == cr)
        continue;
//      cerr << "cr: " << cr << " Undef " << CRef_Undef << endl;
      Clause & satisfied = ca[cr];
      if ( satisfied.can_be_deleted() ) // only track yet-non-deleted clauses
        continue;

      // lock satisfied
      satisfied.spinlock();

      if( config.opt_bve_verbose > 2 || global_debug_out ) cerr << "c UP remove " << satisfied << endl;
      if (doStatistics)
      {
        if (satisfied.learnt())
        {
            ++stats.removedLearnts;
            stats.learntLits += satisfied.size();
        }
        else 
        { 
            ++stats.removedClauses;
            stats.removedLiterals += satisfied.size();
        }
      }
      satisfied.set_delete(true);
      satisfied.unlock();
      didChange();
      
      // overwrite CRef in Occ 
      
      dirtyOccs.setCurrentStep(toInt(l));
      positive[i] = CRef_Undef;

      if (config.opt_minimal_updates)
      {
        for (int i = 0; i< satisfied.size(); ++i) 
            data.deletedVar(var(satisfied[i]));
        garbageCounter += ca.clauseWord32Size(satisfied.size(), satisfied.has_extra());
      }
      else if (config.heap_updates > 0 && config.opt_bve_heap != 2)
        data.removedClause(cr, &heap, config.heap_updates == 2, ignore, &data_lock, &heap_lock); // updates stats and deleteTimer
      else 
        data.removedClause(cr, NULL, false, var_Undef, &data_lock, NULL);
      
   }

    const Lit nl = ~l;
    int countO = 0;
    int countL = 0;
    vector<CRef> & negative = data.list(nl);

    for( int i = 0 ; i < negative.size(); ++i )
    {
      const CRef cr = negative[i];
      if (CRef_Undef == cr)
          continue;

      Clause& c = ca[cr];
      if (c.can_be_deleted())
          continue;

      c.spinlock();

      // sorted propagation!
      if ( !c.can_be_deleted() ) 
      {
        for ( int j = 0; j < c.size(); ++ j ) 
          if ( c[j] == nl ) 
          { 
	        if( config.opt_bve_verbose > 2 || global_debug_out ) cerr << "c UP remove " << nl << " from " << c << endl;
                c.removePositionSorted(j);
	        break;
	    }
        if (c.learnt())  ++countL;
        else             ++countO;
      }
      // unit propagation
      data_lock.lock();
      if ( c.size() == 0 || (c.size() == 1 &&  solver->value( c[0] ) == l_False) ) 
      {
        data.setFailed();   // set state to false
        data_lock.unlock();

        if (config.opt_bve_verbose > 2 || global_debug_out) cerr << "c UNSAT by UP" << endl;
        c.set_delete(true); // TODO it seems safer to do this, is it necessary
        c.unlock();

        // End Readlock
        assert(rwlock_count == 1);
        --rwlock_count;
        rwlock.readUnlock();
        var_lock[v].unlock();

        return l_False;
      } 
      else if( c.size() == 1 ) 
      {
         if( solver->value( c[0] ) == l_Undef && (global_debug_out || config.opt_bve_verbose > 2) )
             cerr << "c UP enqueue " << c[0] << " with previous value " 
                  << (solver->value( c[0] ) == l_Undef ? "undef" : (solver->value( c[0] ) == l_False ? "unsat" : " sat ") ) << endl;
	     if( solver->value( c[0] ) == l_Undef ) 
         {
           solver->uncheckedEnqueue(c[0]);
         }
         didChange();
         c.set_delete(true);
         data_lock.unlock();
         if (config.opt_minimal_updates)
         {
            for (int i = 0; i < c.size(); ++i) 
                data.deletedVar(var(c[i]));
            garbageCounter += ca.clauseWord32Size(c.size(), c.has_extra());
         }
         else if (config.heap_updates > 0 && config.opt_bve_heap != 2)
            data.removedClause(cr, &heap, config.heap_updates == 2, ignore, &data_lock, &heap_lock); // updates stats and deleteTimer
         else 
            data.removedClause(cr, NULL, false, var_Undef, &data_lock, NULL);
         if (doStatistics) 
         {
             if (c.learnt())  ++countL; 
             else ++countO;
             ++stats.unitsEnqueued;
         }
      }
      else
      { 
         data_lock.unlock();
         didChange();
         if (true && ! c.can_strengthen())
         {
            c.set_strengthen(true);
            c.set_subsume(true);
            strength_lock.lock();
            sharedSubsimpQueue.push_back(cr);
            strength_lock.unlock();
         }
      }        
      c.unlock();
      negative[i] = CRef_Undef;
      dirtyOccs.setCurrentStep(toInt(nl));
    }

    // End Readlock
    assert(rwlock_count == 1);
    --rwlock_count;
    rwlock.readUnlock();

    // update formula data!
    if (config.opt_minimal_updates)
    {
      data.deletedVar(var(nl));
      garbageCounter += countL + countO; // do not update data structure
    }
    else if (config.heap_updates > 0 && config.opt_bve_heap != 2)
      data.removedLiteral(nl, countL + countO, &heap, config.heap_updates == 2,ignore, &data_lock, &heap_lock);
    else 
      data.removedLiteral(nl, countL + countO, NULL, false, var_Undef, &data_lock, NULL);
    
    if (doStatistics) 
    {
        stats.removedLiterals += countO;
        stats.learntLits      += countL;
    }
    var_lock[v].unlock();
  }
  
  return data.ok() ? l_Undef : l_False;
}
