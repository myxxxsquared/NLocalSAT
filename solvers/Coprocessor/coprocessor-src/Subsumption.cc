/**********************************************************************************[Subsumption.cc]
Copyright (c) 2012, Kilian Gebhardt, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Subsumption.h"
using namespace Coprocessor;


// options


Subsumption::Subsumption( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Propagation& _propagation )
: Technique( _config, _ca, _controller )
, data(_data)
, propagation( _propagation )
, subsumedClauses(0)
, subsumedLiterals(0)
, removedLiterals(0)
, subsumeSteps(0)
, strengthSteps(0)
, processTime(0)
, strengthTime(0)
, subLimit(config.opt_sub_subLimit)
, strLimit(config.opt_sub_strLimit)
, callIncrease(config.opt_sub_callIncrease)
, limitIncreases(0)
{
}

void Subsumption::giveMoreSteps()
{
  if( !willSimplify() ) return;
  subsumeSteps = subsumeSteps < config.opt_sub_inpStepInc ? 0 : subsumeSteps - config.opt_sub_inpStepInc;
  strengthTime = strengthTime < config.opt_sub_inpStepInc ? 0 : strengthTime - config.opt_sub_inpStepInc;
}


void Subsumption::printStatistics(ostream& stream)
{
stream << "c [STAT] SuSi(1) " << processTime << " s, " 
                              << subsumedClauses << " cls, " 
			       << " with " << subsumedLiterals << " lits, "
			       << removedLiterals << " strengthed "
			       << endl;
stream << "c [STAT] SuSi(2) " << subsumeSteps << " subs-steps, " 
                              << strengthSteps << " strenght-steps, " 
			      << limitIncreases << " increases, "
			       << strengthTime << "s strengthening "
			       << endl;
    for (int i = 0; i < controller.size(); ++i)
    {
        stream << "c [STAT] SuSi(1)-Thread " << i << " "
                           << localStats[i].processTime << " s, " 
                                      << localStats[i].subsumedClauses << " cls, " 
                           << " with " << localStats[i].subsumedLiterals << " lits, "
                           << localStats[i].removedLiterals << " strengthed "
                           << endl;
        stream << "c [STAT] SuSi(2)-Thread " << i << " " 
                           << localStats[i].subsumeSteps << " subs-steps, " 
                                      << localStats[i].strengthSteps << " strenght-steps, " 
                           << localStats[i].strengthTime << "s strengthening "
                           << localStats[i].lockTime << "s locking "
                           << endl;
    }
}

void Subsumption::resetStatistics()
{
    if (localStats.size() < controller.size()) 
        localStats.resize(controller.size());
    for (int i = 0; i < controller.size(); ++i)
    {
        localStats[i].removedLiterals = 0;
        localStats[i].strengthSteps = 0;
        localStats[i].subsumedClauses = 0;
        localStats[i].subsumedLiterals = 0;
        localStats[i].subsumeSteps = 0;
        localStats[i].processTime = 0;
        localStats[i].strengthTime = 0;
        localStats[i].lockTime = 0;
    }
    

}

bool Subsumption::process(bool doStrengthen, Heap< VarOrderBVEHeapLt >* heap, const Var ignore, const bool doStatistics)
{
  modifiedFormula = false;
  
  if( config.opt_sub_debug > 1 ) cerr << "c call susi process with subs: " << data.getSubsumeClauses() << " and str: " <<  data.getStrengthClauses() << endl;
  
  if( !data.ok() ) return false;
  if( !performSimplification() ) { // if nothing to be done, at least clean all the lists!
    if( config.opt_sub_debug > 1 ) cerr << "c reject susi due to penalty" << endl;
    for( int i = 0 ; i < data.getSubsumeClauses().size(); ++ i ) ca[ data.getSubsumeClauses()[i] ].set_subsume(false);
    data.getSubsumeClauses().clear();
    for( int i = 0 ; i < data.getStrengthClauses().size(); ++ i ) ca[ data.getStrengthClauses()[i] ].set_strengthen(false);
    data.getStrengthClauses().clear();
    return false; // do not execute simplification?
  }
  
  // do not simplify, if the formula is considered to be too large!
  if( !data.unlimited() && ( data.nVars() > config.opt_subsimp_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_subsimp_cls && data.nTotLits() > config.opt_subsimp_lits ) ) return false;
  
  // increase limits per call if necessary
  if( subsumeSteps + callIncrease > subLimit )  { subLimit = subsumeSteps + callIncrease;  limitIncreases++; }
  if( strengthSteps + callIncrease > strLimit ) { strLimit = strengthSteps + callIncrease; limitIncreases++; }
  
  if( config.opt_sub_debug > 0 ) {
      cerr << "c check for subsumption: " << endl;
      for( int i = 0 ; i < data.getSubsumeClauses().size(); ++ i )  cerr << "c [" << i << "]("<<data.getSubsumeClauses()[i]<<") : " << ca[data.getSubsumeClauses()[i]] << endl;
      cerr << "c check for strengthening: " << endl;
      for( int i = 0 ; i < data.getStrengthClauses().size(); ++ i )  cerr << "c [" << i << "]("<<data.getStrengthClauses()[i]<<") : " << ca[data.getStrengthClauses()[i]] << endl;
  }
  
  while( data.ok() && (hasToSubsume() || hasToStrengthen() ))
  {
    if( hasToSubsume() ){
      fullSubsumption(heap, ignore, doStatistics);
      // clear queue afterwards
      for( int i = 0 ; i < data.getSubsumeClauses().size(); ++ i ) ca[ data.getSubsumeClauses()[i] ].set_subsume(false);
      data.getSubsumeClauses().clear();
    }
    if( hasToStrengthen() ) {
      if( !doStrengthen ) {
	// do not apply strengthening?
	for( int i = 0 ; i < data.getStrengthClauses().size(); ++ i ) ca[ data.getStrengthClauses()[i] ].set_strengthen(false);
	data.getStrengthClauses().clear();
	continue;
      }
      if (controller.size() > 0 && (config.opt_sub_par_strength == 2 || (data.getStrengthClauses().size() > config.opt_sub_par_str_minCls && config.opt_sub_par_strength == 1)))
      {
          parallelStrengthening(heap, ignore, doStatistics);
	  assert( data.getStrengthClauses().size() == 0 && "finished strengthening" );
      }
      else {
          int avgParStrengthSteps = 0; 
          for (int i = 0; i < localStats.size(); ++i) {
              avgParStrengthSteps += localStats[i].strengthSteps;
          }
          // increase seq StrengthSteps by parallel Avarage 
          if (controller.size() > 0) strengthSteps += avgParStrengthSteps / controller.size();

          fullStrengthening(heap, ignore, doStatistics); // corrects occs and counters by itself

          // decrease seq StrengthSteps by parallel Avarage again
          if (controller.size() > 0) strengthSteps -= avgParStrengthSteps / controller.size();

          if (config.opt_sub_allStrengthRes > 0)
          {
            for (int j = 0; j < toDelete.size(); ++j)
            {  
              Clause & c = ca[toDelete[j]]; 
              if (!c.can_be_deleted())
              {
                  c.set_delete(true);
		  data.addCommentToProof("remove from toDelete by strengthening");
		  data.addToProof(c,true); // delete this clause from the proof!
                  data.removedClause(toDelete[j], heap, ignore);
                  if (doStatistics)
                  {
                      removedLiterals += c.size();
                  }
              }
            }
            toDelete.clear(); 
            data.getStrengthClauses().swap(newClauses);
            newClauses.clear();
          }
      }
      // clear queue afterwards
      if (config.opt_sub_allStrengthRes == 0) {
	for( int i = 0 ; i < data.getStrengthClauses().size(); ++ i ) ca[ data.getStrengthClauses()[i] ].set_strengthen(false);
	data.getStrengthClauses().clear();
      }
    }
  }
  
  modifiedFormula = modifiedFormula || propagation.appliedSomething();
  if( !modifiedFormula ) unsuccessfulSimplification();
  return modifiedFormula;
}



bool Subsumption::hasToSubsume() const
{
  return data.getSubsumeClauses().size() > 0; 
}

lbool Subsumption::fullSubsumption(Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics)
{
  // run subsumption for the whole queue
  if( heap == 0 && controller.size() > 0 && (config.opt_sub_par_subs == 2 || config.opt_sub_par_subs == 1 && (data.getSubsumeClauses().size() > 100000 || ( data.getSubsumeClauses().size() > 50000 && 10*data.nCls() > 22*data.nVars() ) )) ) {
    parallelSubsumption(doStatistics); // use parallel, is some conditions have been met
    //data.correctCounters();    // 
  } else {
    int avgParSubsSteps = 0; 
    for (int i = 0; i < localStats.size(); ++i) {
      avgParSubsSteps += localStats[i].subsumeSteps;
    }
    // increase seq StrengthSteps by parallel Avarage 
    if (controller.size() > 0) subsumeSteps += avgParSubsSteps / controller.size();

    subsumption_worker(0,data.getSubsumeClauses().size(), heap, ignore, doStatistics); // performs all occ and stat-updates
    
    if (controller.size() > 0) subsumeSteps -= avgParSubsSteps / controller.size();
  }
  
  for( int i = 0 ; i < data.getSubsumeClauses().size(); ++ i ) ca[ data.getSubsumeClauses()[i] ].set_subsume(false);
  data.getSubsumeClauses().clear();
  // no result to tell to the outside
  return l_Undef; 
}

bool Subsumption::hasWork() const
{
  return hasToStrengthen() || hasToSubsume();
}


void Subsumption :: subsumption_worker ( unsigned int start, unsigned int end, Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics)
{
    vector < CRef > & occ_updates = subs_occ_updates;
    if (doStatistics)
    {
        processTime = cpuTime() - processTime;   
    }   
    if( config.opt_sub_debug > 1 ) cerr << "subsume from " << start << " to " << end << " with size " << data.getSubsumeClauses().size() << endl;
    
    if( config.opt_sub_preferLearned && data.isInprocessing() ) {
      // move all learned clauses to the back! == original clauses to the front
      int k = 0;
      for (int i = 0 ; i < data.getSubsumeClauses().size(); ++ i ) {
	const CRef cr = data.getSubsumeClauses()[i];
	Clause &c = ca[cr];
	if( !c.learnt() ) {
	  const CRef tmp = i; // pointer to old clause
	  data.getSubsumeClauses()[i] = data.getSubsumeClauses()[k];
	  data.getSubsumeClauses()[k] = data.getSubsumeClauses()[tmp];
	  k++; // move clause to front, increase counter for original variables
	}
	// simply ignore learned clauses!
      }
    }
    
    for (; end > start && !data.isInterupted()
      && ( data.unlimited() || (doStatistics && subsumeSteps < subLimit) )
      ;)
    {
        --end;
	const CRef cr = data.getSubsumeClauses()[end];
        Clause &c = ca[cr];
        if (c.can_be_deleted())
            continue;
        //find Lit with least occurrences
        Lit min = c[0];
        for (int l = 1; l < c.size(); l++)
        {
            if (data[c[l]] < data[min])
               min = c[l]; 
        }
        vector<CRef> & list = data.list(min);
        for (unsigned i = 0; i < list.size()
	  && ( data.unlimited() || (doStatistics && subsumeSteps < subLimit) )
	  ; ++i)
        {
	  
            if (list[i] == cr) {
                continue;
	        } 
	        if ( doStatistics ) ++ subsumeSteps;
	        if (ca[list[i]].size() < c.size()) {
		  continue;
	        } 
	        if (ca[list[i]].can_be_deleted()) { // do not use this clause, but remove it from the list!
		  list[i] = list.back(); list.pop_back(); --i;
		  continue; 
	        } else if (c.ordered_subsumes(ca[list[i]])) {
                
                if (doStatistics)
                {
                    ++subsumedClauses;
                    subsumedLiterals += ca[list[i]].size();
                }
                ca[list[i]].set_delete(true);
		data.addCommentToProof("remove by subsumption");
		data.addToProof(ca[list[i]],true); // remove this clause from the proof!
		data.removedClause(list[i]);
		        didChange(); 
		if ( config.opt_sub_debug > 1 ) cerr << "c subsumption removed " << (ca[list[i]].learnt() ? "learned" : "" ) << " clause " << ca[list[i]] << " by "  <<  (ca[list[i]].learnt() ? "learned" : "" ) << c << endl;
                occ_updates.push_back(list[i]);
		if(  config.opt_sub_debug > 1  ) cerr << "c clause " << ca[list[i]] << " is deleted by " << c << endl;
                if (!ca[list[i]].learnt() && c.learnt())
                {
		    if ( config.opt_sub_debug > 1 ) cerr << "c subsumption turned clause " << c << " from learned in original " << endl;
                    c.set_learnt(false);
                }
            }
        }
        //set can_subsume to false
        c.set_subsume(false);
    }  
    if (doStatistics)
    {
        processTime = cpuTime() - processTime;   
    } 
    // Update Stats and remove Clause from all Occurrence-Lists
    for (int i = 0; i < occ_updates.size(); ++i)
    {
        CRef cr = occ_updates[i];
        Clause & c = ca[cr];
        data.removedClause(cr, heap, ignore);
	assert( c.can_be_deleted() && "clauses that are removed have to have the right flag set!" );
	if( false ) { // be lazy!
         for (int l = 0; l < c.size(); ++l)
             data.removeClauseFrom(cr,c[l]);
	}
    }
    occ_updates.clear();
}

/**
 * Threadsafe copy of subsumption_worker:
 * Fixes the following race conditions:
 *  - Two equivalent clauses (duplicates) could subsume mutual, 
 *    if subsumption is performed on them in parallel.
 *    Therefore the clause with the smaller CRef will be kept.
 *
 *  - Let A, B be learnt clauses, C non-learnt clause.
 *    If A subsumes B, and in parallel B subsumes C, 
 *      A stays learnt clause since B is learnt, 
 *      B becomes deleted by A, but non-learnt by C
 *      C becomes deleted by B. 
 *    Since C is deleted, A will ommit the subsumption-check. 
 *    Afterwards just A as learnt clause will be kept, and the
 *    non-learnt information of C got lost. 
 *
 *    To solve this problem, the deletion and learnt flags are 
 *    not updated in time, but Clauses are remembered in two vectors.
 *    
 *    Now A will check C for subsumption, and inherit the non-learnt flag.
 *
 * @param start          start index of work-queue 
 * @param stop           stop index (+1) of work-queue, i.e. this index is not included
 * @param to_delete      this clauses, if not deleted, need to be set deleted afterwards
 * @param set_non_learnt this clauses, if not deleted, need to be set non-learnt afterwards 
 * @param stats          local stats
 */
void Subsumption :: par_subsumption_worker ( unsigned int & next_start, unsigned int global_end, SpinLock & balancerLock, vector<CRef> & to_delete, vector< CRef > & set_non_learnt, struct SubsumeStatsData & stats, const bool doStatistics)
{
    unsigned start = 0, end = 0;
    if (doStatistics)
    {
        stats.processTime = wallClockTime() - stats.processTime;   
    }
    while (global_end > next_start &&  !data.isInterupted() 
            && ( data.unlimited() || (doStatistics && subsumeSteps + stats.subsumeSteps < subLimit) ))
    {
        balancerLock.lock();
        if (global_end > next_start)
        {
            start = next_start;
            next_start+= chunk_size;
            end   = next_start > global_end ? global_end : next_start;
        }
        balancerLock.unlock();
        while (end > start && !data.isInterupted()
            && ( data.unlimited() || (doStatistics && subsumeSteps + stats.subsumeSteps < subLimit) ))
        {
            --end;
            const CRef cr = data.getSubsumeClauses()[end];
            Clause &c = ca[cr];
            if (doStatistics) ++stats.subsumeSteps;
            if (c.can_be_deleted())
                continue;
            bool learnt_subsumed_non_learnt = false;
            //find Lit with least occurrences
            Lit min = c[0];
            for (int l = 1; l < c.size(); l++)
            {
                if (data[c[l]] < data[min])
                   min = c[l]; 
            }
            vector<CRef> & list = data.list(min);
            for (unsigned i = 0; i < list.size(); ++i)
            {
          
                if (list[i] == cr) {
                    continue;
                } else if (ca[list[i]].size() < c.size()) {
                    continue;
                } else if (ca[list[i]].can_be_deleted()) {
                    continue;
                } else if (c.ordered_subsumes(ca[list[i]])) {
                    // save at least one duplicate, by deleting the clause with smaller CRef
                    if (c.size() == ca[list[i]].size() && cr > list[i])
                    {
                modifiedFormula = true;
                        // save the non-learnt information
                        if (!c.learnt() && ca[list[i]].learnt())
                        {
                            to_delete.push_back(cr);
                            set_non_learnt.push_back(list[i]);
                        } 
                        else
                        { 
                            if (config.opt_sub_par_subs_counts == 0)
                            {
                                bool removed = data.removeClauseThreadSafe(cr);
                                if (doStatistics && removed)
                                {
                                    ++stats.subsumedClauses;
                                    stats.subsumedLiterals += c.size();
                                }
                            }
                            else 
                            {
                                to_delete.push_back(cr);
                            }
                        }
                        continue;
                    }
                    // save the non-learnt information
                    if (c.learnt() && !ca[list[i]].learnt())
                    {
                        learnt_subsumed_non_learnt = true;
                        to_delete.push_back(list[i]);
                        continue;
                    }
                    if (config.opt_sub_par_subs_counts == 0)
                    {
                        bool removed = data.removeClauseThreadSafe(list[i]);
                        if (doStatistics && removed)
                        {
                            ++stats.subsumedClauses;
                            stats.subsumedLiterals += ca[list[i]].size();
                        }  
                    }
                    else
                    {
                        to_delete.push_back(list[i]);
                    }
                } //else if (doStatistics)       
                  //      ++stats.subsumeSteps;
            }
            //set can_subsume to false
            c.set_subsume(false);
            
            // add Clause to non-learnt-queue
            if (learnt_subsumed_non_learnt)
                set_non_learnt.push_back(cr);
        }
    }
    if (doStatistics) 
        stats.processTime = wallClockTime() - stats.processTime;
}


/**
 * locking based strengthening, based on naive subsumption check with negated literal
 * 
 * @param var_lock vector of locks for each variable
 *
 */
void Subsumption::par_strengthening_worker( unsigned int & next_start, unsigned int global_stop, SpinLock & balancerLock, vector< SpinLock > & var_lock, struct SubsumeStatsData & stats, vector< OccUpdate > & occ_updates, Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics) 
{
    unsigned int start = 0, stop = 0;
    assert(start <= stop && stop <= data.getStrengthClauses().size() && "invalid indices");
    assert(data.nVars() <= var_lock.size() && "var_lock vector to small");
    double & lock_time = stats.lockTime;
    if (doStatistics) stats.strengthTime = wallClockTime() - stats.strengthTime;
    
    deque<CRef> localQueue; // keep track of all clauses that have been added back to the strengthening queue because they have been strengthened
    SpinLock & data_lock = var_lock[data.nVars()];
    
    while (global_stop > next_start && data.ok() && !data.isInterupted())
    { 
        balancerLock.lock();
        if (global_stop > next_start)
        {
            start = next_start;
            next_start+= chunk_size;
            stop   = next_start > global_stop ? global_stop : next_start;
        }
        balancerLock.unlock();

        while (stop > start && data.ok() && !data.isInterupted())
        {    
            CRef cr = CRef_Undef;
            if( localQueue.size() == 0 ) {
                --stop;
                cr = data.getStrengthClauses()[stop];
            } else {
                // TODO: have a counter for this situation!
                cr = localQueue.back();
                localQueue.pop_back();
            }
     
            Clause & c = ca[cr];//data.getStrengthClauses()[stop]];
            lock_strengthener:
            if (c.can_be_deleted() || c.size() == 0)
                continue;
            if( !config.opt_sub_strength ) { // if not enabled, only remove clauses from queue and reset their flag!
                c.set_strengthen(false);
                continue;
            }
            Var fst = var(c[0]);
            
            // lock 1st var
            if (config.opt_sub_lock_stats) lock_time = cpuTime() - lock_time;
            var_lock[fst].lock();
            if (config.opt_sub_lock_stats) lock_time = cpuTime() - lock_time;

            // assure that clause can still strengthen
            if (c.can_be_deleted() || c.size() == 0)
            {
                var_lock[fst].unlock();
                continue;
            }
            
            // assure that first var still valid
            if (var(c[0]) != fst)
            {
                var_lock[fst].unlock();
                goto lock_strengthener;
            }
            
            // search lit with minimal occurrences
            Lit min = c[0];
            for (int j = 1; j < c.size(); ++j)
                if (data[min] * (c.size() - 1) + data[~min] > data[c[j]] * (c.size() -1) + data[~c[j]])
                    min = c[j];


            for (int l = 0; l < c.size(); ++l)
            {
                Lit neg = ~(c[l]);
                c[l] = neg;
                //use minimal list, or the negated list if  min == c[l] 
                vector< CRef> & list = (neg == ~min) ? data.list(neg) : data.list(min);
                // vector< CRef> & list = data.list(neg);
                for (int l_cr = 0; l_cr < list.size(); ++l_cr)
                {
                    if (list[l_cr] == cr)
                        continue;
                    assert(list[l_cr] != cr && "expect no tautologies here");
                    Clause & d = ca[list[l_cr]];
                    lock_to_strengthen:
                    if (d.can_be_deleted() || d.size() == 0)
                        continue;
                    Var d_fst = var(d[0]);

                    // if the d_fst > fst, d cannot contain fst, and therefore c cannot strengthen d
                    if (d_fst > fst)
                        continue;

                    // check if d_fst already locked by this thread, if not: lock
                    if (d_fst != fst)
                    {
                       if (config.opt_sub_lock_stats) lock_time = cpuTime() - lock_time;
                       var_lock[d_fst].lock();
                       if (config.opt_sub_lock_stats) lock_time = cpuTime() - lock_time;

                       // check if d has been deleted, while waiting for lock
                       if (d.can_be_deleted() || d.size() == 0)
                       {
                           var_lock[d_fst].unlock();
                           continue;
                       }

                       // check if d's first lit has changed, while waiting for lock
                       if (var(d[0]) != d_fst)
                       {
                           var_lock[d_fst].unlock();
                           goto lock_to_strengthen;
                       }
                    }
                    
                    // now d_fst is locked and for sure first variable
                    // do subsumption check
                    if (doStatistics) ++stats.strengthSteps;
                    
                    int l1 = 0, l2 = 0, pos = -1;
                    while (l1 < c.size() && l2 < d.size())
                    {
                       if (c[l1] == d[l2])
                       {
                            if (c[l1] == neg)
                                pos = l2;
                            ++l1;
                            ++l2;
                       }
                       // d does not contain c[l1]
                       else if (c[l1] < d[l2])
                            break;
                       else
                            ++l2;
                    }
                    
                    // if subsumption successful, strengthen
                    if (l1 == c.size())
                    {
                        assert(pos != -1 && "Position invalid"); //TODO -> if this happens, we found normel a subsumption case?, so why not deal with it? this is no error
                        if (doStatistics) ++stats.removedLiterals;
                modifiedFormula = true;
                        // unit found
                        if (d.size() == 2)
                        {
                            d.set_delete(true);
                            //data.lock();
                            if (config.opt_sub_lock_stats) lock_time = cpuTime() - lock_time; 
                            data_lock.lock();
                            if (config.opt_sub_lock_stats) lock_time = cpuTime() - lock_time; 
			     const Lit& unitLit = d[(pos + 1) % 2];
			     data.addCommentToProof("found during strengthening");data.addUnitToProof(unitLit); // add the unit
                            lbool state = data.enqueue(unitLit);
                            data_lock.unlock();  
                            data.removedClause(list[l_cr],heap, config.heap_updates == 2,ignore, &data_lock);
                            if (l_False == state)
                            {
                                var_lock[d_fst].unlock();
                                var_lock[fst].unlock();
                                if (doStatistics) stats.strengthTime = wallClockTime() - stats.strengthTime;
                                return;
                            }
                        }
                        else if (d.size() == 1)
                        {
                            assert(false && "no unit clauses should be strengthened");
                            // empty -> fail
                        }
                        //O if the first lit was strengthend, overwrite it in the end, since the lock would not be efficient any more
                        else
                        {
                            // keep track of this clause for further strengthening!
                            if( !d.can_strengthen() ) {
                                localQueue.push_back( list[l_cr] );
                                d.set_strengthen(true);
                              }
                            
                            occ_updates.push_back(OccUpdate(list[l_cr] , d[pos]));
                            d.removePositionSortedThreadSafe(pos);
                            // TODO to much overhead? 
                            if (config.opt_sub_lock_stats) lock_time = cpuTime() - lock_time; 
                            data_lock.lock();
                            if (config.opt_sub_lock_stats) lock_time = cpuTime() - lock_time; 
                            data.removedLiteral(neg, 1, heap, ignore);
                            if ( ! d.can_subsume()) 
                            {
                                d.set_subsume(true);
                                data.getSubsumeClauses().push_back(list[l_cr]);
                            }
                            data_lock.unlock();
                        }
                    }
                    
                    // if a new lock was acquired, free it
                    if (d_fst != fst)
                    {
                        var_lock[d_fst].unlock();
                    }
                   
                }
                c[l] = ~neg;
            }
            c.set_strengthen(false);
            // free lock of first variable
            var_lock[fst].unlock();
            
        }
    }
    if (doStatistics) stats.strengthTime = wallClockTime() - stats.strengthTime;
}

/** lock-based parallel non-naive strengthening-methode
 * @param data object
 * @param start where to start strengthening in strengtheningqueue
 * @param end where to stop strengthening
 * @param var_lock vector of locks for each variable
 */
void Subsumption::par_nn_strengthening_worker( unsigned int & next_start, unsigned int global_end, SpinLock & balancerLock, vector< SpinLock > & var_lock, struct SubsumeStatsData & stats, vector<OccUpdate> & occ_updates, Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics)
{ 
  unsigned int start = 0, end = 0;
  assert(start <= end && end <= data.getStrengthClauses().size() && "invalid indices");
  assert(data.nVars() <= var_lock.size() && "var_lock vector to small");
  if (doStatistics)
    stats.strengthTime = wallClockTime() - stats.strengthTime;
 
   deque<CRef> localQueue; // keep track of all clauses that have been added back to the strengthening queue because they have been strengthened
  SpinLock & data_lock = var_lock[data.nVars()];

  while (global_end > next_start && !data.isInterupted() 
          && (data.unlimited() || (doStatistics && strengthSteps + stats.strengthSteps < strLimit )))
  { 
      balancerLock.lock();
      if (global_end > next_start)
      {
          start = next_start;
          next_start+= chunk_size;
          end   = next_start > global_end ? global_end : next_start;
      }
      balancerLock.unlock();
      while (end > start && !data.isInterupted()
          && (data.unlimited() || (doStatistics && strengthSteps + stats.strengthSteps < strLimit )))
      {
        if (!data.ok()) 
        {
            stats.strengthTime = wallClockTime() - stats.strengthTime;
            return;
        }
        CRef cr = CRef_Undef;
        if( localQueue.size() == 0 ) {
          --end;
          cr = data.getStrengthClauses()[end];
        } else {
          // TODO: have a counter for this situation!
          cr = localQueue.back();
          localQueue.pop_back();
        }
        Clause& strengthener = ca[cr];
     
        lock_strengthener_nn:
        if (strengthener.can_be_deleted() || !strengthener.can_strengthen() 
                /*strengthener.size() == 0*/)
            continue;
        if( !config.opt_sub_strength ) { // if not enabled, only remove clauses from queue and reset their flag!
            strengthener.set_strengthen(false);
            continue;
        }

        Var fst = var(strengthener[0]);
        // lock 1st var
        var_lock[fst].lock();
        
        // assure that clause can still strengthen
        if (strengthener.can_be_deleted() || strengthener.size() == 0)
        {
            var_lock[fst].unlock();
            continue;
        }
        
        // assure that first var still valid
        if (var(strengthener[0]) != fst)
        {
            var_lock[fst].unlock();
            goto lock_strengthener_nn;
        }
     
        if( strengthener.size() < 2 ) {
            if( strengthener.size() == 1 ) 
            {
                data_lock.lock();
		data.addCommentToProof("found during strengthening");data.addUnitToProof(strengthener[0]); // add the unit
                lbool status = data.enqueue(strengthener[0]); 
                data_lock.unlock();

                var_lock[fst].unlock(); // unlock fst var

                if( l_False == status ) 
                {
                    if (doStatistics) stats.strengthTime = wallClockTime() - stats.strengthTime;
                    return;
                }
                else continue;
            }
            else 
            { 
                data.setFailed();  // can be done asynchronously
                var_lock[fst].unlock(); 
                if (doStatistics) stats.strengthTime = wallClockTime() - stats.strengthTime;
                return;
            }
        }    
        //find Lit with least occurrences and its occurrences
        // search lit with minimal occurrences
        assert (strengthener.size() > 1 && "expect strengthener to be > 1");
        Lit min = lit_Undef, nmin = lit_Undef;
        Lit /*min0 = strengthener[0], min1 = strengthener[1],*/ minT = strengthener[0];
        for (int j = 1; j < strengthener.size(); ++j)
        {
          if (data[var(minT)] > data[var(strengthener[j])])
              minT = strengthener[j];
        }
        {
            min = minT;
            nmin = ~minT;
        } 
        assert(min != nmin && "min and nmin should be different");
        vector<CRef>& list = data.list(min);        // occurrences of minlit from strengthener
        vector<CRef>& list_neg = data.list(nmin);   // occurrences of negated minlit from strengthener
        
        if (l_False == par_nn_strength_check(data, list, localQueue,  strengthener, cr, fst, var_lock, stats, occ_updates, heap, ignore, doStatistics))
        {
            var_lock[fst].unlock();
            if (doStatistics) stats.strengthTime = wallClockTime() - stats.strengthTime;
            return;
        }
        // if we use ~min, then some optimization can be done, since neg_lit has to be ~min
        if (l_False == par_nn_negated_strength_check(data, list_neg, localQueue, strengthener, cr, min, fst, var_lock, stats, occ_updates, heap, ignore, doStatistics))
        {
            var_lock[fst].unlock();
            if (doStatistics) stats.strengthTime = wallClockTime() - stats.strengthTime;
            return;
        }

        strengthener.set_strengthen(false);

        // free lock of first variable
        var_lock[fst].unlock();
      }
  }
  if (doStatistics) stats.strengthTime = wallClockTime() - stats.strengthTime;
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
inline lbool Subsumption::par_nn_strength_check(CoprocessorData & data, vector < CRef > & list, deque<CRef> & localQueue, Clause & strengthener, CRef cr, Var fst, vector < SpinLock > & var_lock, struct SubsumeStatsData & stats, vector< OccUpdate> & occ_updates, Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics) 
{
    int si, so;           // indices used for "can be strengthened"-testing
    int negated_lit_pos;  // index of negative lit, if we find one
 
    SpinLock & data_lock = var_lock[data.nVars()];
    
    // test every clause, where the minimum is, if it can be strenghtened
    for (unsigned int j = 0; j < list.size() && !data.isInterupted()
      && (data.unlimited() || (doStatistics && strengthSteps + stats.strengthSteps < strLimit ) );
      ++j )
    {
      Clause& other = ca[list[j]];
      if (doStatistics) ++stats.strengthSteps;
      
      lock_to_strengthen_nn:
      if (other.can_be_deleted() || list[j] == cr || other.size() == 0)
        continue;
      Var other_fst = var(other[0]);

      // if the other_fst > fst, other cannot contain fst, and therefore strengthener cannot strengthen other
      if (other_fst > fst)
          continue;

      // check if other_fst already locked by this thread, if not: lock
      if (other_fst != fst)
      {
         var_lock[other_fst].lock();

         // check if other has been deleted, while waiting for lock
         if (other.can_be_deleted() || other.size() == 0)
         {
             var_lock[other_fst].unlock();
             continue;
         }

         // check if others first lit has changed, while waiting for lock
         if (var(other[0]) != other_fst)
         {
             var_lock[other_fst].unlock();
             goto lock_to_strengthen_nn;
         }
      }
      
      // now other_fst is locked and for sure first variable
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

      // if subsumption successful, strengthen
      if (negated_lit_pos != -1 && si == strengthener.size())
      {
          
          if (doStatistics) ++stats.removedLiterals;
          // unit found
          if (other.size() == 2)
          {
              other.set_delete(true);
              data_lock.lock();
	      const Lit& unitLit = other[(negated_lit_pos + 1) % 2];
	      data.addCommentToProof("found during strengthening");data.addUnitToProof(unitLit); // add the unit
              lbool state = data.enqueue(unitLit);
              data_lock.unlock();
	          modifiedFormula = true;
              data.removedClause(list[j], heap, config.heap_updates == 2,ignore, &data_lock);
              if (l_False == state)
              {
                  var_lock[other_fst].unlock();
                  return l_False;
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
              if(  config.opt_sub_debug > 1  ) cerr << "c remove (@" << __LINE__ << ")" << negated_lit_pos << " from clause " << other << endl;
              // keep track of this clause for further strengthening!
              if( !other.can_strengthen() ) {
                localQueue.push_back( list[j] );
                other.set_strengthen(true);
              }
              Lit neg = other[negated_lit_pos];
	      
	      if( config.opt_sub_debug > 1 ) cerr << "c add remove info (@" << __LINE__ << ")  [" << occ_updates.size() << "] : " << list[j] << " with clause " << neg << " and ref " << list[j] << endl;
              occ_updates.push_back(OccUpdate(list[j] , neg));
              other.removePositionSortedThreadSafe(negated_lit_pos);
	          modifiedFormula = true;
              data.removedLiteral(neg, 1, heap, config.heap_updates == 2,ignore, &data_lock);
              if ( ! other.can_subsume()) 
              {
                  other.set_subsume(true);
                  data_lock.lock();
                  data.getSubsumeClauses().push_back(list[j]);
                  data_lock.unlock();
              }
          }
      }
      // if a new lock was acquired, free it
      if (other_fst != fst)
      {
          var_lock[other_fst].unlock();
      }
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
inline lbool Subsumption::par_nn_negated_strength_check(CoprocessorData & data, vector < CRef > & list, deque<CRef> & localQueue, Clause & strengthener, CRef cr, Lit min, Var fst, vector < SpinLock > & var_lock, struct SubsumeStatsData & stats, vector< OccUpdate> & occ_updates, Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics) 
{
    int si, so;           // indices used for "can be strengthened"-testing
    int negated_lit_pos;  // index of negative lit, if we find one
 
    SpinLock & data_lock = var_lock[data.nVars()];
    
    // test every clause, where the minimum is, if it can be strenghtened
    for (unsigned int j = 0; j < list.size() && !data.isInterupted()
      && (data.unlimited() || (doStatistics && strengthSteps + stats.strengthSteps < strLimit ) )
      ; ++j)
    {
      Clause& other = ca[list[j]];
      if (doStatistics) ++stats.strengthSteps;
      
      lock_to_strengthen_nn:
      if (other.can_be_deleted() || list[j] == cr || other.size() == 0)
        continue;
      Var other_fst = var(other[0]);

      // if the other_fst > fst, other cannot contain fst, and therefore strengthener cannot strengthen other
      if (other_fst > fst)
          continue;

      // check if other_fst already locked by this thread, if not: lock
      if (other_fst != fst)
      {
         var_lock[other_fst].lock();

         // check if other has been deleted, while waiting for lock
         if (other.can_be_deleted() || other.size() == 0)
         {
             var_lock[other_fst].unlock();
             continue;
         }

         // check if others first lit has changed, while waiting for lock
         if (var(other[0]) != other_fst)
         {
             var_lock[other_fst].unlock();
             goto lock_to_strengthen_nn;
         }
      }
      
      // now other_fst is locked and for sure first variable
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

      // if subsumption successful, strengthen
      if (negated_lit_pos != -1 && si == strengthener.size())
      {
          
          if (doStatistics) ++stats.removedLiterals;
          // unit found
          if (other.size() == 2)
          {
              other.set_delete(true);
              data_lock.lock();
	      const Lit& unitLit = other[(negated_lit_pos + 1) % 2];
	      data.addCommentToProof("found during strengthening");data.addUnitToProof(unitLit); // add the unit
              lbool state = data.enqueue( unitLit );
              data_lock.unlock();
	          modifiedFormula = true;
              data.removedClause(list[j],heap, config.heap_updates == 2,ignore, &data_lock);
              if (l_False == state)
              {
                 var_lock[other_fst].unlock();
                 return l_False;
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
              if(  config.opt_sub_debug > 1  ) cerr << "c remove (@" << __LINE__ << ")" << negated_lit_pos << " from clause " << other << endl;
              // keep track of this clause for further strengthening!
              if( !other.can_strengthen() ) {
                localQueue.push_back( list[j] );
                other.set_strengthen(true);
              }
              Lit neg = other[negated_lit_pos];
	      
	      if( config.opt_sub_debug > 1 ) cerr << "c add remove info (@" << __LINE__ << ")  [" << occ_updates.size() << "] : " << list[j] << " with clause " << neg << " and ref " << list[j] << endl;
              occ_updates.push_back(OccUpdate(list[j] , neg));
              other.removePositionSortedThreadSafe(negated_lit_pos);
	          modifiedFormula = true;
              data.removedLiteral(neg, 1, heap, config.heap_updates == 2,ignore, &data_lock);
              if ( ! other.can_subsume()) 
              {
                  other.set_subsume(true);
                  data_lock.lock();
                  data.getSubsumeClauses().push_back(list[j]);
                  data_lock.unlock();
              }
          }
      }
      // if a new lock was acquired, free it
      if (other_fst != fst)
      {
          var_lock[other_fst].unlock();
      }
    }
    return l_Undef;
}

bool Subsumption::hasToStrengthen() const
{
  return data.getStrengthClauses().size() > 0;
}

/** runs a fullstrengthening on data.getStrengthClauses(), needs occurrencelists (naive strengthening seems to be faster, TODO: strengthening on literals with minimal occurrences)
 * @param data occurrenceslists
 * @return 
 */
lbool Subsumption::fullStrengthening(Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics)
{
    /*
     * TODO strengthening with min occurances-lits
    for( int pos = 0 ; pos < 2; ++ pos )
    {
       //find lit with minimal occurrences
       vector<CRef>& list = pos == 0 ? data.list(min) :  data.list(~min);
    }
     */
  if( config.opt_sub_allStrengthRes > 0 || !config.opt_sub_naivStrength ) {
    return strengthening_worker( 0, data.getStrengthClauses().size(), heap, ignore);
  }
    if (doStatistics) strengthTime = cpuTime() - strengthTime;
    deque<CRef> localQueue; // keep track of all clauses that have been added back to the strengthening queue because they have been strengthened
    vector<OccUpdate> & occ_updates = strength_occ_updates; 
    //for every clause:
    for (int i = 0; i < data.getStrengthClauses().size() && !data.isInterupted();)
    {
        CRef cr = CRef_Undef;
        if( localQueue.size() == 0 ) {
            cr = data.getStrengthClauses()[i];
            ++i;
        } else {
            // TODO: have a counter for this situation!
            cr = localQueue.back();
            localQueue.pop_back();
        }
        Clause &c = ca[cr];
        if (c.can_be_deleted() || !c.can_strengthen())
            continue;   // dont check if it cant strengthen or can be deleted
        // for every literal in this clause:
        
	if( !config.opt_sub_strength ) { // if not enabled, only remove clauses from queue and reset their flag!
	  c.set_strengthen(false);
	  continue;
	}
        
        // search for lit with minimal occurrences;
        Lit min = c[0];
        for (int j = 1; j < c.size(); ++j)
            if (data[min] * (c.size() - 1) + data[~min] > data[c[j]] * (c.size() -1) + data[~c[j]])
                min = c[j];

        for (int j = 0; j < c.size()
	  && (data.unlimited() || (doStatistics && strengthSteps < strLimit ) )
	  ; ++j)
        {
            // negate this literal and check for subsumptions for every occurrence of its negation:
            Lit neg_lit = ~c[j];
            c[j] = neg_lit;     // temporarily change lit for subsumptiontest
            vector<CRef> & list = (neg_lit == ~min) ? data.list(neg_lit) : data.list(min);  // get occurrences of this lit
            //vector<CRef> & list = data.list(neg_lit);  // get occurrences of this lit
            for (unsigned int k = 0; k < list.size()
	      && (data.unlimited() || (doStatistics && strengthSteps < strLimit ) )
	      ; ++k)
            {
                if (list[k] == cr)
                    continue;
		
		if (doStatistics) ++strengthSteps;
		
                Clause & other = ca[list[k]];
                if (other.can_be_deleted()){     // dont check if this clause can be deleted, but remove it from its list
		    list[k] = list.back(); list.pop_back(); --k;
                    continue;
		}
                assert(other.size() > 1 && "Expect other to be > 1");
                
                
                // check for subsumption
                int l1 = 0, l2 = 0, pos = -1;
                while (l1 < c.size() && l2 < other.size())
                {
                   if (c[l1] == other[l2])
                   {
                        if (c[l1] == neg_lit)
                            pos = l2;
                        ++l1;
                        ++l2;
                   }
                   // other does not contain c[l1]
                   else if (c[l1] < other[l2])
                        break;
                   else
                        ++l2;
                }
                if (l1 == c.size() && pos != -1)    
                {
                    if (doStatistics) ++removedLiterals;
		    const Lit remLit = other[pos];
                    other.removePositionSorted(pos);     // strengthen clause
		    data.addCommentToProof("remove literal by strengthening");
		    data.addToProof(other);data.addToProof(other,true,remLit); // add information to proof!
		    other.updateExtraInformation( c.extraInformation() ); // update the extra information of this clause!
		    modifiedFormula = true;
		            if(  config.opt_sub_debug > 1  ) cerr << "c remove (@" << __LINE__ << ")" << neg_lit << " from clause " << other << endl;
                    //if(  config.opt_sub_debug > 1  ) cerr << "c used strengthener (lit negated) " << c << endl;
                    if(other.size() == 1)
                    {
                      // propagate if clause is unit
                      other.set_delete(true); 
                      data.enqueue(other[0],other.extraInformation()); // enqueue the literal with the extraInformation of the unit clause!
                    } 
                    else
                    {
                        // add clause since it got smaler and could subsume to subsumption_queue
                        if(!other.can_subsume())
                        {
                            // if the flag was set, this clause is allready in the subsumptionqueue, if not, we need to add this clause as it could subsume again
                            other.set_subsume(true);
                            data.getSubsumeClauses().push_back(list[k]);
                        }
                        // keep track of this clause for further strengthening!
                        if( !other.can_strengthen() ) {
	                        localQueue.push_back( list[k] );
	                        other.set_strengthen(true);
	                    }

                        // track occurrence update
                        if( config.opt_sub_debug > 1 ) cerr << "c add remove info (@" << __LINE__ << ")  [" << occ_updates.size() << "] : " << list[k] << " with clause " << neg_lit << " and ref " << list[k] << endl;
                        occ_updates.push_back(OccUpdate(list[k],neg_lit));
                        //list[k] = list[list.size() - 1];
                        //list.pop_back();    // shrink vector
                        
                        // k--; // since k++ in for-loop
                    }
                }
            }
            c[j] = ~neg_lit;    // change the negated lit back
        }
        if (data.hasToPropagate()) 
        {
            if (propagation.process(data, true) == l_False) {
	            data.setFailed();
              return l_False;
	        }
        }
        c.set_strengthen(false);
    }

  updateOccurrences( occ_updates, heap, ignore);
  occ_updates.clear();

  if (doStatistics) strengthTime = cpuTime() - strengthTime;
  // no result to tell to the outside
  return l_Undef;   
}

/**
 *creating resolvents in the createAllResolvents Version of Strengthening
 *
 */
lbool Subsumption::createResolvent( const CRef cr, CRef & resolvent, const int negated_lit_pos, Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics)
{
    Clause & origin = ca[cr];
    assert (origin.size() >= 2);
    assert (0 <= negated_lit_pos && negated_lit_pos < origin.size());
    assert (!origin.can_be_deleted());
    if (origin.size() == 2)
    {
	const Lit& unitLit = origin[(negated_lit_pos + 1) % 2];
	 data.addCommentToProof("found by strengthening"); data.addUnitToProof( unitLit ); 
        lbool state = data.enqueue( unitLit );
        if (l_False == state)
            return l_False;
        else
            return l_True;
    }
    else 
    {
      ps.clear();
      for (int i = 0; i < origin.size(); ++i)
      {
        if (i == negated_lit_pos)
          continue;
        ps.push(origin[i]);
      }
      if (doStatistics)
      { // count resolvents negatively
        removedLiterals -= origin.size() - 1;
      }
      resolvent = ca.alloc(ps, origin.learnt());
      data.addClause(resolvent, heap, ignore);
      if (ca[resolvent].learnt())
        data.getLEarnts().push(resolvent);
      else
        data.getClauses().push(resolvent);
      return l_Undef;
    }
}



/** the strengthening-methode, which runs through the strengtheningqueue from start to end and tries to strengthen with the clause from str-queue on the clauses from data
 * @param data vector of occurrences of clauses
 * @param start where to start strengthening in strengtheningqueue
 * @param end where to stop strengthening
 *
 * 
 */
lbool Subsumption::strengthening_worker( unsigned int start, unsigned int end, Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics)
{
  if (doStatistics)
      strengthTime = cpuTime() - strengthTime;
  int si, so;           // indices used for "can be strengthened"-testing
  int negated_lit_pos;  // index of negative lit, if we find one
  deque<CRef> localQueue; // keep track of all clauses that have been added back to the strengthening queue because they have been strengthened
  vector < OccUpdate > & occ_updates = strength_occ_updates;
  
  if( config.opt_sub_preferLearned && data.isInprocessing() ) {
      // move all learned clauses to the back! == original clauses to the front
      int k = 0;
      for (int i = 0 ; i < data.getSubsumeClauses().size(); ++ i ) {
	const CRef cr = data.getSubsumeClauses()[i];
	Clause &c = ca[cr];
	if( !c.learnt() ) {
	  CRef tmp = data.getSubsumeClauses()[i]; 
	  data.getSubsumeClauses()[i] = data.getSubsumeClauses()[k];
	  data.getSubsumeClauses()[k] = data.getSubsumeClauses()[tmp];
	  k++; // move clause to front, increase counter for original variables
	}
	// simply ignore learned clauses!
      }
  }
  
  for (; end > start && !data.isInterupted()
    && (data.unlimited() || (doStatistics && strengthSteps < strLimit ) )
    ;)
  {
    CRef cr = CRef_Undef;
    if( localQueue.size() == 0 ) {
      --end;
      cr = data.getStrengthClauses()[end];
    } else {
      // TODO: have a counter for this situation!
      cr = localQueue.back();
      localQueue.pop_back();
    }
    Clause& strengthener = ca[cr];
    if (strengthener.can_be_deleted() || !strengthener.can_strengthen())
      continue;
    
    if( !config.opt_sub_strength ) { // if not enabled, only remove clauses from queue and reset their flag!
      strengthener.set_strengthen(false);
      continue;
    }
    
    //find Lit with least occurrences and its occurrences
    // search lit with minimal occurrences

    if( strengthener.size() < 2 ) {
      if( strengthener.size() == 1 ) { 
	if( l_False == data.enqueue(strengthener[0]) ) break;
	else continue;
      }
      else { data.setFailed(); break; }
    }
    
    assert (strengthener.size() > 1 && "expect strengthener to be > 1");
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
    // test every clause, where the minimum is, if it can be strenghtened
    for (unsigned int j = 0; j < list.size()
      && !data.isInterupted()
      && (data.unlimited() || (doStatistics && strengthSteps < strLimit ) )
      ; ++j)
    {
      if ( list[j] == cr) continue; 
      Clause& other = ca[list[j]];
      if (doStatistics) ++strengthSteps;
      if ( other.size() == 0 ) { assert( !data.ok() && "unsat should be found already!" ); break; }  // here, data.ok should be false already -> nothing to be done!
      if( other.can_be_deleted() ) { // skip, but remove from list!
	if( config.opt_sub_debug > 1 ) cerr << "c overwrite for literal " << min << " : list[" << j << "]=" << list[j] << " with list[" << list.size() - 1 << "] = " << list.back() << endl;
	list[j] = list.back(); list.pop_back(); --j;
	continue;
      }
      
      Clause& strengthener = ca[cr]; // if config.opt_sub_allStrengthRes -> realloc possible
      
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
          break;    // the other clause had not the same lit and it was not negated, can't strengthen
        else
          ++so;
      }
      assert( !other.can_be_deleted() && "the clause that is tested should not be known to be redundant already!" );
      if (negated_lit_pos != -1 && si == strengthener.size()) // TODO if negated_lit_pos == -1 -> normal subsumption case, why not apply  it?
      {
        if (other.size() <= config.opt_sub_allStrengthRes) // check this only for relevant clauses
        {
          CRef newCRef;
          toDelete.push_back(list[j]);
          lbool status = createResolvent(list[j], newCRef, negated_lit_pos, heap, ignore, doStatistics);
          if (l_False == status)
            return l_False;
          if (l_Undef == status)
          {
            data.getSubsumeClauses().push_back(newCRef);
            newClauses.push_back(newCRef);
	    // only if clause is actually needed
	    data.addCommentToProof("created by strengthening (allStrengthRes)");
	    data.addToProof( ca[newCRef] ); // add clause to proof!
	    ca[newCRef].setExtraInformation( strengthener.extraInformation() ); ca[newCRef].updateExtraInformation(other.extraInformation()); // setup extra information
	    if ( config.opt_sub_debug > 1 ) cerr << "c created resolvent while strengthening: " << ca[newCRef] << endl;
	    if ( config.opt_sub_debug > 1 ) cerr  << "c origin: " << strengthener << " and " << other << endl;
          }

        }
        else
        {
          if (doStatistics) ++ removedLiterals;
          // if neglit found and we went through all lits of strengthener, then the other clause can be strengthened
          if(!other.can_subsume())
          {
            // if the flag was set, this clause is allready in the subsumptionqueue, if not, we need to add this clause as it could subsume again
            other.set_subsume(true);
            data.getSubsumeClauses().push_back(list[j]);
          }
          // keep track of this clause for further strengthening!
          if( !other.can_strengthen() ) {
            localQueue.push_back( list[j] );
            other.set_strengthen(true);
          }
          didChange();
	  if( config.opt_sub_debug > 1 ) cerr << "c add remove info (@" << __LINE__ << ")  [" << occ_updates.size() << "] : " << list[j] << " with clause " << other[negated_lit_pos] << " and ref " << list[j] << endl;
          occ_updates.push_back(OccUpdate(list[j] , other[negated_lit_pos]));
          if( config.opt_sub_debug > 1 ) cerr << "c remove (@" << __LINE__ << ")" << other[negated_lit_pos] << " from clause " << other << " with " << strengthener << endl;
	  const Lit remLit = other[negated_lit_pos];
          other.removePositionSorted(negated_lit_pos);
	  data.addCommentToProof("removed literal by strengthening (worker)");
	  data.addToProof(other);data.addToProof(other,true,remLit); // add clause to proof
	  other.updateExtraInformation( strengthener.extraInformation() ); // update extra info
          if(other.size() == 1)
          {
            // propagate if clause is only 1 lit big
            assert(var(other[0]) < data.nVars() && "Literal does not exist");
            data.enqueue(other[0]);
            other.set_delete(true);
            //propagation.propagate(data, true);
          }
        }
      }
    }
    //propagation only in a valid state 
    if (data.hasToPropagate()) 
    {
	 if( config.opt_sub_debug > 1 ) cerr << "c call propagate @ " << __LINE__ << endl;
	 if( data.outputsProof() ) { updateOccurrences(occ_updates, heap, ignore); }
        if (propagation.process(data, true, heap, ignore) == l_False)
            return l_False;
    }
    // now test for the occurrences of negated min, now the literal, that appears negated has to be min
    for (unsigned int j = 0; j < list_neg.size()
      && !data.isInterupted()
      && (data.unlimited() || (doStatistics && strengthSteps < strLimit ) )
      ; ++j)
    {
      Clause& other = ca[list_neg[j]];
      if (doStatistics) ++ strengthSteps;
      if (other.can_be_deleted()) {
	if( config.opt_sub_debug > 1 ) cerr << "c overwrite for literal " << nmin << " : list_neg[" << j << "]=" << list_neg[j] << " with list_neg[" << list_neg.size() - 1 << "] = " << list_neg.back() << endl;
	list_neg[j] = list_neg.back(); list_neg.pop_back(); --j;
        continue;
      }
      
      Clause& strengthener = ca[cr]; // if config.opt_sub_allStrengthRes -> realloc possible
      si = 0;
      so = 0;
      negated_lit_pos = -1;
      while (si < strengthener.size() && so < other.size())
      {
        if(strengthener[si] == other[so])
        {
          ++si;
          ++so;
        } 
        else if (~min == other[so])
        {
            negated_lit_pos = so;
            ++si; 
            ++so; 
        }
        else if (strengthener[si] < other[so])
          break;
        else
          ++so;
      }
      if (si == strengthener.size() && negated_lit_pos != -1)
      {
        if (other.size() <= config.opt_sub_allStrengthRes)
        {
          CRef newCRef;
          toDelete.push_back(list_neg[j]);
          lbool status = createResolvent(list_neg[j], newCRef, negated_lit_pos, heap, ignore, doStatistics);
          if (l_False == status)
            return l_False;
          if (l_Undef == status)
          {
            data.getSubsumeClauses().push_back(newCRef);
            newClauses.push_back(newCRef);
	    
	    data.addCommentToProof("created by strengthening (allStrengthRes)");
	    data.addToProof( ca[newCRef] ); // add clause to proof!
	    ca[newCRef].setExtraInformation( strengthener.extraInformation() ); ca[newCRef].updateExtraInformation(other.extraInformation()); // setup extra information
          }
          if ( config.opt_sub_debug > 1 ) cerr << "c created resolvent while strengthening: " << ca[newCRef] << endl;
          if ( config.opt_sub_debug > 1 ) cerr  << "c origin: " << strengthener << " and " << other << endl;
        }
        else
        {
          if (doStatistics) ++removedLiterals;
          // other can be strengthened
          if(!other.can_subsume())
          {
            // if the flag was set, this clause is allready in the subsumptionqueue, if not, we need to add this clause as it could subsume again
            other.set_subsume(true);
            data.getSubsumeClauses().push_back(list_neg[j]);
          }
             
          // keep track of this clause for further strengthening!
          if( !other.can_strengthen() ) {
	    localQueue.push_back( list_neg[j] );
	    other.set_strengthen(true);
	  }
          
          if( config.opt_sub_debug > 1 ){
	    cerr << "c add remove info (@" << __LINE__ << ")  [" << occ_updates.size() << "] : " << list_neg[j] << " with clause " << other[negated_lit_pos] << " and ref " << list_neg[j] << endl;
	    cerr << "c lit " << nmin << " list: " << data.list(nmin) << endl;
	  }
          occ_updates.push_back(OccUpdate(list_neg[j] , other[negated_lit_pos]));
          if(  config.opt_sub_debug > 1  ) cerr << "c remove (@" << __LINE__ << ")" << other[negated_lit_pos] << " from clause " << other << " with strengthener " << strengthener << " ( via index: " << list_neg[j] << " cls: " << ca[list_neg[j]] << ")" << endl;
          didChange();
	  const Lit remLit = other[negated_lit_pos];
          other.removePositionSorted(negated_lit_pos);
	  data.addCommentToProof("removed literal by strengthening");
	  data.addToProof(other);data.addToProof(other,true,remLit); // add to proof
	  other.updateExtraInformation( strengthener.extraInformation() ); // update extra info
          
          if(other.size() == 1)
          {
            // propagate if clause is only 1 lit big
            assert(var(other[0]) < data.nVars() && "Literal does not exist");
            data.enqueue(other[0]);
            other.set_delete(true);
            //propagation.propagate(data, true);
          }
        }
      }
    }
    if (data.hasToPropagate()) 
    {
	if( config.opt_sub_debug > 1 ) cerr << "c call propagate!" << endl;
        if( data.outputsProof() ) { updateOccurrences(occ_updates, heap, ignore); }
        if (propagation.process(data, true, heap, ignore) == l_False)
            return l_False;
	    modifiedFormula = modifiedFormula || propagation.appliedSomething();
    }
    ca[cr].set_strengthen(false);
  }

  updateOccurrences( occ_updates, heap, ignore);
  occ_updates.clear();
  if (doStatistics) strengthTime = cpuTime() - strengthTime;
  
  return data.ok() ? l_Undef : l_False;
}

inline void Subsumption::updateOccurrences(vector< OccUpdate > & updates, Heap<VarOrderBVEHeapLt> * heap, const Var ignore)
{
    for (int i = 0; i < updates.size(); ++i)
    {
        if( config.opt_sub_debug > 1 ) cerr << "c list for literal " << updates[i].l << " : " << data.list(updates[i].l) << endl;
        // just remove once from stats -> this is consistent with propagation, since propagation will clear occ-lists 
        // and sets occ-stats by itself
        if (data.removeClauseFrom(updates[i].cr, updates[i].l)) {
	  if( config.opt_sub_debug > 1 ) cerr << "c successfully removed clause [" << i << "/" << updates.size() <<  "] from list for literal " << updates[i].l << " from clause " << ca[updates[i].cr] << " [" << updates[i].cr << "]" << endl;
            data.removedLiteral(updates[i].l, 1, heap, ignore);
	} else if( config.opt_sub_debug > 1 ) cerr << "c DID NOT remove clause [" << i << "/" << updates.size() <<  "] from list for literal " << updates[i].l << " from clause " << ca[updates[i].cr] << " [" << updates[i].cr << "]" << endl;
    }
    updates.clear();
}

void Subsumption::initClause( const Minisat::CRef cr, bool addToStrengthen )
{
  const Clause& c = ca[cr];
  if( !c.can_be_deleted() ) {
    if (c.can_subsume() )
      data.getSubsumeClauses().push_back(cr);
    if (addToStrengthen && c.can_strengthen()) // only if the clause should be added to the strengthening queue
      data.getStrengthClauses().push_back(cr);
  }
}


void Subsumption::parallelSubsumption( const bool doStatistics)
{
  if (doStatistics) processTime = wallClockTime() - processTime;
  if( false ) cerr << "c parallel subsumption with " << controller.size() << " threads" << endl;
  printDRUPwarning(cerr,"parallel subsumption");
  SubsumeWorkData workData[ controller.size() ];
  vector<Job> jobs( controller.size() );
  toDeletes.resize(controller.size());
  nonLearnts.resize(controller.size());
  localStats.resize(controller.size());
  unsigned int queueSize = data.getSubsumeClauses().size();
  unsigned int next_start = 0;

  // Setting Chunk Size
  chunk_size = queueSize > config.opt_sub_chunk_size * controller.size() * 1.8 ? config.opt_sub_chunk_size : (queueSize / controller.size());
  if (chunk_size <= 0) chunk_size = 1;

  // setup data for workers
  for( int i = 0 ; i < controller.size(); ++ i ) {
    workData[i].subsumption = this; 
    workData[i].data  = &data;
    workData[i].start = & next_start;
    workData[i].end   = queueSize;
    workData[i].balancerLock = & balancerLock;
    workData[i].to_delete = & toDeletes[i];
    workData[i].set_non_learnt = & nonLearnts[i];
    workData[i].stats = & localStats[i];
    jobs[i].function  = Subsumption::runParallelSubsume;
    jobs[i].argument  = &(workData[i]);
  }
  controller.runJobs( jobs );

  // Setting delete information
  for (int i = 0 ; i < toDeletes.size(); ++ i) 
  {
    for (int j = 0; j < toDeletes[i].size(); ++j)
    {
        Clause & c = ca[toDeletes[i][j]]; 
        if (!c.can_be_deleted())
        {
            c.set_delete(true);
            data.removedClause(toDeletes[i][j]);
            if (doStatistics)
            {
                ++localStats[i].subsumedClauses;
                localStats[i].subsumedLiterals += c.size();
            }
        }
    }
    toDeletes[i].clear();
  } 
  // Setting non-learnt information
  for (int i = 0; i < nonLearnts.size(); ++i)
  {
    for (int j = 0; j < nonLearnts[i].size(); ++j)
    {
        Clause & c = ca[nonLearnts[i][j]];
        if (!c.can_be_deleted() && c.learnt())
            c.set_learnt(false);
    }
    nonLearnts[i].clear();
  }
  if (doStatistics) processTime = wallClockTime() - processTime;
}

void* Subsumption::runParallelSubsume(void* arg)
{
  SubsumeWorkData* workData = (SubsumeWorkData*) arg;
  workData->subsumption->par_subsumption_worker(*(workData->start),workData->end, *(workData->balancerLock), *(workData->to_delete), *(workData->set_non_learnt), *(workData->stats));
  return 0;
}

void Subsumption::parallelStrengthening(Heap<VarOrderBVEHeapLt> * heap, const Var ignore, const bool doStatistics)
{
  // assert( !data.isInterupted() && "if interrupted, do not hit this point!" );
  //fullStrengthening(data);
  if( false ) cerr << "c parallel strengthening with " << controller.size() << " threads" << endl;
  printDRUPwarning(cerr,"parallel strengthening"); // parallel strenghtening cannot produce DRUP proofs!
  if (doStatistics) strengthTime = wallClockTime() - strengthTime;
  SubsumeWorkData workData[ controller.size() ];
  //vector< struct SubsumeStatsData > localStats (controller.size());
  vector<Job> jobs( controller.size() );
  var_locks.resize(data.nVars() + 1); // 1 extra SpinLock for data
  occ_updates.resize(controller.size());
  unsigned int queueSize = data.getStrengthClauses().size();
  unsigned int next_start = 0;

  // Setting Chunk Size
  chunk_size = queueSize > config.opt_sub_chunk_size * controller.size() * 1.8 ? config.opt_sub_chunk_size : (queueSize / controller.size());
  if (chunk_size <= 0) chunk_size = 1;

  for ( int i = 0 ; i < controller.size(); ++ i ) {
    workData[i].subsumption = this; 
    workData[i].start = & next_start;
    workData[i].end   = queueSize;
    workData[i].balancerLock = & balancerLock;
    //cerr << "c p s thread " << i << " running from " << *(workData[i].start) << " to " << workData[i].end << endl;
    workData[i].data  = &data; 
    workData[i].var_locks = & var_locks;
/*    localStats[i].removedLiterals = 0;
    localStats[i].strengthSteps = 0;
    localStats[i].strengthTime = 0;
    localStats[i].lockTime = 0;*/
    workData[i].stats = & localStats[i];
    workData[i].occ_updates = & occ_updates[i];
    workData[i].heap = heap;
    workData[i].ignore =  ignore;
    workData[i].config =  &config;
    jobs[i].function  = Subsumption::runParallelStrengthening;
    jobs[i].argument  = &(workData[i]);
  }
  controller.runJobs( jobs );

  // update Occurrences
  for (int i = 0; i < controller.size(); ++i)
  {
    updateOccurrences(occ_updates[i], heap, ignore);
    occ_updates[i].clear();
  }

  // we do not have the resources for the remaining clauses!
  for( int i = 0 ; i < data.getStrengthClauses().size(); ++ i ) ca[ data.getStrengthClauses()[i] ].set_strengthen(false);
  data.getStrengthClauses().clear(); 
  
  //propagate units
  propagation.process(data, true, heap, ignore);
  if (doStatistics) strengthTime = wallClockTime() - strengthTime;
}

void* Subsumption::runParallelStrengthening(void* arg)
{
    SubsumeWorkData* workData = (SubsumeWorkData*) arg;
    if ( workData->config->opt_sub_naivStrength ) workData->subsumption->par_strengthening_worker(*(workData->start),workData->end, *(workData->balancerLock), *(workData->var_locks), *(workData->stats), *(workData->occ_updates), workData->heap, workData->ignore);
    else workData->subsumption->par_nn_strengthening_worker(*(workData->start),workData->end, *(workData->balancerLock), *(workData->var_locks), *(workData->stats), *(workData->occ_updates), workData->heap, workData->ignore);
    return 0;
}

void Subsumption::destroy() {
    // Member var seq subsumption
  vector < CRef >().swap(subs_occ_updates);
  // Member var seq strength
  vector < OccUpdate >().swap(strength_occ_updates);
  // Member vars parallel Subsumption
  vector< vector < CRef > >().swap(toDeletes);
  vector< vector < CRef > >().swap(nonLearnts);
  //vector< struct SubsumeStatsData >().swap(localStats);
  
  // Member vars parallel Strengthening
  vector< SpinLock >().swap(var_locks); // 1 extra SpinLock for data
  vector< vector < OccUpdate > >().swap(occ_updates);
}
