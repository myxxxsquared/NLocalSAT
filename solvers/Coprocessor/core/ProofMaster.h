/*********************************************************************************[Communication.h]
Copyright (c) 2014, All rights reserved, Norbert Manthey

 **************************************************************************************************/

#ifndef PROOFMASTER_H
#define PROOFMASTER_H


#include "mtl/Vec.h"
#include "core/SolverTypes.h"
#include "utils/LockCollection.h"

#include "core/OnlineProofChecker.h"

#include <cstdio>
#include <iostream>

using namespace Minisat;
using namespace std;

/** class that takes care of constructing a DRUP proof for a portfolio solver
 *  (yet, only DRUP is supported, and each solver is assumed to not introduce new variables)
 */
class ProofMaster 
{
  SleepLock ownLock;	// lock for the proof file
  FILE* drupProofFile; // Output for DRUP unsat proof
  
  OnlineProofChecker* opc;	// check the proof on the fly during its creation
  
  int threads;		// number of used threads
  int HASHMAX;		// constant used for hashing
  bool useCounting;	// use the counting mechanism instead of producing a very large proof
  bool opt_verboseProof;	// print additional comments to the proof?
  
  const bool debugOutput;	// enable for bug hunting
  
  /** temporal storage for clauses for the proof for each thread until a clause is shared (one more for the proof master
   *  lit_Undef is used to separate clauses
   *  lit_Error is used to indicate deletion of clauses
   */
  vector< vector<Lit> > localClauses;	
  
  // for each clause, re-use the LBD as a counter how often that clause is theoretically present in the proof
  
  vector< vector<CRef> > hashTable; // for each hash have a list of clauses, the LBD of the clause is re-used as the counter for the number of occurrences
  ClauseAllocator ca;	// storage for clauses, all active clauses represent the clauses that are currently present in the proof
  
  MarkArray matchArray;	// array to match two clauses
  
  vec<Lit> tmpCls;	// helper vector to create unit clauses in allocator
  vec<Lit> opcTmpCls;	// to check clauses, a "real" clause is necessary for the online proof checker
  
public:

  /** set up a proof master class with a handle to a file, and a number of threads 
   * @param drupFile pointer to an already opened file for writing the proof to
   * @param nrOfThreads number of threads in the portfolio solver
   * @param nVars number of variables in the formula
   * @param counting use the build-in counting mechanism (smaller proof, more memory usage)
   * @param hashTableSize size of the hash table (higher value -> less collisions -> faster computatation, but more memory
   */
  ProofMaster( FILE* drupFile, const int nrOfThreads, const int nVars, bool counting, bool verboseProof, const int hashTableSize = 100000);
  
  /** add clauses to the proof (if not local, a lock is used before the global proof is updated)
   * Note: that added clause should not be an original clause from the CNF formula! this has to be ensured by the calling thread!
   * @param clause clause that should be added (can be vector or clause)
   * @param extraClauseLit additional literal of the clause that is written to the proof at the first position (and might be presend in the clause again)
   * @param ownerID id of the calling thread, for the clause sharing pool the ID has to match the thread number
   * @param local add the clauses only to the local storage, and do not submit them to the global proof (can be done later, when the next clauses are sent)
   */
  template <class T>
  void addToProof(   const T& clause, const Lit& extraClauseLit , int ownerID, bool local); 
  /** add a set of unit clauses to the proof */
  void addUnitsToProof( const vec<Lit>& units, int ownerID, bool local); 
  /** add a single unit clause to the proof */
  void addUnitToProof( const Lit& unit, int ownerID, bool local); 

  /** add the clause directly to the proof-data without writing to FILE, and without a check. Sets the number of occurrences to the given number 
   * Note: does not lock the global proof
   * @param clause the clause to be added
   * @param numberOfOccurrence number of times that clause is added
   * @param isNewClause is it known that these clauses are already present, if not, then this parameter can be set to true
   */
  template <class T>
  void addInputToProof(const T& clause, int ownerID, int numberOfOccurrence, bool isNewClause = true); 
  
  /** delete a clause from the proof (if not local, a lock is used before the global proof is updated)
   * @param clause clause that should be added (can be vector or clause)
   * @param ownerID id of the calling thread, for the clause sharing pool the ID has to match the thread number
   * @param local delete the clauses only from the local storage, and do not ubdate the global proof (can be done later, when the next clauses are sent)
   */
  template <class T>
  void delFromProof( const T& clause, const Lit& extraClauseLit, int ownerID, bool local); 
  /** delete a single unit clause from the proof */
  void delFromProof( const Lit& unit, int ownerID, bool local); 
  
  /** add all clauses from the local proof of a thread to the global proof 
   *  @param ownerID id of the calling thread
   *  @param useExtraLock lock the global pool before updating
   */
  void updateGlobalProof( int ownerID , bool useExtraLock = false);

  /** add a comment to the global proof (cannot be added to the local proof ... */
  void addCommentToProof( const char* text, int ownerID); // write the text as comment into the proof!
  
  
  /** set up the online proof checker for the parallel proof to continue the work that has been done so far already */
  void setOnlineProofChecker( OnlineProofChecker* setUpChecker );
  
private:
  
  template <class T>
  unsigned long long getHash (const T& clause, const Lit& extraClauseLit, int startIndex, int endIndex); // hash function for a single clause, extraLit might be present in clause again
  unsigned long long getHash (const Lit& unit); // hash function for a unit literal (speciallizes the above method)
  
  /** add a unit clause to the proof without locking (locking has been done by the caller) */
  void addUnitToGlobalProof( const Lit& unit, int ownerID );
  
  /** add a clause to the global proof
   * @param clause container of literals
   * @param extraClauseLit extra literal that is contained in the clause (if it is not lit_Undef)
   * @param start index where the clause to add starts
   * @param end index to element behind last literal of the clause
   */
  template <class T>
  void addGlobalClause( const T& clause, const Lit& extraClauseLit, int ownerID, int startIndex, int endIndex );
  
  /** add a clause to the global proof
   * @param clause container of literals
   * @param extraClauseLit extra literal that is contained in the clause (if it is not lit_Undef)
   * @param start index where the clause to add starts
   * @param end index to element behind last literal of the clause
   */
  template <class T>
  void removeGlobalClause( const T& clause, const Lit& extraClauseLit, int ownerID, int startIndex, int endIndex );
  
};

inline ProofMaster::ProofMaster(FILE* drupFile, const int nrOfThreads, const int nVars, bool counting, bool verboseProof, const int hashTableSize)
: drupProofFile( drupFile )
, opc (0)
, threads( nrOfThreads )
, HASHMAX( hashTableSize )
, useCounting( counting )
, opt_verboseProof(verboseProof)
, debugOutput(false) // enable for bug hunting
{
  localClauses.resize( nrOfThreads+1 ); // one for each thread, and the last one for the clause sharing pool
  matchArray.create( nVars * 2 ); // one for each literal
  if( useCounting ) hashTable.resize( HASHMAX );
}



inline void ProofMaster::updateGlobalProof(int ownerID, bool useExtraLock)
{
    if( ownerID == -1 ) ownerID = threads; // correct owner ID
    if( localClauses[ownerID].size() == 0 ) return;	// if there is nothing to do, return, and do not lock!
    // lock
    if( useExtraLock ) ownLock.lock();
    vector<Lit>& currentList = localClauses[ownerID];
    
    // iterate over the whole clause list
    int start = 0, end = 0;
    bool deleteClause = false;
    for( int i = 0 ; i < currentList.size(); ++ i ) {
      if( currentList[i] == lit_Undef ) // found the next clause
      {
	end = i;	// store pointer to the position behind last literal
	deleteClause = false;
	if( currentList[start] == lit_Error ) {deleteClause = true; start ++; } // check whether this clause should be deleted, update start pointer
	
	// add the clause to the global proof
	if( deleteClause ) removeGlobalClause( currentList, lit_Undef, ownerID, start, end );
	else addGlobalClause( currentList, lit_Undef, ownerID, start, end );
      }
      
    }
    currentList.clear(); 
    
    // unlock
    if( useExtraLock ) ownLock.unlock();
}


inline void ProofMaster::addUnitToGlobalProof(const Lit& unit, int ownerID)
{
    unsigned long long thisHash = getHash( unit );
    CRef hashClause = CRef_Undef;

    if( useCounting ) { // only if the counting feature is enabled
      const vector<CRef>& list = hashTable[ thisHash ];
      if( list.size() > 0 ) { // there are clauses that have to be matched
	matchArray.nextStep();
	for( int i = 0 ; i < list.size(); ++ i ) {
	  const Clause& c = ca[ list[i] ];
	  if( c.size() != 1 || c[0] != unit ) continue; // not the same clause, if the size check fails
	  hashClause = list[i]; break;	// store current reference, stop loop
	}
      }
    }
    // if not present, write clause to proof
    if( hashClause == CRef_Undef ) {
      
      if( opc != 0 ) {	// check proof 
	if( ! opc->addClause(unit) ) { cerr << "c adding unit clause " << unit << " to global proof fails" << endl; assert(false); exit(13); }
      }
      
      // write to file
      if( opt_verboseProof ) fprintf(drupProofFile, "c add clause by %i\n", ownerID);
      fprintf(drupProofFile, "%i 0\n", (var(unit) + 1) * (-2 * sign(unit) + 1));
      
      if( useCounting ) {
	// add to clause storage
	tmpCls.clear(); tmpCls.push(unit);
	CRef ref = ca.alloc( tmpCls , false ); // ok, unit is handled
	ca[ref].setLBD(1); // the clause is currently present once in the proof
	// add to hash table
	hashTable[thisHash].push_back( ref );
	if(opt_verboseProof) cerr << "c add clause " << ca[ref] << " to hash table " << " (hash(" << thisHash << "): " << getHash( unit ) << " ) list:" << hashTable[thisHash] << endl;
      }
    } else { // else increase the counter of that clause by 1
      if( useCounting ) { 
	ca[ hashClause ].setLBD(ca[ hashClause ].lbd() + 1); // re-use LBD
	if(opt_verboseProof)cerr << "c set counter of " << ca[ hashClause ] << " to " << ca[ hashClause ].lbd() << " (hash: " << getHash( unit ) << " ) list:" << hashTable[thisHash] << endl;
      }
    }
}


template <class T>
inline void ProofMaster::addGlobalClause(const T& clause, const Lit& extraClauseLit, int ownerID, int startIndex, int endIndex)
{
    CRef hashClause = CRef_Undef;
    unsigned long long thisHash = HASHMAX;
    
    if( useCounting ) { // check whether the clause already exists
      thisHash = getHash( clause, extraClauseLit, startIndex, endIndex ); // get hash for the current clause
      const vector<CRef>& list = hashTable[ thisHash ];
      if( list.size() > 0 ) { // there are clauses that have to be matched
	matchArray.nextStep();
	int clauseSize = 0 ;
	if( extraClauseLit != lit_Undef ) { clauseSize ++; matchArray.setCurrentStep( toInt ( extraClauseLit ) ); } // mark all literals of the current clause
	for( int i = startIndex ; i < endIndex; ++ i ) {
	  if( extraClauseLit != clause[i] ) {
	    clauseSize ++;
	    matchArray.setCurrentStep( toInt ( clause[i] ) ); // mark all literals of the current clause
	  }
	}
	for( int i = 0 ; i < list.size(); ++ i ) {
	  const Clause& c = ca[ list[i] ];
	  if( c.size() != clauseSize ) continue; // not the same clause, if the size check fails
	  int j = 0;
	  for( ; j < c.size(); ++ j ) { // try to find all literals of the current clause in the matchArray
	    if( ! matchArray.isCurrentStep( toInt(c[j] ) ) ) {
	      break;
	    }
	  }
	  if( j == c.size() ) { // found all literals -> same clause! (because also same size)
	    hashClause = list[i]; break;	// store current reference, stop loop
	  }
	}
      }
    }
    // if not present, write clause to proof
    if( hashClause == CRef_Undef ) {
      
      if( opc != 0 ) { // perform check for the global proof only
	opcTmpCls.clear();
	if( extraClauseLit != lit_Undef ) opcTmpCls.push( extraClauseLit );
	for (int i = startIndex; i < endIndex; i++) { if( clause[i] != lit_Undef && clause[i] != extraClauseLit ) opcTmpCls.push( clause[i] ); }
	if( ! opc->addClause( opcTmpCls ) ) { cerr << "c adding clause " << opcTmpCls << " to global proof fails" << endl; assert(false); exit(13); }
      }
      
      // write to file
      if( opt_verboseProof ) fprintf(drupProofFile, "c add clause by %i\n", ownerID);
      if( extraClauseLit != lit_Undef ) fprintf(drupProofFile, "%i ", (var(extraClauseLit) + 1) * (-2 * sign(extraClauseLit) + 1)); // print this literal first (e.g. for DRAT clauses)
      for (int i = startIndex; i < endIndex; i++) {
	if( clause[i] == lit_Undef || clause[i] == extraClauseLit ) continue;	// print the remaining literal, if they have not been printed yet
	fprintf(drupProofFile, "%i ", (var(clause[i]) + 1) * (-2 * sign(clause[i]) + 1));
      }
      fprintf(drupProofFile, "0\n");
      
      if( useCounting ) {
	// add to clause storage
	tmpCls.clear(); 
	if( extraClauseLit != lit_Undef ) tmpCls.push( extraClauseLit );
	for( int i = 0 ; i < clause.size(); ++ i ) if( clause[i] != extraClauseLit ) tmpCls.push( clause [i] );
	CRef ref = ca.alloc( tmpCls , false ); // ok, extraLit is handled
	ca[ref].setLBD(1); // the clause is currently present once in the proof
	// add to hash table
	hashTable[thisHash].push_back( ref );
	if(opt_verboseProof)cerr << "c add clause " << ca[ref] << " to hash table "  << " (hash(" << thisHash << "): " << getHash( clause, extraClauseLit, startIndex, endIndex ) << " ) list:" << hashTable[thisHash] << endl;
      } else {
	if(opt_verboseProof)cerr << "c do not add to hash table" << endl;
      }
    } else { // else increase the counter of that clause by 1
      if( useCounting ) {
	ca[ hashClause ].setLBD(ca[ hashClause ].lbd() + 1); // re-use LBD
	if(opt_verboseProof)cerr << "c set counter of clause " << ca[ hashClause ] << " to " << ca[ hashClause ].lbd() << " (hash(" << thisHash << ": " << getHash( clause, extraClauseLit, startIndex, endIndex ) << " ) list:"  << hashTable[thisHash] << endl;
      } else {
	if(opt_verboseProof)cerr << "c do not add to hash table" << endl;
      }
    }
  
}


template <class T>
inline void ProofMaster::removeGlobalClause(const T& clause, const Lit& extraClauseLit, int ownerID, int startIndex, int endIndex)
{
  CRef hashClause = CRef_Undef;  
  int hashListEntry = -1;
  unsigned long long thisHash = HASHMAX;
  
  if( useCounting ) { // check whether the clause is in the proof multiple times 
    thisHash = getHash( clause, extraClauseLit, startIndex, endIndex );
    const vector<CRef>& list = hashTable[ thisHash ];
    if(opt_verboseProof) cerr << "c list with hash " << thisHash << ": " << list << endl;
    if( list.size() > 0 ) { // there are clauses that have to be matched
      matchArray.nextStep();
      int clauseSize = 0 ;
      if( extraClauseLit != lit_Undef ) { clauseSize ++; matchArray.setCurrentStep( toInt ( extraClauseLit ) ); } // mark all literals of the current clause
      for( int i = startIndex ; i < endIndex; ++ i ) {
	if( extraClauseLit != clause[i] ) {
	  clauseSize ++;
	  matchArray.setCurrentStep( toInt ( clause[i] ) ); // mark all literals of the current clause
	}
      }
      for( int i = 0 ; i < list.size(); ++ i ) {
	const Clause& c = ca[ list[i] ];
	if( c.size() != clauseSize ) continue; // not the same clause, if the size check fails
	int j = 0;
	for(  ; j < c.size(); ++ j ) { // try to find all literals of the current clause in the matchArray
	  if( ! matchArray.isCurrentStep( toInt(c[j] ) ) ) {
	    break;
	  }
	}
	if( j == c.size() ) { // found all literals -> same clause! (because also same size)
	  hashListEntry = i; hashClause = list[i]; break;	// store current reference, stop loop
	}
      }
      assert( hashClause != CRef_Undef && "clause to be deleted has to be found!" );
    }
  }
  // if not present, write clause to proof
  assert( (!useCounting || hashClause != CRef_Undef) && "a clause that is deleted should be present in the proof, at least if counting is used" );
  
  if( !useCounting ||  hashClause != CRef_Undef ) { // for the safety of the proof do not remove clauses that are not present!
      assert( (!useCounting || ca[ hashClause ].lbd() > 0) && "all clauses in the proof should be present at least once" );
      if( useCounting ) {
	ca[ hashClause ].setLBD(ca[ hashClause ].lbd() - 1); // re-use LBD, decrease presence of clause
	if(opt_verboseProof)cerr << "c decrease counter of clause " << ca[ hashClause ] << " to " << ca[ hashClause ].lbd() << " (hash: " << getHash( clause, extraClauseLit, startIndex, endIndex ) << " )" << endl;
      }
      if( !useCounting || ca[ hashClause ].lbd() == 0 ) {
	
	if( opc != 0 ) { // perform check for the global proof only
	  opcTmpCls.clear();
	  if( extraClauseLit != lit_Undef ) opcTmpCls.push( extraClauseLit );
	  for (int i = startIndex; i < endIndex; i++) { if( clause[i] != lit_Undef && clause[i] != extraClauseLit ) opcTmpCls.push( clause[i] ); }
	  opc->removeClause( opcTmpCls );
	}
	
	// write to file
	if( opt_verboseProof ) fprintf(drupProofFile, "c remove clause by %i\n", ownerID);
	fprintf(drupProofFile, "d "); // clause should be deleted
	if( extraClauseLit != lit_Undef ) fprintf(drupProofFile, "%i ", (var(extraClauseLit) + 1) * (-2 * sign(extraClauseLit) + 1)); // print this literal first (e.g. for DRAT clauses)
	for (int i = startIndex; i < endIndex; i++) {
	  if( clause[i] == lit_Undef || clause[i] == extraClauseLit ) continue;	// print the remaining literal, if they have not been printed yet
	  fprintf(drupProofFile, "%i ", (var(clause[i]) + 1) * (-2 * sign(clause[i]) + 1));
	}
	fprintf(drupProofFile, "0\n");
	
	if( useCounting ) {
	  vector<CRef>& list = hashTable[ thisHash ];
	  // remove entry from hashTable (fast, unsorted)
	  if(opt_verboseProof)cerr << "c remove clause " << ca[ list[hashListEntry] ] << " from hash table " << " (hash: " << getHash( clause, extraClauseLit, startIndex, endIndex ) << " )" << endl;
	  list[ hashListEntry ] = list[ list.size() - 1 ];
	  list.pop_back();
	  
	  // remove clause from storage TODO: garbage collect? (remove from hash table before garbage collect!)
	  ca[ hashClause ].mark(1);
	  ca.free(hashClause);	
	}
      }

    } else if( useCounting ) {
      static bool didit = false; // will be printed at most once
      if( !didit ) {
	cerr << "c should delete a clause that is not present: " << clause << endl;
	didit = true;
      }
    }
}


inline void ProofMaster::addUnitToProof(const Lit& unit, int ownerID, bool local)
{
  assert( !local && "yet, local proofs are not supported" );
  
  if( local ) { // simply extend the local pool
    if( ownerID == -1 ) ownerID = threads; // correct owner ID
    localClauses[ownerID].push_back( unit ); // do not add the extra lit twice!
    localClauses[ownerID].push_back( lit_Undef ); // mark the end of the clause with "lit_Undef"
  } else {
    // lock
    ownLock.lock();
    // add the clause to the global proof
    addUnitToGlobalProof(unit, ownerID);
    // unlock
    ownLock.unlock();
  }
}


inline void ProofMaster::addUnitsToProof(const vec< Lit >& units, int ownerID, bool local)
{
  assert( !local && "yet, local proofs are not supported" );
  if( local ) { // simply extend the local pool
    if( ownerID == -1 ) ownerID = threads; // correct owner ID
    for( int i = 0 ; i < units.size(); ++ i ) {
      localClauses[ownerID].push_back( units[i] ); // do not add the extra lit twice!
      localClauses[ownerID].push_back( lit_Undef ); // mark the end of the clause with "lit_Undef"
    }
  } else {
    // lock
    ownLock.lock();
    // add the clauses to the global proof
    for( int i = 0 ; i < units.size(); ++ i ) {
      addUnitToGlobalProof(units[i], ownerID);
    }
    // unlock
    ownLock.unlock();
  }
}

template <class T>
inline void ProofMaster::addToProof(const T& clause, const Lit& extraClauseLit,  int ownerID, bool local)
{
  assert( local == false && "yet, local clause blocks are not supported" );
  if( local ) { // simply extend the local pool
    if( extraClauseLit != lit_Undef ) localClauses[ownerID].push_back( extraClauseLit ); // have the extra literal first!
    for( int i = 0 ; i < clause.size(); ++ i ) 
      if( clause[i] != extraClauseLit ) localClauses[ownerID].push_back( clause[i] ); // do not add the extra lit twice!
    localClauses[ownerID].push_back( lit_Undef ); // mark the end of the clause with "lit_Undef"
  } else { // interesting part, write to global proof
    if(opt_verboseProof)cerr << "c PM [" << ownerID << "] adds clause " << clause << endl;
    // lock
    ownLock.lock();
    // add the clause to the global proof (or increase the counter of an existing clause)
    addGlobalClause( clause, extraClauseLit, ownerID, 0, clause.size() );
    // unlock
    ownLock.unlock();
  }
}


template <class T>
inline void ProofMaster::addInputToProof(const T& clause, int ownerID, int numberOfOccurrence, bool isNewClause)
{
    CRef hashClause = CRef_Undef;
    unsigned long long thisHash = HASHMAX;
    
    if(opt_verboseProof)cerr << "c PM add input clause (" << numberOfOccurrence << " times): " << clause << endl;
    
    if( useCounting ) thisHash = getHash( clause, lit_Undef, 0, clause.size() ); // get hash for the current clause
    
    if( useCounting && !isNewClause ) { // check whether the clause already exists
      const vector<CRef>& list = hashTable[ thisHash ];
      if( list.size() > 0 ) { // there are clauses that have to be matched
	matchArray.nextStep();
	int clauseSize = 0 ;
	for( int i = 0 ; i < clause.size(); ++ i ) {
	  clauseSize ++;
	  matchArray.setCurrentStep( toInt ( clause[i] ) ); // mark all literals of the current clause
	}
	for( int i = 0 ; i < list.size(); ++ i ) {
	  const Clause& c = ca[ list[i] ];
	  if( c.size() != clauseSize ) continue; // not the same clause, if the size check fails
	  int j = 0;
	  for( ; j < c.size(); ++ j ) { // try to find all literals of the current clause in the matchArray
	    if( ! matchArray.isCurrentStep( toInt(c[j] ) ) ) {
	      break;
	    }
	  }
	  if( j == c.size() ) { // found all literals -> same clause! (because also same size)
	    hashClause = list[i]; break;	// store current reference, stop loop
	  }
	}
      }
    }
    // if not present, write clause to proof
    if( hashClause == CRef_Undef ) {
      
      if( opc != 0 ) { // perform check for the global proof only
	opcTmpCls.clear();
	for (int i = 0; i < clause.size(); i++) { if( clause[i] != lit_Undef ) opcTmpCls.push( clause[i] ); }
	if( !opc->addClause( opcTmpCls ) ) { cerr << "c adding clause " << opcTmpCls << " to global proof fails" << endl; assert(false); exit(13); }
      }
      
      // write to file
      if( opt_verboseProof ) fprintf(drupProofFile, "c add clause by %i\n", ownerID);
      
      // add enough copies of the clause to the proof!
      for( int nrCopy = 0; nrCopy < numberOfOccurrence; ++ nrCopy ) {
	for (int i = 0; i < clause.size(); i++) {
	  if( clause[i] == lit_Undef ) continue;	// print the remaining literal, if they have not been printed yet
	  fprintf(drupProofFile, "%i ", (var(clause[i]) + 1) * (-2 * sign(clause[i]) + 1));
	}
	fprintf(drupProofFile, "0\n");
	if( useCounting ) break; // if use counting, then stop after the first copy!
      }
      
      if( useCounting ) {
	// add to clause storage
	CRef ref = ca.alloc( clause , false ); // ok, no need for an extra literal!
	ca[ref].setLBD( numberOfOccurrence ); // the clause is currently present once in the proof
	// add to hash table
	if(opt_verboseProof)cerr << "c add clause " << ca[ ref ] << " to hash table" << endl;
	assert( thisHash != HASHMAX && "the hash cannot be HASHMAX if counting is used");
	hashTable[thisHash].push_back( ref );
	if(opt_verboseProof)cerr << "c set counter of clause " << ca[ ref ] << " to " << ca[ref].lbd() << " (hash: " << getHash( clause, lit_Undef, 0, clause.size() ) << " ) list:" << hashTable[thisHash] << endl;
      } else {
	if(opt_verboseProof)cerr << "c do not add to hash table" << endl;
      }
    } else { // else increase the counter of that clause
      if( useCounting ) {
	ca[ hashClause ].setLBD(ca[ hashClause ].lbd() + numberOfOccurrence); // re-use LBD
	if(opt_verboseProof)cerr << "c set counter of clause " << ca[ hashClause ] << " to " << ca[ hashClause ].lbd() << " (hash(" << thisHash << "): " << getHash( clause, lit_Undef, 0, clause.size() ) << " )" << endl;
      } else {
	if(opt_verboseProof)cerr << "c do not add to hash table" << endl;
      }
    }
}


inline void ProofMaster::delFromProof(const Lit& unit, int ownerID, bool local)
{
  assert( !local && "yet, local proofs are not supported" );
  if( local ) { // simply extend the local pool
    if( ownerID == -1 ) ownerID = threads; // correct owner ID
    localClauses[ownerID].push_back( lit_Error ); // define that this clause is to be deleted!
    localClauses[ownerID].push_back( unit );	    // add unit literal
    localClauses[ownerID].push_back( lit_Undef ); // mark the end of the clause with "lit_Undef"
  } else { // interesting part, write to global proof
    // lock
    ownLock.lock();
    if(opt_verboseProof)cerr << "c PM [" << ownerID << "] deletes unit clause " << unit << endl;
    CRef hashClause = CRef_Undef;
    int hashListEntry = -1;
    unsigned long long thisHash = HASHMAX;
    if( useCounting ) {
      thisHash = getHash( unit );
      const vector<CRef>& list = hashTable[ thisHash ];
      if( list.size() > 0 ) { // there are clauses that have to be matched
	for( int i = 0 ; i < list.size(); ++ i ) {
	  const Clause& c = ca[ list[i] ];
	  if( c.size() != 1 || c[0] != unit ) continue; // not the same clause, if the size check fails
	  hashListEntry = i; hashClause = list[i]; 	// store current reference
	  break;	// stop loop
	}
      }
      assert( hashClause != CRef_Undef && "the clause to be deleted has to be present in the proof!" );
    }
    // if not present, write clause to proof
    assert( (!useCounting || hashClause != CRef_Undef ) && "a clause that is deleted should be present in the proof" );
    if( hashClause != CRef_Undef ) { // for the safety of the proof do not remove clauses that are not present!

      assert( useCounting && "can find a hash clause only, if counting is enabled" );
      assert( ca[ hashClause ].lbd() > 0 && "all clauses in the proof should be present at least once" );
      ca[ hashClause ].setLBD(ca[ hashClause ].lbd() - 1); // re-use LBD, decrease presence of clause
      if(opt_verboseProof)cerr << "c decrease the counter of clause " << ca[ hashClause ] << " to " << ca[ hashClause ].lbd() << endl;
      if( ca[ hashClause ].lbd() == 0 ) {
	
	if( opc != 0 ) {	// check proof 
	  opc->removeClause(unit);
	}
	
	// write to file
	if( opt_verboseProof ) fprintf(drupProofFile, "c delete clause by %i\n", ownerID);
	fprintf(drupProofFile, "d %i 0\n", (var(unit) + 1) * (-2 * sign(unit) + 1));
	
	// remove entry from hashTable (fast, unsorted)
	vector<CRef>& list = hashTable[ thisHash ];
	if(opt_verboseProof)cerr << "c remove clause from hash table: " << ca[ list[ hashListEntry ]] << " (hash (" << thisHash<< "): " << getHash( unit ) << " )" << endl;
	list[ hashListEntry ] = list[ list.size() - 1 ];
	list.pop_back();
	
	// remove clause from storage TODO: garbage collect? (remove from hash table before garbage collect!)
	ca[ hashClause ].mark(1);
	ca.free(hashClause);
      }
    } else {
      if( useCounting ) {
	static bool didit = false; // will be printed at most once
	if( !didit ) {
	  if(opt_verboseProof)cerr << "c owner[" << ownerID << "] should delete a unit clause that is not present: " << unit << endl;
	  didit = true;
	  assert( false && "remove non-existing clause" );
	}
      } else { // no counting, print all deletions
	if( opc != 0 ) {	// check proof 
	  opc->removeClause(unit);
	}
	if( opt_verboseProof ) fprintf(drupProofFile, "c add clause by %i\n", ownerID);
	fprintf(drupProofFile, "d %i 0\n", (var(unit) + 1) * (-2 * sign(unit) + 1));
      }
    }

    // unlock
    ownLock.unlock();
  }
}

template <class T>
inline void ProofMaster::delFromProof(const T& clause, const Lit& extraClauseLit, int ownerID, bool local)
{
  assert( !local && "yet, local proofs are not supported" );
  if( local ) { // simply extend the local pool
    if( ownerID == -1 ) ownerID = threads; // correct owner ID
    localClauses[ownerID].push_back( lit_Error ); // define that this clause is to be deleted!
    if( extraClauseLit != lit_Undef ) localClauses[ownerID].push_back( extraClauseLit ); // have the extra literal first!
    for( int i = 0 ; i < clause.size(); ++ i ) 
      if( clause[i] != extraClauseLit ) localClauses[ownerID].push_back( clause[i] ); // do not add the extra lit twice!
    localClauses[ownerID].push_back( lit_Undef ); // mark the end of the clause with "lit_Undef"
  } else { // interesting part, write to global proof
    // lock
    ownLock.lock();
    if(opt_verboseProof)cerr << "c PM [" << ownerID << "] remove clause " << extraClauseLit << " " << clause << endl;
    if( clause.size() == 0 ) assert(false && "empty clauses should not be removed");
    // remove the clause from the global proof (or decrease the counter)
    removeGlobalClause(clause,extraClauseLit,ownerID, 0,clause.size());
    // unlock
    ownLock.unlock();
  }
}


template <class T>
inline unsigned long long ProofMaster::getHash(const T& clause, const Lit& extraClauseLit, int startIndex, int endIndex)
{
    unsigned long long sum = 0, prod = 1, X = 0;
    // process extra lit
    if( extraClauseLit != lit_Undef ) {
      const int l = toInt( extraClauseLit );
      prod *= l; sum += l; X ^= l;
    }
    
    for( int i = startIndex ; i < endIndex; ++ i ) 
    { 
      if( clause[i] != extraClauseLit ) { // but do not process the extraLit twice!
	const int l = toInt( clause[i] );
	prod *= l; sum += l; X ^= l;
      }
    }
    return ((1023 * sum + prod ^ (31 * X)) % HASHMAX); 
}

inline long long unsigned int ProofMaster::getHash(const Lit& unit)
{
    unsigned long long sum = 0, prod = 1, X = 0;
    for( int i = 0 ; i < 1; ++ i ) 
    { 
      const int l = toInt( unit );
      prod *= l; sum += l; X ^= l;
    }
    return (1023 * sum + prod ^ (31 * X)) % HASHMAX; 
}

inline void ProofMaster::setOnlineProofChecker(OnlineProofChecker* setUpChecker)
{
  assert( opc == 0 && "do not overwrite previous handle" );
  opc = setUpChecker;
}

inline void ProofMaster::addCommentToProof(const char* text, int ownerID)
{
  ownLock.lock();
  if( ownerID == -1 ) ownerID = threads;
  fprintf(drupProofFile, "c [by %d] %s\n", ownerID, text);  
  ownLock.unlock();
}



#endif