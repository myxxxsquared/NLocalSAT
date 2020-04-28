/**************************************************************************************[Technique.h]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#ifndef TECHNIQUE_HH
#define TECHNIQUE_HH

#include "core/Solver.h"
#include "utils/System.h"

#include "coprocessor-src/CoprocessorThreads.h"
#include "coprocessor-src/CP3Config.h"
using namespace Minisat;

namespace Coprocessor {

/** template class for all techniques that should be implemented into Coprocessor
 *  should be inherited by all implementations of classes
 */
class Technique {
 
protected:
  CP3Config& config;             // store the configuration for the whole preprocessor
  
  bool modifiedFormula;         // true, if subsumption did something on formula
  bool isInitialized;           // true, if the structures have been initialized and the technique can be used
  uint32_t myDeleteTimer;       // timer to control which deleted variables have been seen already
  
  int thisPelalty;              // how many attepts will be blocked, before the technique is allowed to perform preprocessing again
  int lastMaxPenalty;           // if the next simplification is unsuccessful, block the simplification for more than the given number
  
  ClauseAllocator& ca;          // clause allocator for direct access to clauses
  ThreadController& controller; // controller for parallel execution
    
  bool didPrintCannotDrup;      // store whether the drup warning has been reported already
  bool didPrintCannotExtraInfo; // store whether the extraInfo warning has been reported already
    
public:
  
  Technique( CP3Config& _config, ClauseAllocator& _ca, ThreadController& _controller );
  
  /** return whether some changes have been applied since last time
   *  resets the counter after call
   */
  bool appliedSomething();

  /** call this method for each clause when the technique is initialized with the formula 
   *  This method should be overwritten by all techniques that inherit this class
   */
  void initClause( const CRef cr );
  
  /** free resources of the technique, which are not needed until the technique is used next time
   *  This method should be overwritten by all techniques that inherit this class
   */
  void destroy();
  
  /** This method should be used to print the statistics of the technique that inherits from this class
   */
  void printStatistics( ostream& stream );

  /** per call to the inprocess method of the preprocessor, allow a technique to have this number more steps */
  void giveMoreSteps();
  
protected:
  /** call this method to indicate that the technique has applied changes to the formula */
  void didChange();
  
  /** reset counter, so that complete propagation is executed next time 
   *  This method should be overwritten by all techniques that inherit this class
   */
  void reset();

  /// indicate that this technique has been initialized (reset if destroy is called)
  void initializedTechnique();
  
  /// return true, if technique can be used without further initialization
  bool isInitializedTechnique();
  
  /** give delete timer */
  uint32_t lastDeleteTime();
  
  /** update current delete timer */
  void updateDeleteTime( const uint32_t deleteTime );
  
  /** ask whether a simplification should be performed yet */
  bool performSimplification();
  
  /** return whether next time the simplification will be performed */
  bool willSimplify() const;
  
  /** report that the current simplification was unsuccessful */
  void unsuccessfulSimplification();
  
  /** tell via stream that the technique does not support DRUP proofs */
  void printDRUPwarning(ostream& stream, const string s);

  /** tell via stream that the technique does not support extra clause info proofs */
  void printExtraInfowarning(ostream& stream, const string s);
  
};

inline void Technique::giveMoreSteps()
{
  assert( false && "needs to be overwritten" );
}


inline Technique::Technique( Coprocessor::CP3Config& _config, ClauseAllocator& _ca, Coprocessor::ThreadController& _controller )
: config( _config )
, modifiedFormula(false)
, isInitialized( false )
, myDeleteTimer( 0 )
, thisPelalty(0)
, lastMaxPenalty(0)
, ca( _ca )
, controller( _controller )
, didPrintCannotDrup(false)
, didPrintCannotExtraInfo(false)
{}

inline bool Technique::appliedSomething()
{
  bool modified = modifiedFormula;
  modifiedFormula = false;
  return modified; 
}

inline void Technique::didChange()
{
  modifiedFormula = true;
}

inline void Technique::initClause(const CRef cr)
{
  assert( false && "This method has not been implemented." );   
}

inline void Technique::reset()
{
  assert( false && "This method has not been implemented." ); 
}

inline void Technique::initializedTechnique()
{
  isInitialized = true;
}

inline bool Technique::isInitializedTechnique()
{
  return isInitialized;
}


inline void Technique::destroy()
{
  assert( false && "This method has not been implemented." ); 
}

inline void Technique::printStatistics(ostream& stream)
{
  /* // example output
  stream << "c [STAT] EE " << eeTime << " s, " << steps << " steps" << endl;
  stream << "c [STAT] EE-gate " << gateTime << " s, " << gateSteps << " steps" << endl;
  */
  assert( false && "This method has not been implemented" );
}

inline uint32_t Technique::lastDeleteTime()
{
  return myDeleteTimer;
}

inline void Technique::updateDeleteTime(const uint32_t deleteTime)
{
  myDeleteTimer = deleteTime;
}

inline bool Technique::performSimplification()
{
  bool ret = (thisPelalty == 0);
  thisPelalty = (thisPelalty == 0 ) ? thisPelalty : thisPelalty - 1; // reduce current wait cycle if necessary!
  return ret; // if there is no penalty, apply the simplification!
}

inline bool Technique::willSimplify() const
{
  return thisPelalty == 0;
}


inline void Technique::unsuccessfulSimplification()
{
  thisPelalty = ++lastMaxPenalty;
}

inline void Technique::printDRUPwarning(ostream& stream, const string s)
{
  if( ! didPrintCannotDrup ) stream << "c [" << s << "] cannot produce DRUP proofs" << endl;
  didPrintCannotDrup = true;
}

inline void Technique::printExtraInfowarning(ostream& stream, const string s)
{
  if( ! didPrintCannotExtraInfo ) stream << "c [" << s << "] cannot handle clause/variable extra information" << endl;
  didPrintCannotExtraInfo = true;
}



}

#endif