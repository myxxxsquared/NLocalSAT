/********************************************************************++++++++++++++++++[Shuffler.h]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

/** this class re-implements the rand-method so that it can be used more independently
 */
#include <stdint.h>
#include <vector>

#include "core/Solver.h"
#include "coprocessor-src/CoprocessorTypes.h"
#include "coprocessor-src/CP3Config.h"
using namespace Minisat;

namespace Coprocessor {
  
  class Randomizer {
    uint64_t hold;
  public:
    Randomizer() { hold = 0; };
    
    /** sets the current random value
    */
    void set( uint64_t newValue ){ hold = newValue; }

    /** return the next random value
    */
    uint64_t rand() { return (((hold = hold * 214013L + 2531011L) >> 16) & 0x7fff); }
    
    /** return the next random value modulo some other value
    */
    uint64_t rand(uint64_t upperBound) { uint64_t ret = rand(); return upperBound > 0 ? ret % upperBound : 0; }
  };


  class VarShuffler 
  {
    CP3Config& config;
    uint32_t variables;
    vector< Lit > replacedBy;
    uint32_t seed;
    
    Randomizer randomizer;
    
  public:
    VarShuffler(CP3Config &_config);

    /** apply full shuffling process to clauses */
    void process(vec< Minisat::CRef >& clauses, vec< Minisat::CRef >& learnts, vec< Lit >& trail, uint32_t vars, ClauseAllocator& ca);
    
    /** remap model to original variables */
    void unshuffle( vec<lbool>& model, uint32_t vars );
    
  protected:
    /** set seed fo shuffling (it is a pivate seed, independent from rand() */
      void setSeed( uint32_t s );
    
    /** create a shuffle - mapping */
      void setupShuffling(uint32_t vars);
    
    /** apply the mapping to the formula */
      void shuffle( vec<CRef>& clauses, ClauseAllocator& ca, bool shuffleOrder = false );
      
      /** apply mapping */
      void shuffle( vec<Lit>& lits, bool shuffleOrder = false );
      


  };

};