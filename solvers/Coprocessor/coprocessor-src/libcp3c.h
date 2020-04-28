/***************************************************************************************[libcp3c.h]
Copyright (c) 2013, Norbert Manthey, All rights reserved.

 Headerffile to work with Coprocessor as a library
 
 Methods provide basic access to the preprocessor
 
 At the moment only a single instance of the preprocessor can be initialized
 due to the option system, which currently relies on the Minisat option class
 
 
 NOTE: Building a tool with the dynamic library:
 1) make sure, the file libcp3.so is located in the right directory (here, in '.')
 2) to the usual link command of your tool add the following parameters:
  -L . -lcp3 -lpthread -lz -lrt
  
 NOTE: Running your tool with the dynamic library:
 1) make sure the file libcp3.so is located at a place where it can be found
**************************************************************************************************/

#ifndef LIBCPH_H
#define LIBCPH_H

// to represent formulas and the data type of truth values
#include "stdint.h"


// use these values to cpecify the model in extend model
#ifndef l_True
#define l_True  0 // gcc does not do constant propagation if these are real constants.
#endif

#ifndef l_False
#define l_False 1
#endif 

#ifndef l_Undef
#define l_Undef 2
#endif

// #pragma GCC visibility push(hidden)
// #pragma GCC visibility push(default)
// #pragma GCC visibility pop // now we should have default!

// only if compiling with g++! -> has to be a way with defines!
extern "C" {

  /** initialize a preprocessor instance, and return a pointer to the maintain structure */
  extern void* CPinit( const char* presetConfig = 0);
  
  /** call the preprocess method of the preprocessor */
  extern void CPpreprocess(void* preprocessor);
  
  /** destroy the preprocessor and set its value to 0 */
  extern void CPdestroy(void** preprocessor);
  
  /** parse the options of the command line and pass them to the preprocessor */
  extern void CPparseOptions (void* preprocessor, int* argc, char** argv, int strict);
  extern void CPparseOptionString (void* preprocessor, char* argv);
  
  /** set CP3 to simulate predefined behavior 
   */
  extern void CPsetPresetConfig (void* preprocessor, const char* presetConfig);
  
  /** add a literal to the solver, if lit == 0, end the clause and actually add it */
  extern void CPaddLit (void* preprocessor, int lit);
  
  /** return the version of the library verison */
  extern float CPversion (void* preprocessor);
  
  /** there is another literal inside the sat solver */
  extern int CPhasNextOutputLit(void* preprocessor);
  
  /** give the actual next literal */
  extern int CPnextOutputLit(void* preprocessor);
  
  /** start output from the beginning */
  extern void CPresetOutput(void* preprocessor);
  
  /** freeze the given variable, so that it is not altered semantically 
   * Note: the variable might still be pushed, so that it is necessary to call giveNewLit()
   */
  extern void CPfreezeVariable(void* preprocessor, int variable );
  
  /** returns the new literal of a literal 
   * @param oldLit literal before calling preprocess()
   * @return representation of the literal after preprocessing
   */
  extern int CPgetReplaceLiteral(void* preprocessor, int oldLit );
  
  /** recreate the variables of the given model from the state of the preprocessor 
   *  Note: will copy the model twice to be able to change the data type of the model into minisat vector Minisat::Vec
   */
  // extern void CPpostprocessModel(void* preprocessor, std::vector<uint8_t>& model );
  
  /** reset the model input procedure, and the postprocessing procedure */
  extern void CPresetModel(void* preprocessor);

  /** pass a (satisfied) literal of the current model to the preprocessor 
   * @param pol polarity of the next variable in the model (0=false, 1=true)
   */
  extern void CPpushModelBool(void* preprocessor, int pol);
  
  /** pass a (satisfied) literal of the current model to the preprocessor */
  extern void CPgiveModelLit(void* preprocessor, int literal);
  
  /** pass a (satisfied) literal of the current model to the preprocessor */
  extern void CPpostprocessModel(void* preprocessor);
  
  /** extract the next model literal from the postprocessed model*/
  extern int CPgetFinalModelLit(void* preprocessor);
  
  /** return the number of variables in the postprocessed model */
  extern int CPmodelVariables(void* preprocessor);

  /** returns the number of variables of the formula that is inside the preprocessor
   *  Note: the number of variables can be higher inside the preprocessor, if techniques like
   *  rewriting or BVA have been used, since these techniques introduce new variables
   */
  extern int CPnVars(void* preprocessor);
  
  /** return the number of clauses that are inside the solver */
  extern int CPnClss(void* preprocessor);
  
  /** return the number of actual literals inside the formula */
  extern int CPnLits(void* preprocessor);
  
  /** return state of preprocessor */
  extern int CPok(void* preprocessor);
  
  /** return whether a given literal is already mapped to false */
  extern int CPlitFalsified(void* preprocessor, int lit);
}

// #pragma GCC visibility pop // back to what we had before

#endif