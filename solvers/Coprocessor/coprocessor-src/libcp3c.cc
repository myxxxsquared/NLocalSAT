/**************************************************************************************[libcp3c.cc]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Coprocessor.h"
using namespace Minisat;

/** struct that stores the necessary data for a preprocessor */
struct libcp3 {
  Minisat::vec<Minisat::Lit> currentClause;
  Minisat::CoreConfig* solverconfig;
  Minisat::Solver* solver;
  Coprocessor::CP3Config* cp3config;
  Coprocessor::Preprocessor* cp3;
  // for outputting stuff:
  int outputCls; // current clause that is printed
  int outputLit; // current literal of current clause that is printed
  int modelLit; // current literal of model that is printed
  vec<lbool> model; // current model
  libcp3 () : outputCls(0), outputLit(0), modelLit(0) {} // default constructor to ensure everything is set to 0
};

// #pragma GCC visibility push(hidden)
// #pragma GCC visibility push(default)
// #pragma GCC visibility pop // now we should have default!

//#pragma GCC visibility push(default)

extern "C" {
  
    void* 
    CPinit(const char* presetConfig) {
    libcp3* cp3 = new libcp3;
    cp3->solverconfig = new Minisat::CoreConfig("");
    if( presetConfig  != 0 ) cp3->solverconfig->setPreset(presetConfig );
    cp3->cp3config = new Coprocessor::CP3Config("");
    if( presetConfig  != 0 ) cp3->cp3config->setPreset(presetConfig );
    cp3->solver = new Minisat::Solver (*(cp3->solverconfig));
    cp3->cp3 = new Coprocessor::Preprocessor ( cp3->solver, *(cp3->cp3config) );
    return cp3;
  }

  void  
  CPdestroy(void** preprocessor)
  {
    libcp3** cp3 = (libcp3**) preprocessor;
    delete (*cp3)->cp3config;
    delete (*cp3)->solver;
    // delete (*cp3)->cp3; // not necessary, because solver is already killing it
    delete (*cp3)->solverconfig;
    delete (*cp3);
    (*cp3) = 0;
  }

  void 
  CPpreprocess(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    cp3->cp3->preprocess();
  }

  int 
  CPhasNextOutputLit(void* preprocessor) { 
    libcp3* cp3 = (libcp3*) preprocessor;
    if( cp3->outputCls < cp3->solver->clauses.size() + cp3->solver->trail.size() ) return 1; // there are more clauses to go
    if( cp3->outputCls >= cp3->solver->clauses.size() + cp3->solver->trail.size() ) return 0; // all clauses have been skipped
    // here, only the very last clause needs to be considered!
    if( cp3->outputCls == cp3->solver->trail.size() + cp3->solver->clauses.size() && cp3->outputLit <= 1 ) return 1; // have seen at most one literal of the very last clause yet (there is at least the termination literal)
    if( cp3->outputCls > cp3->solver->trail.size() && // there is a longer clause
      cp3->outputLit <= cp3->solver->ca[ cp3->solver->clauses[ cp3->solver->clauses.size() - 1 ] ].size() // have seen all its literals, but not the termination symbol
    ) return 1;
    return 0;
  }
  
  int 
  CPnextOutputLit(void* preprocessor) {   
    if( !CPhasNextOutputLit(preprocessor) ) return 0;
    libcp3* cp3 = (libcp3*) preprocessor;
    //cerr << "c ask for literal " << cp3->outputLit << " if cls " << cp3->outputCls << " (trail: " << cp3->solver->trail.size() << ", clss: " << cp3->solver->clauses.size() << ")" << endl;
    if( cp3->outputCls < cp3->solver->trail.size() ) { // currently reading the trail
      if( cp3->outputLit >= 1 ) { // reached end of unit clause?
	cp3->outputLit = 0;
	cp3->outputCls ++;
	return 0; // terminate current clause
      } 
      const Lit l = cp3->solver->trail[ cp3->outputCls ];
      cp3->outputLit ++;
      return sign(l) ? ( -var(l) -1 ) : (var(l) +1);
    }
    
    if( cp3->outputCls >= cp3->solver->trail.size() + cp3->solver->clauses.size() ) return 2 << 31; // undefined behavior!
    
    // reading the clauses - jumping over the trail
    const Clause& c = cp3->solver->ca[  cp3->solver->clauses[cp3->outputCls - cp3->solver->trail.size()] ];
    if (c.size() <= cp3->outputLit) { // reached end of the clause
	cp3->outputLit = 0; cp3->outputCls ++;
	return 0; // terminate current clause
    }
    const Lit l = c[ cp3->outputLit ]; 
    cp3->outputLit ++;
    return sign(l) ? ( -var(l) -1 ) : (var(l) +1);
  }
  
  void 
  CPresetOutput(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    cp3->outputCls = 0; cp3->outputLit = 0;
  }

//     void  
//   CPpostprocessModel(void* preprocessor, std::vector< uint8_t >& model)
//   {
//     libcp3* cp3 = (libcp3*) preprocessor;
//     // dangerous line, since the size of the elements inside the vector might be different
//     
//     for( int i = 0 ; i < model.size(); ++ i ) cp3model.push( Minisat::toLbool(model[i]) );
//     cp3->cp3->extendModel(cp3model);
//     model.clear();
//     for( int i = 0 ; i < cp3model.size(); ++ i ) model.push_back( toInt(cp3model[i]) );
//   }
  
  /** reset the model input procedure, and the postprocessing procedure */
  void 
  CPresetModel(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    cp3->model.clear();
    cp3->modelLit = 0;
  }
  
  /** pass a (satisfied) literal of the current model to the preprocessor */
  void 
  CPgiveModelLit(void* preprocessor, int literal) {
    libcp3* cp3 = (libcp3*) preprocessor;
    const Lit l = mkLit( literal < 0 ? - literal + 1 : literal - 1, literal < 0 );
    const Var v = var(l);
    while ( cp3->model.size() <= v ) cp3->model.push( l_Undef ); // make sure there is enough room
    cp3->model[ v ] = literal > 0 ? l_True : l_False; // add the information
  }
  
  /** pass a (satisfied) literal of the current model to the preprocessor 
   * @param pol polarity of the next variable in the model (0=false, 1=true)
   */
  void 
  CPpushModelBool(void* preprocessor, int pol) {
    libcp3* cp3 = (libcp3*) preprocessor;
    if( pol == 0 ) cp3->model.push( l_False );
    else cp3->model.push( l_True );
  }
  
  /** pass a (satisfied) literal of the current model to the preprocessor */
  void 
  CPpostprocessModel(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    cp3->cp3->extendModel(cp3->model);
  }
  
  /** extract the next model literal from the postprocessed model*/
  int 
  CPgetFinalModelLit(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    if( cp3->modelLit < cp3->model.size() ) {
      lbool s = cp3->model[ cp3->modelLit ];
      int ret = s == l_True ? cp3->modelLit + 1 : - cp3->modelLit - 1;
      cp3->modelLit ++;
      return ret;
    } else return 0;
  }

  
  /** return the number of variables in the postprocessed model */
  int 
  CPmodelVariables(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    return cp3->model.size();
  }

    void  
  CPfreezeVariable(void* preprocessor, int variable)
  {
    libcp3* cp3 = (libcp3*) preprocessor;
    cp3->cp3->freezeExtern(variable);
  }

    int  
  CPgetReplaceLiteral(void* preprocessor, int oldLit)
  {
    libcp3* cp3 = (libcp3*) preprocessor;
    return cp3->cp3->giveNewLit(oldLit);
  }

    void  
  CPparseOptions(void* preprocessor, int* argc, char** argv, int strict)
  {
    libcp3* cp3 = (libcp3*) preprocessor;
    cp3->cp3config->parseOptions(*argc,argv,strict != 0 );
  }
  
  void 
  CPparseOptionString (void* preprocessor, char* argv)
  {
    libcp3* cp3 = (libcp3*) preprocessor;
    cp3->cp3config->parseOptions(argv);
  }

   void 
   CPsetPresetConfig (void* preprocessor, const char* presetConfig) {
    libcp3* cp3 = (libcp3*) preprocessor;
    /*
    if( configNr == 1 ) {
      cp3->cp3config->opt_enabled = true;
      cp3->cp3config->opt_up = true;
      cp3->cp3config->opt_subsimp = true;
      cp3->cp3config->opt_sub_allStrengthRes = 3;
      cp3->cp3config->opt_bva = true;
      cp3->cp3config->opt_bva_Alimit =120000;
      cp3->cp3config->opt_bve=true;
      cp3->cp3config->opt_bve_lits=1;
      cp3->cp3config->opt_bve_bc=false;
      cp3->cp3config->opt_cce=true;
      cp3->cp3config->opt_cceSteps=2000000;
      cp3->cp3config->opt_ccelevel=1;
      cp3->cp3config->opt_ccePercent=100;
      cp3->cp3config->opt_unhide=true;
      cp3->cp3config->opt_uhd_UHLE=false;
      cp3->cp3config->opt_uhd_Iters=5;
      cp3->cp3config->opt_dense=true;
    } else if ( configNr == 2 ) {
      cp3->cp3config->opt_enabled = true;
      cp3->cp3config->opt_bva = true;
    }
    */
    cp3->solverconfig->setPreset(presetConfig);
    cp3->cp3config->setPreset(presetConfig);
  }
  
    void  
  CPaddLit(void* preprocessor, int lit)
  {
    libcp3* cp3 = (libcp3*) preprocessor;
      if( lit != 0 ) cp3->currentClause.push( lit > 0 ? mkLit( lit-1, false ) : mkLit( -lit-1, true ) );
      else { // add the current clause, and clear the vector
	// reserve variables in the solver
	for( int i = 0 ; i < cp3->currentClause.size(); ++i ) {
	  const Lit l2 = cp3->currentClause[i];
	  const Var v = var(l2);
	  while ( cp3->solver->nVars() <= v ) cp3->solver->newVar();
	}
	cp3->solver->addClause( cp3->currentClause );
	cp3->currentClause.clear();
      }
  }


   float 
  CPversion(void* preprocessor)
  {
#ifdef TOOLVERSION
    return TOOLVERSION / 100; // the number in TOOLVERSION gives the current version times 100
#else
    return -1;
#endif
  }

  
    int 
  CPnVars(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    return cp3->solver->nVars();
  }
  
  /** return the number of clauses that are inside the solver */
  int
  CPnClss(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    return cp3->solver->clauses.size() + cp3->solver->trail.size();
  }
  
  /** return the number of actual literals inside the formula */
  int 
  CPnLits(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    int sum = 0;
    for( int i = 0 ; i < cp3->solver->clauses.size(); ++i ) {
      sum += cp3->solver->ca[ cp3->solver->clauses[i] ].size();
    }
    sum += cp3->solver->trail.size();
    return sum;
  }

    int  
  CPok(void* preprocessor) {
    libcp3* cp3 = (libcp3*) preprocessor;
    return cp3->solver->okay();
  }

    int  
  CPlitFalsified(void* preprocessor, int lit) {
    libcp3* cp3 = (libcp3*) preprocessor;
    return cp3->solver->value( lit > 0 ? mkLit( lit-1, false ) : mkLit( -lit-1, true ) ) == l_False;
  }

}

// #pragma GCC visibility pop

//#pragma GCC visibility pop