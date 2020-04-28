/************************************************************************[EquivalenceElimination.cc]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/EquivalenceElimination.h"

#include <fstream>

using namespace Coprocessor;






static const int eeLevel = 1;

EquivalenceElimination::EquivalenceElimination(CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, Propagation& _propagation, Coprocessor::Subsumption& _subsumption)
: Technique(_config, _ca,_controller)
, gateSteps(0)
, gateTime(0)
, gateExtractTime(0)
, eeTime(0)
, equivalentLits(0)
, removedCls(0)
, removedViaSubsubption(0)
, steps(0)
, eqLitInStack(0)
, eqInSCC(0)
, eqIndex(0)
, isToAnalyze(0)
, propagation( _propagation )
, subsumption( _subsumption )
{}

void EquivalenceElimination::giveMoreSteps()
{
steps = steps < config.opt_ee_inpStepInc ? 0 : steps - config.opt_ee_inpStepInc;
}


bool EquivalenceElimination::process(Coprocessor::CoprocessorData& data)
{
  if( !performSimplification() ) return false; // do not perform simplification because of presiously failed runs?

  MethodTimer mv(&eeTime);
  modifiedFormula = false;
  if( !data.ok() ) return false;
  
  // do not simplify, if the formula is considered to be too large!
  if( !data.unlimited() && ( data.nVars() > config.opt_ee_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_ee_cls && data.nTotLits() > config.opt_ee_lits) ) return false;
  
  isToAnalyze.resize( data.nVars(), 0 );
    
  data.ma.resize(2*data.nVars());
  
  if( data.hasToPropagate() ) {
    if( l_False == propagation.process(data,true) ) {
      return modifiedFormula;
    }
    modifiedFormula = propagation.appliedSomething() || modifiedFormula;
  }
  
  // find SCCs and apply them to the "replacedBy" structure
  for( Var v = 0 ; v < data.nVars(); ++ v ) {
    eqDoAnalyze.push_back( mkLit(v,false) );
    if( config.ee_debug_out > 2 ) cerr << "c enable literal " << mkLit(v,false) << endl;
    isToAnalyze[ v ] = 1;
  }
  
  if( replacedBy.size() < data.nVars() ) { // extend replacedBy structure
    for( Var v = replacedBy.size(); v < data.nVars(); ++v )
      replacedBy.push_back ( mkLit(v,false) );
  }

 
  if( config.opt_ee_level > 1  && data.ok() ) {
    
    bool moreEquivalences = true;
    
    // repeat until fixpoint?!
    int iter = 0;
    vector<Circuit::Gate> gates;
    while( moreEquivalences ) {

      for( int i = 0 ; i < gates.size(); ++ i ) {
	gates[i].destroy();
      }
      gates.clear();

      iter ++;
      if( config.opt_ee_circuit_iters != -1 && iter > config.opt_ee_circuit_iters ) break;

      if( config.ee_debug_out > 2 ) {
	cerr << endl << "====================================" << endl;
	cerr << "intermediate formula before gates: [ok?: " << data.ok() << "]" << endl;
	for( int i = 0 ; i < data.getTrail().size(); ++ i ) cerr << "[" << data.getTrail()[i] << "]" << endl;
	for( int i = 0 ; i < data.getClauses().size(); ++ i )
	  if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << "[" << data.getClauses()[i] << "]" << ca[  data.getClauses()[i] ] << endl;
	cerr << "c learnts: " << endl;
	for( int i = 0 ; i < data.getLEarnts().size(); ++ i )
	  if( !ca[  data.getLEarnts()[i] ].can_be_deleted() ) cerr << "[" << data.getLEarnts()[i] << "]"  << ca[  data.getLEarnts()[i] ] << endl;    
	cerr << "====================================" << endl << endl;
      }

      if( data.hasToPropagate() ) {
	propagation.process(data,true);
	modifiedFormula = propagation.appliedSomething() || modifiedFormula;
      }
      
      Circuit circ(config,ca); 
      gateExtractTime = cpuTime() - gateExtractTime;
      circ.extractGates(data, gates);
      gateExtractTime = cpuTime() - gateExtractTime;
      if ( config.ee_debug_out > 2 ) {
	cerr << endl << "==============================" << endl;
	data.log.log(eeLevel,"found gates", gates.size());
	for( int i = 0 ; i < gates.size(); ++ i ) {
	  Circuit::Gate& gate = gates[i];
	  // data.log.log(eeLevel,"gate output",gate.getOutput());
	  if(config.ee_debug_out > 2) gate.print(cerr);
	}
	cerr << "==============================" << endl << endl;
	cerr << "c equivalences:" << endl;
	for ( Var v = 0 ; v < data.nVars(); ++v )
	  if( mkLit(v,false) != getReplacement( mkLit(v,false) ) )
	    cerr << "c " << v+1 << " == " << getReplacement( mkLit(v,false) ) << endl;
      }

      vector<Lit> oldReplacedBy = replacedBy;
      //vector< vector<Lit> >* externBig
    
      {
	if( config.ee_debug_out > 2 ) cerr << "c run miter EQ method [ok?: " << data.ok() << "]" << endl;
	moreEquivalences = findGateEquivalencesNew( data, gates );
	if( moreEquivalences )
	  if( config.ee_debug_out > 2 ) cerr << "c found new equivalences with the gate method! [ok?: " << data.ok() << "]" << endl;
	if( !data.ok() )
	  if( config.ee_debug_out > 2 ) cerr << "state of formula is UNSAT!" << endl;
      }
      
      if( config.opt_ee_level > 2 ) {
	if( config.ee_debug_out > 2 ) cerr << "c run gate method" << endl;
	moreEquivalences = moreEquivalences || findGateEquivalences( data, gates );
	if( moreEquivalences )
	  if( config.ee_debug_out > 2 ) cerr << "c found new equivalences with the gate method! [ok?: " << data.ok() << "]" << endl;
	if( !data.ok() )
	  if( config.ee_debug_out > 2 ) cerr << "state of formula is UNSAT!" << endl;
      }
      
      replacedBy = oldReplacedBy;
      
      if( !data.ok() ) { return modifiedFormula; }
      // after we extracted more information from the gates, we can apply these additional equivalences to the forula!
      if ( !moreEquivalences && iter > 1 ) {
	// cerr << "c no more gate equivalences found" << endl;
	break;
      } else {
	// cerr << "c more equi " << moreEquivalences << " iter= " << iter << endl;
      }
      moreEquivalences = false;
      bool doRepeat = false;
      int eeIter = 0;
      do {  // will set literals that have to be analyzed again!
	findEquivalencesOnBig(data);                              // finds SCC based on all literals in the eqDoAnalyze array!
	doRepeat = applyEquivalencesToFormula(data, (iter == 1 && eeIter == 0) );   // in the first iteration, run subsumption/strengthening and UP!
	moreEquivalences = doRepeat || moreEquivalences;
	eeIter ++;
	if( eeIter >= config.opt_ee_bigIters ) break;
      } while ( doRepeat && data.ok() );
      // cerr << "c moreEquivalences in iteration " << iter << " : " << moreEquivalences << " with BIGee iterations " << eeIter << endl;
    }
    if( ((const char*)config.opt_ee_aagFile) != 0  )
      writeAAGfile(data);
    
    if( data.hasToPropagate() ) {
      if( l_False == propagation.process(data,true) ) {
	return modifiedFormula;
      }
      modifiedFormula = propagation.appliedSomething() || modifiedFormula;
    }
  }
  
  //do binary reduction
  if( data.ok() ) {
    int eeIter = 0;
    do { 
      findEquivalencesOnBig(data);                              // finds SCC based on all literals in the eqDoAnalyze array!
      eeIter ++;
      if( eeIter >= config.opt_ee_bigIters ) break;
    } while ( applyEquivalencesToFormula(data ) 
    && data.ok()
    && !data.isInterupted()  
    && (data.unlimited() || steps < config.opt_ee_limit )
    ); // will set literals that have to be analyzed again!
    
    // if( config.ee_debug_out > 1 && )
    if (steps > config.opt_ee_limit ) { cerr  << "c abort global EE round, because step limit has been reached " << endl; }
    
    // cerr << "c ok=" << data.ok() << " toPropagate=" << data.hasToPropagate() <<endl;
    assert( (!data.ok() || !data.hasToPropagate() )&& "After these operations, all propagation should have been done" );
    
    
      if( config.ee_debug_out > 2 ) {
	cerr << endl << "====================================" << endl;
	cerr << "FINAL FORMULA after ELIMINATE: " << endl;
	for( int i = 0 ; i < data.getClauses().size(); ++ i )
	  if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getClauses()[i] ] << endl;
	for( int i = 0 ; i < data.getLEarnts().size(); ++ i )
	  if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getLEarnts()[i] ] << endl;    
	cerr << "====================================" << endl;
	cerr << "Solver Trail: " << endl;
	data.printTrail(cerr);
	cerr << endl << "====================================" << endl << endl;
	cerr << endl;
      }
  }
  if(! modifiedFormula ) unsuccessfulSimplification(); // notify system that nothing has been done here!
  return modifiedFormula;
}

void EquivalenceElimination::initClause(const CRef cr)
{
  
}

bool EquivalenceElimination::findGateEquivalencesNew(Coprocessor::CoprocessorData& data, vector< Circuit::Gate >& gates)
{
  // printDRUPwarning(cerr,"ee gate algorithm");
  
  gateTime  = cpuTime() - gateTime;
  vector< vector<int32_t> > varTable ( data.nVars() ); // store for each variable which gates have this variable as input
  vector< unsigned int > bitType ( data.nVars(), 0 );  // upper 4 bits are a counter to count how often this variable has been considered already as output
 
  const bool enqOut = true;
  const bool enqInp  = true;
  
  if( config.ee_debug_out > 2 ) cerr << "c has to Propagate: " << data.hasToPropagate() << endl;
  
  int oldEquivalences = data.getEquivalences().size();
  
  if( config.opt_eeGateBigFirst ) {
    if( config.ee_debug_out > 2 ) cerr << "c do BIG extraction " << endl;
    do { 
      findEquivalencesOnBig(data);                              // finds SCC based on all literals in the eqDoAnalyze array!
    } while ( applyEquivalencesToFormula(data ) && data.ok() ); // will set literals that have to be analyzed again!
  }
  
  
  if( config.ee_debug_out > 2 ) cerr << "c work with " << gates.size() << " gates [ok?: " << data.ok() << "]" << endl;
  // have gates per variable
  for( int i = 0 ; i < gates.size() ; ++ i ) {
   const Circuit::Gate& g = gates[i];
   switch( g.getType() ) {
     case Circuit::Gate::AND:
       // do not consider gate outputs of blocked gates!
       if( g.isFull() ) bitType[ var(g.x()) ] = bitType[ var(g.x()) ] | 1; // set output bit
       varTable[ var( g.a() ) ].push_back(i);
       varTable[ var( g.b() ) ].push_back(i);
       break;
     default:
       break;
   }
  }
  
  // have a queue of the current gates, perform per type
  deque< int > queue;
  vector< Var > equiVariables; // collect all the other equivalent variables in this vector
  deque< Var > currentVariables;
  deque< Var > *currentPtr = &currentVariables;
  
  MarkArray active;
  active.create( data.nVars() );
  active.nextStep();

  MarkArray reactivated;
  reactivated.create( data.nVars() );
  reactivated.nextStep();
  
  const bool putAllAlways = true;
  
  bool isMiter = true; // what to do with this variable?!
  for( Var v = 0; v < data.nVars(); ++ v ) {
    if( !putAllAlways && bitType[v] != 0 ) continue;
    currentPtr->push_back(v); 
    if( !putAllAlways ) active.setCurrentStep(v);
    // Assumption: inside a miter, each pure input variable has to have an even number of gates!
    if( (varTable[v].size() & 1) != 0 ) { 
      isMiter = false;
      if( config.ee_debug_out > 2 ) cerr << "c the given gate structure cannot be a miter, because variable " << v+1 << " has " << varTable[v].size() << " gates" << endl;
    }
  }
  
  int iter = 0;
  if( config.ee_debug_out > 2 ) {
  cerr << "current GATE variable queue: ";
  for( int i = 0 ; i < currentPtr->size(); ++ i ) cerr << currentVariables[i]+1 << " ";
  cerr << endl;
  }
  
  // structures to store temporary literals
  vector<Lit> upLits (2); upLits.clear();
  vector<Lit> eeLits (2); eeLits.clear();
  
  // as long as there are variables inside the queue
  while( currentPtr->size() > 0 ) {
      ++iter;
      if( iter & 127 == 0 ) cerr << "c at iteration " << iter << " there are " << currentPtr->size() << " variables" << endl;
      // iterate over the different gate types
      const Var v = currentPtr->front();
      currentPtr->pop_front();
      active.reset(v);
      // cerr << "c test variable " << v+1 << endl;
      if( config.ee_debug_out > 2 ) cerr << "c check variable " << v+1 << " with " << varTable[v].size() << " gates and replace literal " << getReplacement( mkLit(v,false ) ) << " [ok?: " << data.ok() << "]" << endl;
      // for all gates with this input variable:
      for( int i = 0 ; i < varTable[v].size(); ++ i ) {
	Circuit::Gate& g = gates[ varTable[v][i] ];
	if( g.isInvalid() ) continue;
	// literals of the current gate
	if( config.ee_debug_out > 2 ) cerr << "c check gate ";
	if( config.ee_debug_out > 2 ) g.print(cerr);
	Lit a = getReplacement( g.a() ); Lit b = getReplacement( g.b() ); Lit x = getReplacement( g.x() ); 
	if( config.ee_debug_out > 2 ) cerr << "c WHICH is rewritten " << x << " <-> AND(" << a << "," << b << ")" << endl;
	
	if( var(x) == var(a) || var(x) == var(b) || var(a) == var(b) ) continue; // such a gate would not be found during analysis ...
	
	// assigned value
	if ( data.value(a) != l_Undef || data.value(b) != l_Undef || data.value(x) != l_Undef) {
	  if( config.ee_debug_out > 2 ) cerr << "c gate has assigned inputs" << endl;
	  if ( data.value(a) == l_True ) {
	    if( config.opt_ee_eagerEquivalence ) setEquivalent(b,x);
	    data.addEquivalences( x,b );
	    if( config.ee_debug_out > 2 ) cerr << "c found equi " << x << " <=> " << b << endl;
// 	    b = getReplacement( g.b() );
// 	    x = getReplacement( g.x() );
	  } else if ( data.value(a) == l_False ) {
	    if( enqOut ) {
	      data.enqueue(~x);  data.addUnitToProof(~x);
	      if( config.ee_debug_out > 2 ) cerr << "c found imply " << ~x << endl;
	    }
	  }
	  if ( data.value(b) == l_True ) {
	    if( config.opt_ee_eagerEquivalence ) setEquivalent(a,x);
	    data.addEquivalences( x,a );
	    if( config.ee_debug_out > 2 ) cerr << "c found equi " << x << " <=> " << a << endl;
// 	    a = getReplacement( g.a() );
// 	    x = getReplacement( g.x() );
	  } else if ( data.value(b) == l_False ) {
	    if( enqOut ) {
	      data.enqueue(~x);  data.addUnitToProof(~x);
	      if( config.ee_debug_out > 2 ) cerr << "c found imply " << ~x << endl;
	    }
	  } else if ( data.value(x) == l_True) {
	    if( enqInp ) {
	      data.enqueue(a);  data.addUnitToProof(a);
	      data.enqueue(b);  data.addUnitToProof(b);
	      if( config.ee_debug_out > 2 ) cerr << "c found imply " << a << " and " << b << endl;
	    }
	  }
	  // do not reason with assigned gates!
	  continue;
	}
	// somehow same inputs
	if( a == b ) {
	  if( config.ee_debug_out > 2 ) cerr << "c found equivalence based on equivalent inputs " << x << " <-> AND(" << a << "," << b << ")" << endl; 
	  if( config.opt_ee_eagerEquivalence ) setEquivalent(a,x);
	  data.addEquivalences(x,a);
// 	  a = getReplacement( g.a() );
// 	  x = getReplacement( g.x() );
	} 

// These rules are unsound!
// 	else if ( a == ~b ) {
// 	  if( config.ee_debug_out > 2 ) cerr << "c find an unsatisfiable G-gate based on complementary inputs " << x << " <-> AND(" << a << "," << b << ")" << endl;  
// 	  if( enqOut ) {
// 	    if( config.ee_debug_out > 2 ) cerr << "c enqueue literal " << ~x << endl;
// 	    data.enqueue(~x);
// 	  }
// 	} 
// 	else if ( x == a ) {
// 	  if( config.ee_debug_out > 2 ) cerr << "c equi inputs G-gate " << x << " <-> AND(" << a << "," << b << ")" << endl;  
// 	  if( config.opt_ee_eagerEquivalence ) setEquivalent(b,x);
// // 	  b = getReplacement( g.b() );
// // 	  x = getReplacement( g.x() );
// 	  data.addEquivalences(x,b);
// 	} else if ( x == b ) {
// 	  if( config.ee_debug_out > 2 ) cerr << "c equi inputs G-gate " << x << " <-> AND(" << a << "," << b << ")" << endl;  
// 	  if( config.opt_ee_eagerEquivalence ) setEquivalent(a,x);
// // 	  a = getReplacement( g.a() );
// // 	  x = getReplacement( g.x() );
// 	  data.addEquivalences(x,a);
// 	} 
// 	else if ( x == ~a || x == ~b) {
// 	  if( config.ee_debug_out > 2 ) cerr << "c find an unsatisfiable G-gate based on complementary input to output" << endl; 
// 	  if( enqOut )data.enqueue(~x);
// 	} 

	
	// compare to all other gates of this variable:
	for( int j = i+1 ; j < varTable[v].size(); ++ j ) {
	  Circuit::Gate& other = gates [varTable[v][j]] ;
	  if( other.isInvalid() ) continue;
	  if( other.getType() != Circuit::Gate::AND ) continue;
	  if( config.ee_debug_out > 2 ) cerr << "c with OTHER [" << varTable[v][j] << "," << j << "] ";
	  if( config.ee_debug_out > 2 ) other.print(cerr);
 	  Lit oa = getReplacement( other.a() ); 
 	  Lit ob = getReplacement( other.b() ); 
 	  Lit ox = getReplacement( other.x() ); 
	  if( config.ee_debug_out > 2 ) cerr << "c WHICH is rewritten " << ox << " <-> AND(" << oa << "," << ob << ")" << endl;
	  if( var(ox) == var(oa) || var(ox) == var(ob) || var(oa) == var(ob) ) continue; // such a gate would not be found during analysis ...
	  // assigned value
	  if ( data.value(oa) != l_Undef || data.value(ob) != l_Undef || data.value(ox) != l_Undef) {
	    if( config.ee_debug_out > 2 ) { 
	      cerr << "c gate has assigned inputs" << endl; other.print(cerr); 
	      cerr << "trail: " ;
	      for( int k = 0 ; k < data.getTrail().size(); ++k ) cerr << " " << data.getTrail()[k];
	      cerr << endl;
	    }
	    if ( data.value(oa) == l_True ) {
	      if( config.ee_debug_out > 2 ) cerr << "[   0] add equivalence " << ox << " == " << ob << endl;
	      if( config.opt_ee_eagerEquivalence ) setEquivalent(ob,ox);
	      data.addEquivalences( ox,ob );
// 	      ob = getReplacement( other.b() ); 
// 	      ox = getReplacement( other.x() );
	    } else if ( data.value(oa) == l_False ) {
	      if( config.ee_debug_out > 2 ) cerr << "[   1] enqueue " << ~ox << endl;
	      if( enqOut ) { data.enqueue(~ox);  data.addUnitToProof(~ox); }
	    }
	    if ( data.value(ob) == l_True ) {
	      if( config.ee_debug_out > 2 ) cerr << "[   2] add equivalence " << ox << " == " << oa << endl;
	      if( config.opt_ee_eagerEquivalence ) setEquivalent(oa,ox);
	      data.addEquivalences( ox,oa );
// 	      oa = getReplacement( other.a() ); 
// 	      ox = getReplacement( other.x() );
	    } else if ( data.value(ob) == l_False ) {
	      if( config.ee_debug_out > 2 ) cerr << "[   3] enqueue " << ~ox << endl;
	      if( enqOut ) {data.enqueue(~ox);  data.addUnitToProof(~ox); }
	    } else if ( data.value(ox) == l_True) {
	      if( config.ee_debug_out > 2 ) cerr << "[   4] enqueue " << oa << " and " << ob << endl;
	      if( enqInp ) { data.enqueue(oa);   data.addUnitToProof(oa);}
	      if( enqInp ) { data.enqueue(ob);  data.addUnitToProof(ob);}
	    }
	    // do not reason with assigned gates!
	    continue;
	  }
	  
	  // do some statistics
	  gateSteps ++;
	  
	  /// do simplify gate!
	  if( oa == ob ) {
	    if( config.ee_debug_out > 2 ) cerr << "c found equivalence based on equivalent inputs" << endl;
	    if( config.ee_debug_out > 2 ) cerr << "[   5]" << endl;
	    if( config.opt_ee_eagerEquivalence ) setEquivalent(oa,ox);
	    data.addEquivalences(ox,oa);
// 	    oa = getReplacement( other.a() ); 
// 	    ox = getReplacement( other.x() );
	  } 
// these rules are unsound
	  else if ( oa == ~ob ) { // this rule holds!
	    continue; // this kind of gate should not be used!
	  } 
// 	  else if ( ox == oa ) {
// 	    if( config.ee_debug_out > 2 ) cerr << "[   7]" << endl;
// 	    if( config.opt_ee_eagerEquivalence ) setEquivalent(ob,ox);
// // 	    ob = getReplacement( other.b() ); 
// // 	    ox = getReplacement( other.x() );
// 	    data.addEquivalences(ox,ob);
// 	  } else if ( ox == ob ) {
// 	    if( config.ee_debug_out > 2 ) cerr << "[   8]" << endl;
// 	    if( config.opt_ee_eagerEquivalence ) setEquivalent(oa,ox);
// // 	    oa = getReplacement( other.a() ); 
// // 	    ox = getReplacement( other.x() );
// 	    data.addEquivalences(ox,oa);
// 	  }
	  else if ( ox == ~oa || ox == ~ob) { // this rule holds!
	    continue; // this gate should not be used!
	  } 

	  
	  // handle all equivalence cases!
	  eeLits.clear(); upLits.clear();
	  if ( (oa == a && ob == b) || (oa == b && ob == a ) ) {
	    // usual equivalence of outputs!
	    if( config.ee_debug_out > 2 ) cerr << "[  10]" << endl;
	    eeLits.push_back(x); eeLits.push_back(ox);
	    // both gates are valid -> 
	    if( config.ee_debug_out > 2 ) { cerr << "c invalidate "; other.print(cerr); }
	    other.invalidate();
	    
	  } else if( var(oa) == var(a) || var(oa) == var(b) || var(ob) == var(a) || var(ob) == var(b) ) {
	    // TODO: implement all cases!
	    // extra cases where at least one input matches!
	    if(  (oa == a && ob == x) // x<->AND(a,c) , and c <-> AND(a,x) => c == x !!!
	      || (ob == b && oa == x)
	      || (b == ob && a == ox)
	      || (a == oa && b == ox)
	      ) {
	      if( config.ee_debug_out > 2 ) cerr << "[  11] match one input, and output is another input: " << x << " <-> AND(" << a << "," << b << ")  vs " << ox << " <-> AND(" << oa << "," << ob << ")" << endl;
	      eeLits.push_back(x);eeLits.push_back(ox);
	    } else if ( ox == ~x && 
	      ( (oa == ~a && ob==~b ) || (oa == ~b && ob ==~a) )
	    ) {
	      if( config.ee_debug_out > 2 ) cerr << "[  12]" << endl;
	      // x <-> AND(a,b) and -x <-> AND(-a,-b) => x=a=b!
	      eeLits.push_back(x);eeLits.push_back(a); // every two literals represent an equivalent pair
	      eeLits.push_back(x);eeLits.push_back(b);
	    } 
// 	      else if( (oa == ~a && ob == ~b ) || (oa==~b && ob==~a) ){
// 	      if( x == ox ) { data.enqueue(~ox);  
// 	      } else {
// 		// both gates cannot be active at the same time! -> add a new learned clause!
// 		eeLits.clear();
// 		if( ox < x ) { eeLits.push_back(~ox);eeLits.push_back(~x); }
// 		else { eeLits.push_back(~x);eeLits.push_back(~ox); }
// 		CRef lc = ca.alloc(eeLits, true);
// 		assert ( ca[lc].size() == 2 && "new learned clause has to be binary!" );
// 		data.addClause(lc);
// 		data.getLEarnts().push(lc);
// 		eeLits.clear();
// 		if( config.ee_debug_out > 2 ) cerr << "c add clause " << ca[lc] << endl;
// 		if( isToAnalyze[ var(x) ] == 0 ) { eqDoAnalyze.push_back(x); isToAnalyze[ var(x) ] = 1; }
// 		if( isToAnalyze[ var(ox) ] == 0 ) { eqDoAnalyze.push_back(ox); isToAnalyze[ var(ox) ] = 1; }
// 	      }
// 	    } 
	    else if( (oa == a && ob == ~b) || (oa == b && ob == ~a)  || (oa == ~a && ob == b)  || (oa == ~b && ob == a) ) {
	      // derive a new gate from the given ones!
	      int oldGates = gates.size();
	      if( oa == a ) {
		// constructor expects literals of the ternary representative clause
		if( config.ee_debug_out > 2 ) cerr << "[  13]" << endl;
		if( x == ~ox ) {
		  cerr << "c complementary outputs, one complementary input, other input equal " << ox << " <-> AND(" << ob << "," << oa << ")" << endl;
		  data.addUnitToProof(a);
		  data.enqueue(a); // handle gates where the input would be complementary
		}
		else gates.push_back( Circuit::Gate( ~a, x, ox, Circuit::Gate::AND, Circuit::Gate::FULL) );
	      } else if ( ob == b ) {
		if( config.ee_debug_out > 2 ) cerr << "[  14]" << endl;
		if( x == ~ox ) {
		  cerr << "c complementary outputs, one complementary input, other input equal " << ox << " <-> AND(" << ob << "," << oa << ")" << endl;
		  data.addUnitToProof(b);
		  data.enqueue(b); // handle gates where the input would be complementary
		}
		else gates.push_back( Circuit::Gate( ~b, x, ox, Circuit::Gate::AND, Circuit::Gate::FULL) );
	      } else if ( ob == a ) {
		if( config.ee_debug_out > 2 ) cerr << "[  15]" << endl;
		if( x == ~ox ) {
		  cerr << "c complementary outputs, one complementary input, other input equal " << ox << " <-> AND(" << ob << "," << oa << ")" << endl;
		  data.addUnitToProof(a);
		  data.enqueue(a); // handle gates where the input would be complementary
		}
		else gates.push_back( Circuit::Gate( ~a, x, ox, Circuit::Gate::AND, Circuit::Gate::FULL) );
	      } else if ( oa == b ) {
		if( config.ee_debug_out > 2 ) cerr << "[  16]" << endl;
		if( x == ~ox ) {
		  cerr << "c complementary outputs, one complementary input, other input equal " << ox << " <-> AND(" << ob << "," << oa << ")" << endl;
		  data.addUnitToProof(b);
		  data.enqueue(b); // handle gates where the input would be complementary
		}
		else gates.push_back( Circuit::Gate( ~b, x, ox, Circuit::Gate::AND, Circuit::Gate::FULL) );
	      }
	      if( gates.size() > oldGates ) {
		if( config.ee_debug_out > 2 ) {
		  cerr << "c added new gate";
		  gates[ oldGates ].print(cerr);
		}
		// TODO: what to do with the new gate? for now, put it into the lists of the other variables!
		if( !active.isCurrentStep(var(x)) && !reactivated.isCurrentStep(var(x)) ) { 
		  if( config.ee_debug_out > 2 ) {
		    cerr << "c reactivate varible " << x << " because of gate ";
		    gates[ oldGates ].print(cerr);
		  }
		  currentPtr->push_back( var(x) ); active.setCurrentStep(var(x));
		  reactivated.setCurrentStep(var(x));
		}
		if( !active.isCurrentStep(var(ox)) && !reactivated.isCurrentStep(var(ox)) ) { 
		  if( config.ee_debug_out > 2 ) {
		    cerr << "c reactivate varible " << ox << " because of gate ";
		    gates[ oldGates ].print(cerr);
		  }
		  currentPtr->push_back( var(ox) ); active.setCurrentStep(var(ox));
		  reactivated.setCurrentStep(var(ox));
		}
		// TODO: move to front?
		varTable[ var(x)].push_back( oldGates );
		varTable[var(ox)].push_back( oldGates );
	      }

	    } else if( (x == oa && ob == ~a)
	       || (x == oa && oa == ~b)
	       || (x == ob && oa == ~a)
	       || (x == ob && oa == ~b)
	      
	    ) {
	      if( config.ee_debug_out > 2 ) cerr << "[  17] entail " << ~ox << endl;
	      // the output of a gate together with a complementary input in another gate cannot be satisfied -> other gate is unsat!
	      data.addUnitToProof(~ox);
	      data.enqueue(~ox);
	    }
	    else {
	      if( config.ee_debug_out > 2 ) {
		if( var(x) == var(ox) ||
		  ( (var(a) == var(oa) && var(b) == var(ob)) || (var(b) == var(oa) && var(a) == var(ob)) )
		|| ( var(x) == var(oa) && (var(a) == var(ob) || var(b) == var(ob) ) )
		|| ( var(x) == var(ob) && (var(a) == var(oa) || var(b) == var(oa) ) ) ) {
		  cerr << "c UNHANDLED CASE with two gates:" << endl;
		  cerr << x << " <-> AND(" << a << ", " << b << ")" << endl
		      << ox << " <-> AND(" << oa << ", " << ob << ")" << endl;
		}
	      }
	    }
	  }
	  
	  
	    while ( eeLits.size() >= 2 ) {
	      const Lit x = eeLits[eeLits.size()-1]; const Lit ox = eeLits[eeLits.size()-2];
	      eeLits.pop_back();eeLits.pop_back();
	      if( var(x) != var(ox) ) {
		if( config.opt_ee_eagerEquivalence ) setEquivalent(x,ox);
		data.addEquivalences(x,ox);
		// put smaller variable in queue, if not already present
		Var minV = var(x) < var(ox) ? var(x) : var(ox);
		Var maxV = (minV ^ var(x) ^ var(ox));
		if( config.ee_debug_out > 2 ) cerr << "c equi: " << x << " == " << ox << " min=" << minV+1 << " max=" << maxV+1 << endl;
		if( !putAllAlways && ! active.isCurrentStep(minV) ) {
		  active.setCurrentStep(minV);
		  currentPtr->push_back(minV);
		  if( config.ee_debug_out > 2 ) cerr << "c re-activate output variable " << minV + 1 << endl;
		}
		// moves gates from greater to smaller!
		for( int k = 0 ; k < varTable[maxV].size(); ++k )
		  varTable[minV].push_back( varTable[maxV][k] );
		varTable[maxV].clear();
	      } else {
		if( x == ~ox ) {
		  data.setFailed();
		  data.addCommentToProof("structural hashing found that a variable has to be equivalent to its complement");
		  data.addUnitToProof(x);
		  data.addUnitToProof(ox);
		  cerr << "c failed, because AND miter procedure found that " << x << " is equivalent to " << ox << endl;
		  gateTime  = cpuTime() - gateTime;
		  return true;
		} else {
		  if( config.ee_debug_out > 2 ) cerr << "c found equivalence " << x << " == " << ox << " again" << endl;
		}
	      }
	    }
	  
	}
	
      }
  }
  
  if( config.ee_debug_out > 2 ) cerr << "c OLD equis: " << oldEquivalences << "  current equis: " << data.getEquivalences().size() << " hasToPropagate" << data.hasToPropagate() << endl;
  gateTime  = cpuTime() - gateTime;
  return (data.getEquivalences().size() - oldEquivalences > 0) || data.hasToPropagate();
}

bool EquivalenceElimination::findGateEquivalences(Coprocessor::CoprocessorData& data, vector< Circuit::Gate > gates)
{
  MethodTimer mt(&gateTime);
  int oldEquivalences = data.getEquivalences().size();
  
  cerr << "c this algorithm is not final yet, and might produce incorrect results" << endl;
  return false; // do not execute this algorithm!
  
  /** a variable in a circuit can participate in non-clustered gates only, or also participated in clustered gates */
  vector< vector<int32_t> > varTable ( data.nVars() ); // store for each variable which gates have this variable as input
  // store for each variable, whether this variable has a real output (bit 1=output, bit 2=clustered, bit 3 = stamped)
  vector< unsigned int > bitType ( data.nVars(), 0 ); // upper 4 bits are a counter to count how often this variable has been considered already as output
  
  for( int i = 0 ; i < gates.size() ; ++ i ) {
   const Circuit::Gate& g = gates[i];
   switch( g.getType() ) {
     case Circuit::Gate::AND:
       bitType[ var(g.x()) ] = bitType[ var(g.x()) ] | 1; // set output bit
       varTable[ var(g.a()) ].push_back(i);
       varTable[ var(g.b()) ].push_back(i);
       break;
     case Circuit::Gate::ExO:
       for( int j = 0 ; j<g.size() ; ++ j ) {
	 const Var v = var( g.get(j) );
         bitType[v] = bitType[v] | 2; // set clustered bit
         varTable[v]. push_back(i);
       }
       break;
     case Circuit::Gate::GenAND:
       bitType[ var(g.getOutput()) ] = bitType[ var(g.getOutput()) ] | 1; // set output bit
       for( int j = 0 ; j<g.size() ; ++ j ) {
	 const Var v = var( g.get(j) );
         varTable[v]. push_back(i);
       }
       break;
     case Circuit::Gate::ITE:
       bitType[ var(g.x()) ] = bitType[ var(g.x()) ] | 1; // set output bit
       varTable[ var(g.s()) ].push_back(i);
       varTable[ var(g.t()) ].push_back(i);
       varTable[ var(g.f()) ].push_back(i);
       break;
     case Circuit::Gate::XOR:
       bitType[ var( g.a()) ] = bitType[ var( g.a()) ] | 2 ; // set clustered bit!
       bitType[ var( g.b()) ] = bitType[ var( g.b()) ] | 2 ; // set clustered bit!
       bitType[ var( g.c()) ] = bitType[ var( g.c()) ] | 2 ; // set clustered bit!
       varTable[var( g.a())]. push_back(i);
       varTable[var( g.b())]. push_back(i);
       varTable[var( g.c())]. push_back(i);
       break;
     case Circuit::Gate::FA_SUM:
       bitType[ var( g.a()) ] = bitType[ var( g.a()) ] | 2 ; // set clustered bit!
       bitType[ var( g.b()) ] = bitType[ var( g.b()) ] | 2 ; // set clustered bit!
       bitType[ var( g.c()) ] = bitType[ var( g.c()) ] | 2 ; // set clustered bit!
       bitType[ var( g.x()) ] = bitType[ var( g.x()) ] | 2 ; // set clustered bit!
       varTable[var( g.a())]. push_back(i);
       varTable[var( g.b())]. push_back(i);
       varTable[var( g.c())]. push_back(i);
       varTable[var( g.x())]. push_back(i);
       break;
     case Circuit::Gate::INVALID:
       break;
     default:
       assert( false && "This gate type cannot be handled (yet)" );
   }
  }
  
  // TODO: remove clustered gates, if they appear for multiple variables!
  /*
  cerr << "c ===== START SCANNING ======= " << endl;
  for( Var v = 0 ; v < data.nVars(); ++ v ) {
     cerr << "c var " << v+1 << " role: " << "("<< (int)bitType[v] << ")" << endl;
  }
  */
  
  vector< Var > inputVariables;
  deque< int > queue;
  // collect pure input variables!
  for( Var v = 0 ; v < data.nVars(); ++ v ) {
    if( 0 == bitType[v] ) {
      if( varTable[v].size() == 0 ) continue; // use only if it helps enqueuing gates!
      //cerr << "c use for initial scanning: " << v+1 << " with " << ((int)bitType[v]) << endl; 
      inputVariables.push_back(v);
      bitType[v] = (bitType[v] | 4); // stamp
      // todo: stamp variable?!
    }
  }
  for( Var v = 0 ; v < data.nVars(); ++ v ) {
    if( (bitType[v] & 5) == 0  ) { // not yet stamped, and no output
      inputVariables.push_back(v);
      if( varTable[v].size() == 0 ) continue; // use only if it helps enqueuing gates!
      //cerr << "c use for initial clustered scanning: " << v+1 << " with " << ((int)bitType[v]) << endl; 
      bitType[v] = (bitType[v] | 4); // stamp
      // todo: stamp variable?!
    }
  }
  
  // fill queue to work with
  for( int i = 0 ; i < inputVariables.size(); ++ i ) {
    const Var v = inputVariables[i];
    for( int j = 0 ; j < varTable[v].size(); ++ j ) {
      Circuit::Gate& g = gates[ varTable[v][j] ]; 
      if( !g.isInQueue() ) 
        { queue.push_back( varTable[v][j] ); 
          g.putInQueue();
	  //cerr << "c put gate into queue: ";
	  // g.print(cerr); // do not print gate by default!
	  // mark all inputs for clustered gates!
	  if( g.getType() == Circuit::Gate::XOR ) {
	    bitType[var(g.a())] = (bitType[var(g.a())] | 4); // stamp
	    bitType[var(g.b())] = (bitType[var(g.b())] | 4); // stamp
	    bitType[var(g.c())] = (bitType[var(g.c())] | 4); // stamp
	  } else if( g.getType() == Circuit::Gate::ExO ) {
	    for( int j = 0 ; j < g.size(); ++ j ) {
	      bitType[var(g.get(j))] = (bitType[var(g.get(j))] | 4); // stamp
	    }
	  } else if( g.getType() == Circuit::Gate::FA_SUM ){
	    bitType[var(g.a())] = (bitType[var(g.a())] | 4); // stamp
	    bitType[var(g.b())] = (bitType[var(g.b())] | 4); // stamp
	    bitType[var(g.c())] = (bitType[var(g.c())] | 4); // stamp
	    bitType[var(g.x())] = (bitType[var(g.x())] | 4); // stamp
	  }
	}
    }
  }
  
  if( queue.empty() && gates.size() > 0 ) {
    // not pure inputs available, start with all clustered gates!
    for( int i = 0 ; i < gates.size(); ++ i ) {
      Circuit::Gate& g = gates[ i ]; 
      if(  g.getType() == Circuit::Gate::XOR || g.getType() == Circuit::Gate::ExO || g.getType() == Circuit::Gate::FA_SUM ) 
        { queue.push_back( i ); 
          g.putInQueue();
	  //cerr << "c put gate into queue: ";
	  // g.print(cerr);
	  if( g.getType() == Circuit::Gate::XOR ) {
	    bitType[var(g.a())] = (bitType[var(g.a())] | 4); // stamp
	    bitType[var(g.b())] = (bitType[var(g.b())] | 4); // stamp
	    bitType[var(g.c())] = (bitType[var(g.c())] | 4); // stamp
	  } else if( g.getType() == Circuit::Gate::ExO ) {
	    for( int j = 0 ; j < g.size(); ++ j ) {
	      bitType[var(g.get(j))] = (bitType[var(g.get(j))] | 4); // stamp
	    }
	  } else {
	    bitType[var(g.a())] = (bitType[var(g.a())] | 4); // stamp
	    bitType[var(g.b())] = (bitType[var(g.b())] | 4); // stamp
	    bitType[var(g.c())] = (bitType[var(g.c())] | 4); // stamp
	    bitType[var(g.x())] = (bitType[var(g.x())] | 4); // stamp
	  }
	}
    }
  }
  
  // if there are no clustered gates, there is something different wrong -> add all gates, stamp all variables!
  if( queue.empty() && gates.size() > 0 ) {
    // not pure inputs available, start with all clustered gates!
    for( int i = 0 ; i < gates.size(); ++ i ) {
      Circuit::Gate& g = gates[ i ]; 
      queue.push_back( i ); 
          g.putInQueue();
	  //cerr << "c put gate into queue: ";
	  // g.print(cerr);
    }
    for( Var v = 0 ; v < data.nVars(); ++ v ) {
	bitType[v] = (bitType[v] | 4); // stamp
    }
  }
  
  if( queue.empty() ) cerr << "c there are no gates to start from, with " << gates.size() << " initial gates!" << endl;
  assert ( (gates.size() == 0 || queue.size() > 0) && "there has to be at least one gate to start from!" ); 
  while( !queue.empty() && data.ok() ) {
    const int gateIndex = queue.front();
    Circuit::Gate& g = gates[ queue.front() ];
    queue.pop_front();
    // check number of being touched, do not process a gate too often!
    if( g.touch() > 16 ) {
      //cerr << "c looked at the gate 16 times: ";
      // g.print(cerr);
      continue; // do not look at the gate too often!
    }
     
    // check whether we are allowed to work on this gate already
    if( allInputsStamped( g, bitType ) ) {
      // calculate equivalences based on gate type, stamp output variable and enqueue successor gates
      processGate( data, g, gates, queue, bitType, varTable );
      // enqueueSucessorGates(g,queue,gates,bitType,varTable);
    } else {
      //cerr << "c not all inputs are available for "; g.print(cerr );
       queue.push_back(gateIndex);
    }
  }
  
  // just in case some unit has been found, we have to propagate it!
  if( data.hasToPropagate() ) {
    propagation.process(data,true);
    modifiedFormula = modifiedFormula || propagation.appliedSomething(); 
  }
  
  return oldEquivalences < data.getEquivalences().size();
}

bool EquivalenceElimination::allInputsStamped(Circuit::Gate& g, std::vector< unsigned int >& bitType)
{
   int count = 0;
   switch( g.getType() ) {
     case Circuit::Gate::AND:
       return (bitType[ var(g.a()) ] & 4) != 0 && (bitType[ var(g.b()) ] & 4) != 0 ;
       break;
     case Circuit::Gate::ExO:
       for( int j = 0 ; j<g.size() ; ++ j ) {
	 const Var v = var( g.get(j) );
	 // one bit must not be stamped!
         if( (bitType[ v ] & 4) == 0 ) 
	   if ( count != 0 ) return false; else count++;
       }
       //cerr << "c all inputs of ExO are stamped: "; g.print(cerr);
       return true;
     case Circuit::Gate::GenAND:
       for( int j = 0 ; j<g.size() ; ++ j ) {
	 const Var v = var( g.get(j) );
	 if( (bitType[ v ] & 4) == 0 ) return false;
       }
       return true;
     case Circuit::Gate::ITE:
       if(  (bitType[ var(g.s()) ] & 4) == 0  
	 || (bitType[ var(g.t()) ] & 4) == 0  
	 || (bitType[ var(g.f()) ] & 4) == 0 ) return false;
       return true;
     case Circuit::Gate::XOR:
	if((bitType[ var(g.a()) ] & 4) == 0 ) count ++;
	if((bitType[ var(g.b()) ] & 4) == 0 ) count ++;  
	if((bitType[ var(g.c()) ] & 4) == 0 ) count ++;
	if( count > 1 ) return false;
       return true;
     case Circuit::Gate::FA_SUM:
	if((bitType[ var(g.a()) ] & 4) == 0 ) count ++;
	if((bitType[ var(g.b()) ] & 4) == 0 ) count ++;  
	if((bitType[ var(g.c()) ] & 4) == 0 ) count ++;
	if((bitType[ var(g.x()) ] & 4) == 0 ) count ++;
	if( count > 1 ) return false;
       return true;
     case Circuit::Gate::INVALID:
       return false;
     default:
       assert( false && "This gate type cannot be handled (yet)" );
       return false;
   }
   return false;
}

bool EquivalenceElimination::checkEquivalence(const Circuit::Gate& g1, const Circuit::Gate& g2, Lit& e1, Lit& e2)
{
  return false;
}

void EquivalenceElimination::enqueueSucessorGates( Circuit::Gate& g, std::deque< int > queue, std::vector<Circuit::Gate>& gates, std::vector< unsigned int >& bitType, vector< vector<int32_t> >& varTable)
{
switch( g.getType() ) {
     case Circuit::Gate::AND:
       {const Var v = var( g.x() );
        bitType[v] = bitType[v] | 4; // stamp output bit!
	// enqueue gates, if not already inside the queue:
	for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	  if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	    gates[ varTable[ v ][i] ].putInQueue();
	    queue.push_back( varTable[ v ][i] );
	  }
	}
       break;}
     case Circuit::Gate::ExO:
       for( int j = 0 ; j<g.size() ; ++ j ) {
	const Var v = var( g.get(j) );
        bitType[v] = bitType[v] | 4; // stamp output bit!
	// enqueue gates, if not already inside the queue:
	for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	  if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	    gates[ varTable[ v ][i] ].putInQueue();
	    queue.push_back( varTable[ v ][i] );
	  }
	}
       }
       break;
     case Circuit::Gate::GenAND:
     {
	const Var v = var( g.getOutput() );
        bitType[v] = bitType[v] | 4; // stamp output bit!
	// enqueue gates, if not already inside the queue:
	for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	  if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	    gates[ varTable[ v ][i] ].putInQueue();
	    queue.push_back( varTable[ v ][i] );
	  }
	}
       break;}
     case Circuit::Gate::ITE:
     {const Var v = var( g.x() );
        bitType[v] = bitType[v] | 4; // stamp output bit!
	// enqueue gates, if not already inside the queue:
	for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	  if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	    gates[ varTable[ v ][i] ].putInQueue();
	    queue.push_back( varTable[ v ][i] );
	  }
	}
       break;}
     case Circuit::Gate::XOR:
     {for ( int i = 0 ; i < 3; ++ i ) {
	 const Var v = ((i==0) ? var(g.a()) : ((i==1) ? var(g.b()) : var(g.c()) )  );
	  bitType[v] = bitType[v] | 4; // stamp output bit!
	  // enqueue gates, if not already inside the queue:
	  for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	    if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	      gates[ varTable[ v ][i] ].putInQueue();
	      queue.push_back( varTable[ v ][i] );
	    }
	  }
       }
       break;}
     case Circuit::Gate::FA_SUM:
       assert( false && "This gate type has not been implemented (yet)" );
       break;
     case Circuit::Gate::INVALID:
       break;
     default:
       assert( false && "This gate type cannot be handled (yet)" );
   }
}

void EquivalenceElimination::processGate(CoprocessorData& data, Circuit::Gate& g, vector< Circuit::Gate >& gates, std::deque< int >& queue, std::vector< unsigned int >& bitType, vector< vector<int32_t> >& varTable)
{
  switch( g.getType() ) {
     case Circuit::Gate::AND:
       return processANDgate(data,g,gates,queue,bitType,varTable);
     case Circuit::Gate::ExO:
       return processExOgate(data,g,gates,queue,bitType,varTable);
     case Circuit::Gate::GenAND:
       return processGenANDgate(data,g,gates,queue,bitType,varTable);
     case Circuit::Gate::ITE:
       return processITEgate(data,g,gates,queue,bitType,varTable);
     case Circuit::Gate::XOR:
       return processXORgate(data,g,gates,queue,bitType,varTable);
     case Circuit::Gate::FA_SUM:
       return processFASUMgate(data,g,gates,queue,bitType,varTable);
       break;
     case Circuit::Gate::INVALID:
       break;
     default:
       assert( false && "This gate type cannot be handled (yet)" );
   }
}

void EquivalenceElimination::processANDgate(CoprocessorData& data, Circuit::Gate& g, vector< Circuit::Gate >& gates, std::deque< int >& queue, std::vector< unsigned int >& bitType, vector< vector< int32_t > >& varTable, MarkArray* active, std::deque< Var >* activeVariables)
{
  // cerr << "c compare " << queue.size() << " gates against current AND gate ";
//   g.print(cerr);
  
  // TODO: x<->AND(a,c) , and c <-> AND(a,x) => c == x !!!
  
  Lit a = getReplacement( g.a() ); 
  Lit b = getReplacement( g.b() ); 
  Lit x = getReplacement( g.x() ); 
  
  for( int i = 0 ; i < queue.size(); ++ i ) {
    const Circuit::Gate& other = gates [queue[i]] ;
    if( other.getType() != Circuit::Gate::AND ) continue;

    Lit oa = getReplacement( other.a() ); 
    if( oa != a && oa != b ) continue; // does not match another input!
    Lit ob = getReplacement( other.b() ); 
    if( (oa == b && ob != a) || ( oa == a && ob != b ) ) continue; // does not match another input!
    Lit ox = getReplacement( other.x() ); 
    
//     cerr << "c gates are equivalent: " << endl;
//     g.print(cerr);
//     other.print(cerr);
    
    if( var(x) != var(ox) ) {
      setEquivalent(x,ox);
      data.addEquivalences(x,ox);
      //cerr << "c equi: " << x << " == " << ox << endl;
      // old or new method?
      if( active ==0 && activeVariables == 0 ) {
	// new equivalent gate -> enqueue successors!
	const Var v = var( other.x() );
	bitType[v] = bitType[v] | 4; // stamp output bit!
	// enqueue gates, if not already inside the queue:
	for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	  if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	    gates[ varTable[ v ][i] ].putInQueue();
	    queue.push_back( varTable[ v ][i] );
	  }
	}
      } else {
	if( !active->isCurrentStep(   var(x)) ) {
	  active->setCurrentStep(     var(x)); 
	  activeVariables->push_back( var(x));
	}
	if( !active->isCurrentStep(   var(ox)) ) {
	  active->setCurrentStep(     var(ox)); 
	  activeVariables->push_back( var(ox) );
	}
      }
      
    } else {
      if( x == ~ox ) {
	data.setFailed();
	data.addCommentToProof("structural hashing found that a variable has to be equivalent to its complement");
	data.addUnitToProof(x);
	data.addUnitToProof(ox);
	//cerr << "c failed, because AND procedure found that " << x << " is equivalent to " << ox << endl;
      } else {
// 	cerr << "c found equivalence " << x << " == " << ox << " again" << endl;
      }
    }
    
  }
  
  if( active == 0 && activeVariables == 0 ) {
    // new equivalent gate -> enqueue successors!
    const Var v = var( g.x() );
    bitType[v] = bitType[v] | 4; // stamp output bit!
    // enqueue gates, if not already inside the queue:
    for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
      if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	gates[ varTable[ v ][i] ].putInQueue();
	queue.push_back( varTable[ v ][i] );
      }
    }
  }
}

void EquivalenceElimination::processExOgate(CoprocessorData& data, Circuit::Gate& g, vector< Circuit::Gate >& gates, std::deque< int >& queue, std::vector< unsigned int >& bitType, vector< vector< int32_t > >& varTable, MarkArray* active, std::deque< Var >* activeVariables)
{
//   cerr << "c compare " << queue.size() << " gates against current ExO gate ";
//   g.print(cerr);
  
  Lit lits[g.size()];
  for( int i = 0 ; i < g.size(); ++ i )
    lits[i] = getReplacement(g.get(i));
  
  for( int i = 0 ; i < queue.size(); ++ i ) {
    const Circuit::Gate& other = gates [queue[i]] ;
    if( other.getType() != Circuit::Gate::ExO ) continue;
    if( other.size() != g.size() ) continue; // cannot say anything about different sizes

//     cerr << "c compare two ExOs of size " << other.size() << " : "; other.print(cerr);

    // hit each input:
    int hit = 0;
    Lit freeLit = lit_Undef;
    for( int j = 0 ; j < other.size(); ++ j ) {
      const Lit r = getReplacement(other.get(j));
//       cerr << "c find lit " << r << " (hit already: " << hit << ")" << endl;
      for( int k = hit; k < other.size(); ++ k ) {
	if( r == lits[k] ) { lits[k] = lits[hit] ; lits[hit] = r; ++ hit; break; }
      }
//       if( hit > 0 ) cerr << "c hit after search: " << hit << " hit lit= " << lits[hit-1] << endl;
      if( hit < j ) break;
      else if( hit == j && freeLit == lit_Undef) freeLit = other.get(j);
    }
    if( hit + 1 < other.size() ) continue; // not all inputs match!
//     cerr << "c final hit: " << hit << " corr. lit: " << lits[hit] << endl;

    if( var( lits[ g.size() -1 ] ) != var( freeLit ) ) {
	setEquivalent(lits[ g.size() -1 ],freeLit);
	data.addEquivalences(lits[ g.size() -1 ],freeLit);
	//cerr << "c equi: " << lits[ g.size() -1 ] << " == " << freeLit << endl;
	
	if( active == 0 && activeVariables == 0 ) {
	// new equivalent gate -> enqueue successors!
	for( int j = 0 ; j < other.size(); ++ j ) {
	  const Var v = var( other.get(j) );
	  bitType[v] = bitType[v] | 4; // stamp output bit!
	  // enqueue gates, if not already inside the queue:
	  for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	    if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	      gates[ varTable[ v ][i] ].putInQueue();
	      queue.push_back( varTable[ v ][i] );
	    }
	  }
	}
	
      } else {
	if( !active->isCurrentStep(   var(lits[ g.size() -1 ])) ) {
	  active->setCurrentStep(     var(lits[ g.size() -1 ])); 
	  activeVariables->push_back( var(lits[ g.size() -1 ]));
	}
	if( !active->isCurrentStep(   var(freeLit)) ) {
	  active->setCurrentStep(     var(freeLit)); 
	  activeVariables->push_back( var(freeLit) );
	}
      }
	
	
      } else {
	if( lits[ g.size() -1 ] == ~freeLit ) {
	  data.setFailed();
	  data.addCommentToProof("structural hashing found that a variable has to be equivalent to its complement");
	  data.addUnitToProof(lits[ g.size() -1 ]);
	  data.addUnitToProof(freeLit);
	  //cerr << "c failed, because ExO procedure found that " << lits[ g.size() -1 ] << " is equivalent to " << freeLit << endl;
// 	  cerr << "c corresponding gates: " << endl;
// 	  g.print(cerr);
// 	  other.print(cerr);
	  return;
	} else {
// 	  cerr << "c found equivalence " << lits[ g.size() -1 ] << " == " << freeLit << " again" << endl;
	}
      }
  }
  
  if( active == 0 && activeVariables == 0 ) {
    // new equivalent gate -> enqueue successors!
    for( int j = 0 ; j < g.size(); ++ j ) {
	  const Var v = var( g.get(j) );
	  bitType[v] = bitType[v] | 4; // stamp output bit!
	  // enqueue gates, if not already inside the queue:
	  for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	    if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	      gates[ varTable[ v ][i] ].putInQueue();
	      queue.push_back( varTable[ v ][i] );
	    }
	  }
    }
  }
}

void EquivalenceElimination::processGenANDgate(CoprocessorData& data, Circuit::Gate& g, vector< Circuit::Gate >& gates, std::deque< int >& queue, std::vector< unsigned int >& bitType, vector< vector< int32_t > >& varTable, MarkArray* active, std::deque< Var >* activeVariables)
{
//   cerr << "c compare " << queue.size() << " gates against current GenAND gate ";
//   g.print(cerr);
  
  Lit lits[g.size()];
  for( int i = 0 ; i < g.size(); ++ i )
    lits[i] = getReplacement(g.get(i));
  
  for( int i = 0 ; i < queue.size(); ++ i ) {
    const Circuit::Gate& other = gates [queue[i]] ;
    if( other.getType() != Circuit::Gate::GenAND ) continue;
    if( other.size() != g.size() ) continue; // cannot say anything about different sizes

    // hit each input:
    int hit = 0;
    for( int j = 0 ; j < other.size(); ++ j ) {
      const Lit r = getReplacement(other.get(j));
      for( int k = hit; k < other.size(); ++ k ) {
	if( r == lits[hit] ) { lits[hit] = lits[k]; lits[k] = r; ++ hit; break; }
      }
      if( hit != j+1 ) break;
    }
    if( hit != other.size() ) continue; // not all inputs match!

    if( var( g.getOutput() ) != var( other.getOutput() ) ) {
	setEquivalent(g.getOutput(),other.getOutput());
	data.addEquivalences(g.getOutput(),other.getOutput());
	//cerr << "c equi: " << g.getOutput() << " == " << other.getOutput() << endl;
      if( active == 0 && activeVariables == 0 ) {
	// new equivalent gate -> enqueue successors!
	  const Var v = var( other.getOutput() );
	  bitType[v] = bitType[v] | 4; // stamp output bit!
	  // enqueue gates, if not already inside the queue:
	  for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	    if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	      gates[ varTable[ v ][i] ].putInQueue();
	      queue.push_back( varTable[ v ][i] );
	    }
	  }
      } else {
	if( !active->isCurrentStep(   var(g.getOutput())) ) {
	  active->setCurrentStep(     var(g.getOutput()) ); 
	  activeVariables->push_back( var(g.getOutput()) );
	}
	if( !active->isCurrentStep(   var(other.getOutput())) ) {
	  active->setCurrentStep(     var(other.getOutput()) ); 
	  activeVariables->push_back( var(other.getOutput()) );
	}
      }
	
	
      } else {
	if( g.getOutput() == ~other.getOutput() ) {
	  
	  data.setFailed();
	  data.addCommentToProof("structural hashing found that a variable has to be equivalent to its complement");
	  data.addUnitToProof(g.getOutput());
	  data.addUnitToProof(other.getOutput());
	  //cerr << "c failed, because GenAND procedure found that " << g.getOutput() << " is equivalent to " << other.getOutput() << endl;
// 	  cerr << "c corresponding gates: " << endl;
// 	  g.print(cerr);
// 	  other.print(cerr);
	  return;
	} else {
// 	  cerr << "c found equivalence " << g.getOutput() << " == " << other.getOutput() << " again" << endl;
	}
      }
  }
  
  if( active == 0 && activeVariables == 0 ) {
// new equivalent gate -> enqueue successors!
	  const Var v = var( g.getOutput() );
	  bitType[v] = bitType[v] | 4; // stamp output bit!
	  // enqueue gates, if not already inside the queue:
	  for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	    if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	      gates[ varTable[ v ][i] ].putInQueue();
	      queue.push_back( varTable[ v ][i] );
	    }
	  }
  }

}

void EquivalenceElimination::processITEgate(CoprocessorData& data, Circuit::Gate& g, vector< Circuit::Gate >& gates, std::deque< int >& queue, std::vector< unsigned int >& bitType, vector< vector< int32_t > >& varTable, MarkArray* active, std::deque< Var >* activeVariables)
{
//   cerr << "c compare " << queue.size() << " gates against current ITE gate ";
//   g.print(cerr);
  
  const Lit s = getReplacement( g.s() ); 
  const Lit t = getReplacement( g.t() ); 
  const Lit f = getReplacement( g.f() ); 
  const Lit x = getReplacement( g.x() ); 
  
  for( int i = 0 ; i < queue.size(); ++ i ) {
    const Circuit::Gate& other = gates [queue[i]] ;
    if( other.getType() != Circuit::Gate::ITE ) continue;

    const Lit os = getReplacement( other.s() ); 
    if( var(s) != var(os) ) continue; // the selector variable has to be the same!!
    const Lit ot = getReplacement( other.t() ); 
    if( var(t) != var(ot) && var(ot) != var(f) ) continue; // has to match one of the inputs!
    const Lit of = getReplacement( other.f() ); 
    if(  (var(t) == var(ot) && var(of) != var(f) )
      || (var(f) == var(ot) && var(of) != var(t) )) continue; // inputs have to match inputs!
    Lit ox = getReplacement( other.x() ); 
    if( x == ox ) continue; // can only define output, but no other bits of the gates!
    // equivalence could be either positive or negative
    enum Match {
      POS,
      NONE,
      NEG
    };
    Match match = NONE;
    if( s == os ) {
      if( t == ot && f == of ) match = POS;
      else if ( t == ~ot && f == ~of ) match = NEG;
    } else {
      if( f == ot && t == of ) match = POS;
      else if ( t == ~of && f == ~ot ) match = NEG;
    }
    if( match == NONE ) continue;
    else if( match == NEG ) ox = ~ox;
   
    if( var(x) != var(ox) ) {
      setEquivalent(x,ox);
      data.addEquivalences(x,ox);
      //cerr << "c equi: " << x << " == " << ox << endl;
      
      if( active == 0 && activeVariables == 0 ) {
	// new equivalent gate -> enqueue successors!
	const Var v = var( other.x() );
	bitType[v] = bitType[v] | 4; // stamp output bit!
	// enqueue gates, if not already inside the queue:
	for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	  if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	    gates[ varTable[ v ][i] ].putInQueue();
	    queue.push_back( varTable[ v ][i] );
	  }
	}
      } else {
	if( !active->isCurrentStep(   var(x)) ) {
	  active->setCurrentStep(     var(x) ); 
	  activeVariables->push_back( var(x) );
	}
	if( !active->isCurrentStep(   var(ox)) ) {
	  active->setCurrentStep(     var(ox) ); 
	  activeVariables->push_back( var(ox) );
	}
      }
      
    } else {
      if( x == ~ox ) {
	data.setFailed();
	data.addCommentToProof("structural hashing found that a variable has to be equivalent to its complement");
	data.addUnitToProof(x);
	data.addUnitToProof(ox);
	//cerr << "c failed, because ITE procedure found that " << x << " is equivalent to " << ox << endl;
//	cerr << "c equi gate 1: " << x  << " = ITE(" << s  << "," << t  << "," << f  << ")" << endl;
// 	cerr << "c equi gate 2: " << ox << " = ITE(" << os << "," << ot << "," << of << ")" << endl;
      } else {
// 	cerr << "c found equivalence " << x << " == " << ox << " again" << endl;
      }
    }
    
  }
  
  if( active == 0 && activeVariables == 0 ) {
    // this gate has been processed!
    const Var v = var( x );
    bitType[v] = bitType[v] | 4; // stamp output bit!
    // enqueue gates, if not already inside the queue:
    for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
      if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	gates[ varTable[ v ][i] ].putInQueue();
	queue.push_back( varTable[ v ][i] );
      }
    }
  }
}

void EquivalenceElimination::processXORgate(CoprocessorData& data, Circuit::Gate& g, vector< Circuit::Gate >& gates, std::deque< int >& queue, std::vector< unsigned int >& bitType, vector< vector< int32_t > >& varTable, MarkArray* active, std::deque< Var >* activeVariables)
{
//   cerr << "c compare " << queue.size() << " gates against current XOR gate ";
//   g.print(cerr);
  
  Lit lits[3];
  lits[0] = getReplacement( g.a() ); 
  lits[1] = getReplacement( g.b() ); 
  lits[2] = getReplacement( g.c() ); 
  bool pol = sign(lits[0]) ^ sign(lits[1]) ^ sign(lits[2]);
  
  for( int i = 0 ; i < queue.size(); ++ i ) {
    const Circuit::Gate& other = gates [queue[i]] ;
    if( other.getType() != Circuit::Gate::XOR  // xor is either equivalent to another xor
      && other.getType() != Circuit::Gate::FA_SUM ) continue; // or subsumes equivalent FA_SUM

//     cerr << "c other gate: "; other.print(cerr);
    
    if( other.getType() == Circuit::Gate::XOR ) {
      int hit = 0;
      Lit freeLit = lit_Undef;
      const Lit oa = getReplacement( other.a() ); 
      for( int j = 0; j < 3; ++ j ) {
	if( var(lits[j]) == var(oa) ) { const Lit tmp = lits[0]; lits[0] = lits[j]; lits[j] = tmp; hit++; break; } 
      }
      if( hit == 0 ) freeLit = oa;
//       if( freeLit != lit_Undef ) cerr << "c freelit = " << freeLit << endl;
      const Lit ob = getReplacement( other.b() ); 
      for( int j = hit; j < 3; ++ j ) {
	if( var(lits[j]) == var(ob) ) { const Lit tmp = lits[hit]; lits[hit] = lits[j]; lits[j] = tmp; hit++; break; } 
      }
      if( hit < 2 )  // check for the free literal
	if( hit == 0 ) { /*cerr << "failed with one of literal " << oa << " ," << ob << endl;*/ continue; } // this xor gate does not match 2 variables!
	else if( freeLit == lit_Undef ) freeLit = ob ; // this literal is the literal that does not match!

//       if( freeLit != lit_Undef ) cerr << "c freelit = " << freeLit << endl;
      const Lit oc = getReplacement( other.c() ); 
      for( int j = hit; j < 3; ++ j ) {
	if( var(lits[j]) == var(oc) ) { const Lit tmp = lits[hit]; lits[hit] = lits[j]; lits[j] = tmp; hit++; break; } 
      }
      if( hit < 3 )  // check for the free literal
	if( hit < 2 ) {/*cerr << "failed with one of literal " << oa << " ," << ob << ", " << oc << endl; */continue; } // this xor gate does not match 2 variables!
      // might be the case that all variables match!
      if( freeLit == lit_Undef ) freeLit = oc ; // this literal is the literal that does not match!

//       if( freeLit != lit_Undef ) cerr << "c freelit = " << freeLit << endl;
      // get right polarity!
//       cerr << "c pol= " << pol << " new pol= " << (int)(sign(oa) ^ sign(ob) ^ sign(oc) ^ sign(freeLit) ) << endl;
      if( (pol ^ sign(lits[2] ) ) != (sign(oa) ^ sign(ob) ^ sign(oc) ^ sign(freeLit) ) ) freeLit = ~freeLit;
      
      if( var(lits[2]) != var(freeLit) ) {
	setEquivalent(lits[2],freeLit);
	data.addEquivalences(lits[2],freeLit);
	//cerr << "c equi: " << lits[2] << " == " << freeLit << endl;
	
      if (active==0 && activeVariables==0) {
	// new equivalent gate -> enqueue successors!
	for( int j = 0 ; j < 3; ++ j ) { // enqueue all literals!
	  const Var v = var( j == 0 ? other.a() : ((j == 1 ) ? other.b() : other.c() ));
	  bitType[v] = bitType[v] | 4; // stamp output bit!
	  // enqueue gates, if not already inside the queue:
	  for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	    if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	      gates[ varTable[ v ][i] ].putInQueue();
	      queue.push_back( varTable[ v ][i] );
	    }
	  }
	}
      } else {
	if( !active->isCurrentStep(   var(lits[2])) ) {
	  active->setCurrentStep(     var(lits[2]) ); 
	  activeVariables->push_back( var(lits[2]) );
	}
	if( !active->isCurrentStep(   var(freeLit)) ) {
	  active->setCurrentStep(     var(freeLit) ); 
	  activeVariables->push_back( var(freeLit) );
	}
      }
	
      } else {
	if( lits[2] == ~freeLit ) {
	  data.setFailed();
	  data.addCommentToProof("structural hashing found that a variable has to be equivalent to its complement");
	  data.addUnitToProof(lits[2]);
	  data.addUnitToProof(freeLit);
	  //cerr << "c failed, because XOR procedure found that " << lits[2] << " is equivalent to " << freeLit << endl;
	  return;
	} else {
	  //cerr << "c found equivalence " << lits[2] << " == " << freeLit << " again" << endl;
	}
      }
    } else {
      int hit = 0;
      Lit freeLit = lit_Undef;
      
      bool qPol = false;
      for( int j = 0 ; j < 4; ++ j ) { // enqueue all literals!
        const Lit ol = ( j == 0 ? other.a() : ((j == 1 ) ? other.b() : (j==3? other.c() : other.x()) ) );
	for ( int k = hit; k < 3; ++ k )
	  if( var(ol) == var(lits[k]) ) // if this variable matches, remember that it does! collect the polarity!
	    { const Lit tmp = lits[hit]; lits[hit] = lits[k]; lits[k] = tmp; hit++; pol = pol ^ sign(ol); break; }
	if( hit != j + 1 )
	  if( freeLit == lit_Undef ) freeLit = ol;
	  else { freeLit == lit_Error; break; }
      }
      if( freeLit == lit_Error ) continue; // these gates do not match!
      
      if( pol == qPol ) freeLit = ~freeLit;
      data.addUnitToProof(freeLit);
      if( l_False == data.enqueue(freeLit) ) return;
      //cerr << "c" << endl << "c found the unit " << freeLit << " based on XOR reasoning" << "c NOT HANDLED YET!" << endl << "c" << endl;
      //cerr << "c corresponding gates: " << endl;
      // g.print(cerr);
      // other.print(cerr);
    }
  }
  
  if (active==0 && activeVariables==0) {
      for( int j = 0 ; j < 3; ++ j ) { // enqueue all literals!
	const Var v = var( lits[j] );
	bitType[v] = bitType[v] | 4; // stamp output bit!
	// enqueue gates, if not already inside the queue:
	for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	  if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	    gates[ varTable[ v ][i] ].putInQueue();
	    queue.push_back( varTable[ v ][i] );
	  }
	}
      }
  }
}

void EquivalenceElimination::processFASUMgate(CoprocessorData& data, Circuit::Gate& g, vector< Circuit::Gate >& gates, std::deque< int >& queue, std::vector< unsigned int >& bitType, vector< vector< int32_t > >& varTable, MarkArray* active, std::deque< Var >* activeVariables)
{
//   cerr << "c compare " << queue.size() << " gates against current FASUM gate ";
//   g.print(cerr);
  
  Lit lits[4];
  lits[0] = getReplacement( g.a() ); 
  lits[1] = getReplacement( g.b() ); 
  lits[2] = getReplacement( g.c() ); 
  lits[3] = getReplacement( g.x() ); 
  bool pol = sign(lits[0]) ^ sign(lits[1]) ^ sign(lits[2]) ^ sign(lits[3]);
  
  for( int i = 0 ; i < queue.size(); ++ i ) {
    const Circuit::Gate& other = gates [queue[i]] ;
    if( other.getType() != Circuit::Gate::XOR  // xor is either equivalent to another xor
      && other.getType() != Circuit::Gate::FA_SUM ) continue; // or subsumes equivalent FA_SUM

//     cerr << "c other gate: "; other.print(cerr);
    
    if( other.getType() == Circuit::Gate::FA_SUM ) {
      int hit = 0;
      Lit freeLit = lit_Undef;
      const Lit oa = getReplacement( other.a() ); 
      for( int j = 0; j < 4; ++ j ) {
	if( var(lits[j]) == var(oa) ) { const Lit tmp = lits[0]; lits[0] = lits[j]; lits[j] = tmp; hit++; break; } 
      }
      if( hit == 0 ) freeLit = oa;
//       if( freeLit != lit_Undef ) cerr << "c 1 freelit = " << freeLit << endl;
      const Lit ob = getReplacement( other.b() ); 
      for( int j = hit; j < 4; ++ j ) {
	if( var(lits[j]) == var(ob) ) { const Lit tmp = lits[hit]; lits[hit] = lits[j]; lits[j] = tmp; hit++; break; } 
      }
      if( hit < 2 )  // check for the free literal
	if( hit == 0 ) {/*cerr << "failed with one of literal " << oa << " ," << ob << endl; */continue; } // this xor gate does not match 3 variables!
	else if( freeLit == lit_Undef ) freeLit = ob ; // this literal is the literal that does not match!

//       if( freeLit != lit_Undef ) cerr << "c 2 freelit = " << freeLit << endl;
      const Lit oc = getReplacement( other.c() ); 
      for( int j = hit; j < 4; ++ j ) {
	if( var(lits[j]) == var(oc) ) { const Lit tmp = lits[hit]; lits[hit] = lits[j]; lits[j] = tmp; hit++; break; } 
      }

      if( hit < 3 )  // check for the free literal
	if( hit < 2 ) {/*cerr << "failed with one of literal " << oa << " ," << ob << ", " << oc << endl;*/ continue; } // this xor gate does not match 3 variables!
	else if( freeLit == lit_Undef ) freeLit = oc ; // this literal is the literal that does not match!
      
//       if( freeLit != lit_Undef ) cerr << "c 3 freelit = " << freeLit << endl;
      const Lit od = getReplacement( other.x() ); 
      for( int j = hit; j < 4; ++ j ) {
	if( var(lits[j]) == var(od) ) { const Lit tmp = lits[hit]; lits[hit] = lits[j]; lits[j] = tmp; hit++; break; } 
      }
      
      if( hit < 3 ) {/*cerr << "failed with one of literal " << oa << " ," << ob << ", " << oc << " ," << od << endl;*/ continue; } // this xor gate does not match 3 variables!
      // might be the case that all variables match!
      if( freeLit == lit_Undef ) freeLit = od ; // this literal is the literal that does not match!

//       if( freeLit != lit_Undef ) cerr << "c 4 freelit = " << freeLit << endl;
      // get right polarity!
//       cerr << "c pol= " << pol << " new pol= " << (int)(sign(oa) ^ sign(ob) ^ sign(oc) ^ sign(od) ^ sign(freeLit) ) << endl;
      if( (pol ^ sign(lits[3] ) ) != (sign(oa) ^ sign(ob) ^ sign(oc) ^ sign(od) ^ sign(freeLit) ) ) freeLit = ~freeLit;
      
      if( var(lits[3]) != var(freeLit) ) {
	setEquivalent(lits[3],freeLit);
	data.addEquivalences(lits[3],freeLit);
	cerr << "c equi: " << lits[3] << " == " << freeLit << endl;
	
      if( active == 0 && activeVariables == 0 ) {
	// new equivalent gate -> enqueue successors!
	for( int j = 0 ; j < 4; ++ j ) { // enqueue all literals!
	  const Var v = var( j == 0 ? other.a() : ((j == 1 ) ? other.b() : (j==3? other.c() : other.x()) ) );
	  bitType[v] = bitType[v] | 4; // stamp output bit!
	  // enqueue gates, if not already inside the queue:
	  for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	    if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	      gates[ varTable[ v ][i] ].putInQueue();
	      queue.push_back( varTable[ v ][i] );
	    }
	  }
	}
      } else {
	if( !active->isCurrentStep(   var(lits[3])) ) {
	  active->setCurrentStep(     var(lits[3]) ); 
	  activeVariables->push_back( var(lits[3]) );
	}
	if( !active->isCurrentStep(   var(freeLit)) ) {
	  active->setCurrentStep(     var(freeLit) ); 
	  activeVariables->push_back( var(freeLit) );
	}
      }
	
      } else {
	if( lits[3] == ~freeLit ) {
	  data.setFailed();
	  data.addCommentToProof("structural hashing found that a variable has to be equivalent to its complement");
	  data.addUnitToProof(lits[3]);
	  data.addUnitToProof(freeLit);
	  //cerr << "c failed, because FASUM procedure found that " << lits[3] << " is equivalent to " << freeLit << endl;
	  return;
	} else {
	 // cerr << "c found equivalence " << lits[3] << " == " << freeLit << " again" << endl;
	}
      }
    } else {
      //cerr << " FA_SUM vs XOR: Not implemented yet" << endl;
      // TODO: is the small xor subsumes the big one, the neagtion of the remaining literal has to be unit propagated!
      int hit = 0;
      Lit freeLit = lit_Undef;
      
      bool qPol = false;
      for( int j = 0 ; j < 3; ++ j ) { // enqueue all literals!
        const Lit ol = ( j == 0 ? other.a() : ((j == 1 ) ? other.b() : other.c() ) );
	for ( int k = hit; k < 4; ++ k )
	  if( var(ol) == var(lits[k]) ) // if this variable matches, remember that it does! collect the polarity!
	    { const Lit tmp = lits[hit]; lits[hit] = lits[k]; lits[k] = tmp; hit++; pol = pol ^ sign(ol); break; }
      }
      if( hit < 3 ) continue; // these gates do not match!
      freeLit = lits[3];
      
      if( pol ^ sign( freeLit ) == qPol ) freeLit = ~freeLit;
      data.addUnitToProof(freeLit);
      if( l_False == data.enqueue(freeLit) ) return;
      //cerr << "c" << endl << "c found the unit " << freeLit << " based on XOR reasoning" << "c NOT HANDLED YET!" << endl << "c" << endl;
      //cerr << "corresponding gates:" << endl;
      //g.print(cerr);
      //other.print(cerr);
    }

  }
  
  if( active == 0 && activeVariables == 0 ) {
	// new equivalent gate -> enqueue successors!
	for( int j = 0 ; j < 4; ++ j ) { // enqueue all literals!
	  const Var v = var( j == 0 ? g.a() : ((j == 1 ) ? g.b() : (j==3? g.c() : g.x()) ) );
	  bitType[v] = bitType[v] | 4; // stamp output bit!
	  // enqueue gates, if not already inside the queue:
	  for( int i = 0 ; i < varTable[ v ].size(); ++ i ) {
	    if(! gates[ varTable[ v ][i] ].isInQueue() ) {
	      gates[ varTable[ v ][i] ].putInQueue();
	      queue.push_back( varTable[ v ][i] );
	    }
	  }
	}
  }
  
}

void EquivalenceElimination::findEquivalencesOnBigFast(CoprocessorData& data, vector< vector<Lit> >* externBig)
{
  int dfs = 0;

  vector<Vertex> vertexes ( data.nVars() * 2 );
  
  vector<Lit> todo, path; // work queue, temporary SCC candidate
  
  data.ma.resize( data.nVars() * 2);
  data.ma.nextStep();
  
  if( config.ee_debug_out > 1 ) {
    cerr << "c formula: " << endl;
    for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
      cerr << "[" << i << " ] " << ca[ data.getClauses()[i] ] << endl;
    }
    cerr << "c to process: " << eqDoAnalyze << endl;
  }
  
  // create underlying data structure
  BIG big;
  if( externBig == 0 ) big.create(ca, data.nVars(), data.getClauses(), data.getLEarnts() );
  
  while( !eqDoAnalyze.empty() && !data.isInterupted() && (data.unlimited() || steps < config.opt_ee_limit) )
  {
      // get the literal to start with!
      Lit randL = eqDoAnalyze[ eqDoAnalyze.size() -1 ];
      if( data.randomized() ) { // shuffle an element back!
	uint32_t index = rand() % eqDoAnalyze.size();
	eqDoAnalyze[ eqDoAnalyze.size() -1 ] = eqDoAnalyze[index];
	eqDoAnalyze[index] = randL;
	randL = eqDoAnalyze[ eqDoAnalyze.size() -1 ];
      }
      eqDoAnalyze.pop_back();
      const Lit l = randL;
      isToAnalyze[ var(randL) ] = 0;
      
      if( vertexes[ toInt(l) ].seen != -1  ) {
	if( config.ee_debug_out > 1) cerr << "c do not re-work liteal " << l << endl;
	continue; // saw this literal already!
      }
//       if( data.ma.isCurrentStep( toInt(l) ) ) {
// 	if( config.ee_debug_out > 1) cerr << "c there is already a SCC involving literal " << l << " or its complement" <<  endl;
// 	continue; // already found an SCC with this variable (there will be a symmetric one in the big, no need to find it!)
//       }
      const int size = externBig == 0 ? big.getSize(l) : (*externBig)[toInt(l)].size();
      if( false && size == 0 ) { 
	if( config.ee_debug_out > 1 ) cerr << "c literal " << l << " without children is not analyzed" << endl;
	vertexes[ toInt(l) ].seen = 0; vertexes[ toInt(l) ].min = -2; // set min to invalid!
	continue;
      } // do not process literals without child literals!

      // init literal
      vertexes[ toInt(l) ].start = dfs ++; vertexes[ toInt(l) ].min = vertexes[ toInt(l) ].start;
      assert( todo.size() == 0  && "there cannot be elements in the todo stack when it is initialized!" );
      todo.push_back(l);path.push_back(l);
      
      if( config.ee_debug_out > 1) cerr << "c start with root " << l << endl;
      
      // actual iterative algorithm
      while( todo.size() > 0 ) {
	Lit V = todo.back(); // variable to work on!
	if( config.ee_debug_out > 1) cerr << "c current stack: " << todo << endl;
	if( config.ee_debug_out > 1) cerr << "c continue with " << V << "[" << vertexes[toInt(V)].start << " , " << vertexes[toInt(V)].min << " , " << vertexes[toInt(V)].seen << " / " << ( externBig == 0 ? big.getSize(V) : (*externBig)[toInt(V)].size() ) << "]" << endl;
	
	if( vertexes[ toInt(V) ].seen != -1 ) { // have been working on this literal before already!
	  Lit lastSeen = externBig == 0 ? big.getArray(V)[ vertexes[toInt(V)].seen ] : (*externBig)[toInt(V)][ vertexes[toInt(V)].seen ];
	  vertexes[toInt(V)].min = vertexes[toInt(V)].min < vertexes[ toInt(lastSeen) ].min ? vertexes[toInt(V)].min : vertexes[ toInt(lastSeen) ].min ; // set min of "parent node"
	  if( config.ee_debug_out > 1)  cerr << "c update recursive min(" << V << ") to " << vertexes[toInt(V)].min << endl;
	}
	
	vertexes[toInt(V)].seen ++; // start with 0th element / continue with next element after recursion
	
	// process all child nodes of the current node in the BIG
	const int size = externBig == 0 ? big.getSize(V) : (*externBig)[toInt(V)].size();
	for( ; vertexes[toInt(V)].seen < size; ) { 
	  const Lit v = externBig == 0 ? big.getArray(V)[ vertexes[toInt(V)].seen ] : (*externBig)[toInt(V)][ vertexes[toInt(V)].seen ];
	  if( config.ee_debug_out > 1) cerr << "c check child " << v << " [ seen(" << v << ") =" << vertexes[toInt(v)].seen << " , "  << vertexes[toInt(v)].start << " , " << vertexes[toInt(V)].min << "]" << endl;
	  if( vertexes[toInt(v)].seen == -1 ) { // have not seen this node so far, apply recursion on it
	    if( config.ee_debug_out > 1) cerr << "c found [" << vertexes[toInt(V)].seen << "]:  fresh " << v << "[" << vertexes[toInt(v)].start << " <= " << dfs + 1 << "]" << endl;
	    todo.push_back(v);path.push_back(v);
	    vertexes[toInt(v)].start = dfs ++; vertexes[toInt(v)].min = vertexes[toInt(v)].start; // init the new node!
	    goto nextNode;
	  } else {
	    if( config.ee_debug_out > 1) cerr << "c found [" << vertexes[toInt(V)].seen << "]: already analyzed " << v << " [" << vertexes[toInt(v)].start << " , " << vertexes[toInt(V)].min << "]" << endl;
	    // check this edge only, if the other vertex has not been completed yet!
	    if( !data.ma.isCurrentStep( toInt(v) ) ) // this literal does not give a bigger SCC! -> has been removed from path already!
	      vertexes[toInt(V)].min = vertexes[toInt(V)].min <= vertexes[toInt(v)].start ? vertexes[toInt(V)].min : vertexes[toInt(v)].start ; // set min of "parent node" // TODO: according to recursive algorithm: use start instead of min!
	    if( config.ee_debug_out > 1)  cerr << "c update already found min(" << V << ") to " << vertexes[toInt(V)].min << endl;
	    vertexes[toInt(V)].seen ++;
	  }
	}
	
	// finished all child nodes, check whether a SCC has been found
	if( vertexes[toInt(V)].start == vertexes[toInt(V)].min ) {
	  if( config.ee_debug_out > 1) cerr << "c current Node is SCC root " << V << endl;
	  eqCurrentComponent.clear();
	  Lit w = lit_Undef;
	  Lit minLit = path.back();
	  do { // pop all elements behind V!
	    assert( path.size() > 0 && "there have to be more elements on the stack!" );
	    w = path.back(); path.pop_back();
	    minLit = w < minLit ? w : minLit;
	    if( !config.opt_ee_eager_frozen || !data.doNotTouch( var(w) ) ) eqCurrentComponent.push_back( w ); // add variable only, if it is not frozen, or if frozen variables should not be treated eagerly
	    data.ma.setCurrentStep( toInt(w) ); // ensure that the same SCC will not be found twice!
	    if( config.ee_debug_out > 1) cerr << "c put " << w << "[" << vertexes[toInt(V)].start << "] into the same component!" << endl;
	  } while( w != V );
	  if( eqCurrentComponent.size() > 1 && !sign(minLit) ) { // only add one of the two symmetric SCCs!
	    if( config.ee_debug_out > 1) cerr << "c add SCC of size " << eqCurrentComponent.size() << " with smallest lit " << minLit << " : " << eqCurrentComponent << endl;
	    if( steps < config.opt_ee_limit ) data.addEquivalences( eqCurrentComponent ); // do only add the current component, if its guaranteed to be correct
	  }
	}
	
	// finished the current node, continue with its parent node
	todo.pop_back();
	
	if( config.ee_debug_out > 1) cerr << "c finish working on " << V << "[" << vertexes[toInt(V)].start << " , " << vertexes[toInt(V)].min << " , " << vertexes[toInt(V)].seen << " / " << ( externBig == 0 ? big.getSize(V) : (*externBig)[toInt(V)].size() ) << "]" << endl;
	nextNode:; // jump here if the next recursion depth should be analyzed!
      }

  }
  
  //if( config.ee_debug_out > 1 &&
  if( steps > config.opt_ee_limit ) 
  { cerr  << "c abort rewriting equivalences, because step limit has been reached " << endl; }
}

void EquivalenceElimination::findEquivalencesOnBig(CoprocessorData& data, vector< vector<Lit> >* externBig)
{
  if( config.ee_debug_out > 1 ) cerr << "c call find EE on BIG [ok?: " << data.ok() << "]" << endl;
  if( config.opt_ee_iterative ) return findEquivalencesOnBigFast(data,externBig);
  else return findEquivalencesOnBigRec(data,externBig);
}


void EquivalenceElimination::findEquivalencesOnBigRec(CoprocessorData& data, vector< vector<Lit> >* externBig)
{
  // create / resize data structures:
  if( eqLitInStack == 0 ) eqLitInStack = (char*) malloc( sizeof( char ) * data.nVars() * 2 );
  else  eqLitInStack = (char*) realloc( eqLitInStack, sizeof( char ) * data.nVars() * 2 );
  if( eqInSCC == 0 ) eqInSCC = (char*) malloc( sizeof( char ) * data.nVars()  );
  else  eqInSCC = (char*) realloc( eqInSCC, sizeof( char ) * data.nVars()  );
  eqNodeIndex.resize( data.nVars() * 2, -1 );
  eqNodeLowLinks.resize( data.nVars() * 2, -1 );
  
  // reset all data structures
  eqIndex = 0;
  eqNodeIndex.assign( eqNodeIndex.size(), -1 );
  eqNodeLowLinks.assign( eqNodeLowLinks.size(), -1 );
  memset( eqLitInStack, 0, sizeof(char) * data.nVars() );
  memset( eqInSCC, 0, sizeof(char) * data.nVars() );
  eqStack.clear();
  
  BIG big;
  if( externBig == 0 ) big.create(ca, data.nVars(), data.getClauses(), data.getLEarnts() );
  
  steps += (data.getClauses().size() / 16); // some initial steps, because BIG was created
  
  if( config.ee_debug_out > 2 ) {
     cerr << "c to process: ";
     for( int i = 0 ; i < eqDoAnalyze.size(); ++ i ) {
        cerr << eqDoAnalyze[i] << " ";
     }
      if( config.ee_debug_out > 2 ) {
	cerr << endl << "====================================" << endl;
	cerr << "intermediate formula before gates: [ok?: " << data.ok() << "]" << endl;
	for( int i = 0 ; i < data.getTrail().size(); ++ i ) cerr << "[" << data.getTrail()[i] << "]" << endl;
	for( int i = 0 ; i < data.getClauses().size(); ++ i )
	  if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getClauses()[i] ] << endl;
	for( int i = 0 ; i < data.getLEarnts().size(); ++ i )
	  if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getLEarnts()[i] ] << endl;    
	cerr << "====================================" << endl << endl;
      }
     cerr << endl;
  }
  
  while( !eqDoAnalyze.empty() && !data.isInterupted() && (data.unlimited() || steps < config.opt_ee_limit) )
  {
      Lit randL = eqDoAnalyze[ eqDoAnalyze.size() -1 ];
      if( data.randomized() ) { // shuffle an element back!
	uint32_t index = rand() % eqDoAnalyze.size();
	eqDoAnalyze[ eqDoAnalyze.size() -1 ] = eqDoAnalyze[index];
	eqDoAnalyze[index] = randL;
	randL = eqDoAnalyze[ eqDoAnalyze.size() -1 ];
      }
      eqDoAnalyze.pop_back();
      isToAnalyze[ var(randL) ] = 0;
      
      const Lit l = randL;
      // filter whether the literal should be tested!

      // skip literal, if it is already in a SCC or it does not imply anything
      if( eqInSCC[ var(l) ] == 1 ) continue;
      if( data.doNotTouch( var(l) ) ) continue;
      // compute SCC
      eqCurrentComponent.clear();
      
      // TODO: iterative version of tarjan algorithm:
      // if there is any SCC, add it to SCC, if it contains more than one literal
      eqTarjan(1,l,l,data,big,externBig);
  }
}

#define MININ(x,y) (x) < (y) ? (x) : (y)

void EquivalenceElimination::eqTarjan(int depth, Lit l, Lit list, CoprocessorData& data, BIG& big, vector< vector< Lit > >* externBig)
{
    eqNodeIndex[toInt(l)] = eqIndex;
    eqNodeLowLinks[toInt(l)] = eqIndex;
    eqIndex++;
    eqStack.push_back(l);
    eqLitInStack[ toInt(l) ] = 1;
    
    if( depth > 32000 ) {
      static bool didit = false;
      if( !didit ) { cerr << "c recursive EE algorithm reached depth 32K, use the iterative version!" << endl; didit = true; }
      return; // stop recursion here, because it can break things when too many recursive calls are done!
    }
    
    steps ++;
    if( steps > config.opt_ee_limit ) {
      //if( config.ee_debug_out > 1 ) 
	cerr  << "c reject analyzing SSCs further, because step limit is reached " << endl;
      return;
    }
    
    if( config.ee_debug_out > 2 ) cerr  << "c run tarjan on " << l << " at depth " << depth << endl;
    if( externBig != 0 ) {
      const vector<Lit>& impliedLiterals =  (*externBig)[ toInt(list) ];
      for(uint32_t i = 0 ; i < impliedLiterals.size(); ++i)
      {
        const Lit n = impliedLiterals[i];
        if(eqNodeIndex[toInt(n)] == -1){
          eqTarjan(depth+1, n, n, data,big,externBig);
          eqNodeLowLinks[toInt(l)] = MININ( eqNodeLowLinks[toInt(l)], eqNodeLowLinks[toInt(n)]);
        } else if( eqLitInStack[ toInt(n) ] == 1 ){
          eqNodeLowLinks[toInt(l)] = MININ(eqNodeLowLinks[toInt(l)], eqNodeIndex[toInt(n)]);
        }
      }
    } else {
      const Lit* impliedLiterals = big.getArray(list);
      const uint32_t impliedLiteralsSize = big.getSize(list);
      for(uint32_t i = 0 ; i < impliedLiteralsSize; ++i)
      {
        const Lit n = impliedLiterals[i];
	if( config.ee_debug_out > 2 ) cerr << "c next implied lit from " << l << " is " << n << " [" << i << "/" << impliedLiteralsSize << "]" << endl;
        if(eqNodeIndex[toInt(n)] == -1){
          eqTarjan(depth+1, n, n, data,big,externBig);
          eqNodeLowLinks[toInt(l)] = MININ( eqNodeLowLinks[toInt(l)], eqNodeLowLinks[toInt(n)]);
        } else if( eqLitInStack[ toInt(n) ] == 1 ){
          eqNodeLowLinks[toInt(l)] = MININ(eqNodeLowLinks[toInt(l)], eqNodeIndex[toInt(n)]);
        }
      }
    }

    // TODO: is it possible to detect failed literals?
    
     if(eqNodeLowLinks[toInt(l)] == eqNodeIndex[toInt(l)]){
         Lit n;
	 eqCurrentComponent.clear();
         do{
             n = eqStack[eqStack.size() - 1]; // *(eqStack.rbegin());
             eqStack.pop_back();
             eqLitInStack[ toInt(n) ] = 0;
             eqInSCC[ var(n) ] = 1;
	     if( !config.opt_ee_eager_frozen || !data.doNotTouch( var(n) ) ) eqCurrentComponent.push_back( n ); // add variable only, if it is not frozen, or if frozen variables should not be treated eagerly
             //eqCurrentComponent.push_back(n);
         } while(n != l);
	 if( eqCurrentComponent.size() > 1 ) {
	   if( config.ee_debug_out > 1 ) cerr << "c ee SCC: " << eqCurrentComponent << endl; 
	   if( steps < config.opt_ee_limit ) data.addEquivalences( eqCurrentComponent ); // do add elements to the equivalence class only, if scanning completed!
	 }
     }
}


Lit EquivalenceElimination::getReplacement( Lit l) 
{
  while ( var(replacedBy[var(l)]) != var(l) ) l = sign(l) ? ~replacedBy[var(l)] : replacedBy[var(l)]; // go down through the whole hierarchy!
  // replacedBy[var(startLit)] = l; // speed up future calculations!
  return l;
}

bool EquivalenceElimination::setEquivalent(Lit representative, Lit toReplace)
{
  const Lit r = getReplacement(representative);
  const Lit s = getReplacement(toReplace);
  if( r == ~s ) return false;
  if( config.ee_debug_out > 2 ) cerr << "c ee literals: " << representative << " ( -> " << r << ") is representative for " << toReplace << " ( -> " << s << ")" << endl;
  if( r < s ) {
    replacedBy[ var(s) ] = ( sign(s) ? ~r : r ); // propagate forward!  
  } else {
    replacedBy[ var(r) ] = ( sign(r) ? ~s : s ); // propagate forward!  
  }
  /*
  replacedBy[ var(toReplace) ] = ( sign(toReplace) ? ~r : r );
  replacedBy[ var(s) ] = ( sign(s) ? ~r : r ); // propagate forward!
  */
  return true;
}

bool EquivalenceElimination::applyEquivalencesToFormula(CoprocessorData& data, bool force)
{
  bool newBinary = false;
  bool resetVariables = false;
  if( data.getEquivalences().size() > 0 || force) {
   
    // TODO: take care of units that have to be propagated, if an element of an EE-class has already a value!
    isToAnalyze.resize( data.nVars(), 0 );
    data.ma.resize(2*data.nVars());
    
    if( replacedBy.size() < data.nVars() ) { // extend replacedBy structure
      for( Var v = replacedBy.size(); v < data.nVars(); ++v )
	replacedBy.push_back ( mkLit(v,false) );
    }
    
   vector<Lit>& ee = data.getEquivalences();
   
   if( config.ee_debug_out > 2 ) {
      if( config.ee_debug_out > 2 ) {
	cerr << endl << "====================================" << endl;
	cerr << "intermediate formula before APPLYING Equivalences: [ok?: " << data.ok() << "]" << endl;
	for( int i = 0 ; i < data.getTrail().size(); ++ i ) cerr << "[" << data.getTrail()[i] << "]" << endl;
	for( int i = 0 ; i < data.getClauses().size(); ++ i )
	  if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getClauses()[i] ] << endl;
	cerr << "c learnts: " << endl;
	for( int i = 0 ; i < data.getLEarnts().size(); ++ i )
	  if( !ca[  data.getClauses()[i] ].can_be_deleted() ) cerr << ca[  data.getLEarnts()[i] ] << endl;    
	cerr << "====================================" << endl << endl;
      }
      
     cerr << "c equivalence stack: " << endl;
    for( int i = 0 ; i < ee.size(); ++ i ) {
      if( ee[i] == lit_Undef ) cerr << endl;
      else cerr << " " << ee[i];
    }
    cerr << endl;
   }
   
   int start = 0, end = 0;
   
   if( config.opt_ee_eager_frozen )
   { // remove all frozen variables from the ee classes!
    int keep = 0;
    for( int i = 0 ; i < ee.size(); ++ i ) {
      if( ee[i] == lit_Undef || !data.doNotTouch( var( ee[i] ) ) ) ee[keep++] = ee[i]; // keep all literals that are not frozen, and keep the "lit_Undef" separators!
    }
    ee.resize(keep);
   }
   
   for( int i = 0 ; i < ee.size(); ++ i )
   {
     if( ee[i] == lit_Undef ) {
       // handle current EE class!
       end = i - 1;
       Lit repr = getReplacement(ee[start]);
        data.ma.nextStep(); // TODO FIXME check whether this has to be moved before the for loop
	for( int j = start ; j < i; ++ j ) // select minimum!
	{ 
	  repr =  repr < getReplacement(ee[j]) ? repr : getReplacement(ee[j]);
//	  data.ma.setCurrentStep( toInt( ee[j] ) );
	}

       // check whether a literal has also an old replacement that has to be re-considered!
       data.lits.clear();
       
       equivalentLits --; // one of the literals wont be removed
       for( int j = start ; j < i; ++ j ) {// set all equivalent literals
	 const Lit myReplace = getReplacement(ee[j]);
	 if( myReplace == ee[j] ) equivalentLits ++; // count how many equal literals
	 if( ! data.ma.isCurrentStep( toInt( myReplace )) )
	   data.lits.push_back(myReplace); // has to look through that list as well!
	   
	 // add the equivalence to the proof, as single sequential clauses
	 if( data.outputsProof() && repr != ee[j] ) { // do not add trivial clauses to the proof!
	  data.addCommentToProof("add equivalence to proof");
	  if( ee[j] != ~repr ) { // added equivalences should have different literals, and not complementarly literals (although this case exists)
	    proofClause.clear();proofClause.push_back( ~repr ); proofClause.push_back(ee[j]);
	    data.addToProof(proofClause, false,  ee[j]); // the literal that is not kept should be the first literal, because this way the same equivalence can be added multiple times
	    proofClause[0] = ~proofClause[0]; if( ee[j] != ~repr ) proofClause[1] = ~proofClause[1];
	    data.addToProof(proofClause, false, ~ee[j]); // the literal that is not kept should be the first literal, because this way the same equivalence can be added multiple times
	  }
	 }
	   
	 if( ! setEquivalent(repr, ee[j] ) ) { 
	   if( data.outputsProof() ) {
	     data.addCommentToProof("setting equivalent failed - add a unit to the proof to test this behavior per UP");
	     proofClause.clear(); proofClause.push_back( repr );
	     data.addToProof(proofClause);
	   }
	   if( config.ee_debug_out > 2 ) cerr << "c applying EE failed due to setting " << repr << " and " << ee[j] << " equivalent -> UNSAT" << endl;
	   data.setFailed(); return newBinary;
	}
       }
       
       if(config.ee_debug_out > 2)
       for( int j = start ; j < i; ++ j ) {// set all equivalent literals
         cerr << "c replace " << (sign(ee[j]) ? "-" : "" ) << var(ee[j]) + 1 << " by " << (sign(getReplacement(ee[j])) ? "-" : "" ) << var(getReplacement(ee[j])) + 1 << endl;
       }
       
       int dataElements = data.lits.size();
       
       data.clss.clear();
        // check whether one of the EE-class literals is already assigned, if yes, enqueue the remaining literals!
       lbool setValue =  data.value(repr);
       if( setValue == l_Undef ) {
	setValue =  data.value(getReplacement(repr));
	if( setValue == l_Undef ) {
	  for( int j = start ; j < i; ++ j ) {
	    if( data.value( ee[j] ) != l_Undef ) { setValue = data.value( ee[j] ); break; } // found one assigned literal
	    if( data.value( getReplacement(ee[j]) ) != l_Undef ) { setValue = data.value( getReplacement(ee[j]) ); break; } // found one assigned literal
	  }
	}
       }
       if( setValue == l_Undef ) {
	for( int j = start ; j < i; ++ j ) { // nothing set, simply add back the clauses as before!
	  if ( ee[j] == repr ) continue;
	  if( !data.doNotTouch( var(ee[j]) ) ) continue; // only create these clauses for the "do not touch" literals
	  data.addCommentToProof("add clauses for doNotTouch variables");
	  proofClause.clear(); // create repr <-> ee[j] clauses and add them!
	  proofClause.push_back( ~repr );proofClause.push_back( ee[j] );
          CRef cr = ca.alloc(proofClause, false); 
	  data.addToProof(ca[cr]); // tell proof about the new clause!
	  ca[cr].setExtraInformation( data.defaultExtraInfo() ); // setup extra information for this clause!
	  data.clss.push_back(cr);
	  proofClause[0] = repr; proofClause[1] = ~ee[j];
          cr = ca.alloc(proofClause, false); 
	  data.addToProof(ca[cr]); // tell proof about the new clause!
	  data.clss.push_back(cr);
	  ca[cr].setExtraInformation( data.defaultExtraInfo() ); // setup extra information for this clause!
	}
       } else {
	 if( setValue == l_True ) {
	   for( int j = start ; j < i; ++ j ) {
	     if( data.value( ee[j] ) == l_True ) continue;
	     else if( data.value( ee[j] ) == l_False ) { data.setFailed(); break; }
	     else { 
	       data.enqueue( ee[j], data.defaultExtraInfo() ); // enqueue the literal itself!
	       data.addCommentToProof("added by EE class");
	       data.addUnitToProof( ee[j] );
	     }
	   }
	 } else {
	   assert( setValue == l_False && "all complements of the class literals have to be satisfied, because set above!" );
	   for( int j = start ; j < i; ++ j ) {
	     if( data.value( ee[j] ) == l_False ) continue;
	     else if( data.value( ee[j] ) == l_True ) { data.setFailed(); break; }
	     else {
	       data.enqueue( ~ee[j], data.defaultExtraInfo() ); // enqueue the complement!
	       data.addCommentToProof("added by EE class");
	       data.addUnitToProof( ~ee[j] );
	     }
	   }
	 }
	 
	 // go to next EE class!
	 
       }
       
       // rewrite formula only if the EE class is not yet set as units
       if( setValue == l_Undef )
       {
       
       data.ma.nextStep();
       for( int j = start ; j < i; ++ j ) { // process each element of the class!
	 Lit l = ee[j];
	 // first, process all the clauses on the list with old replacement variables
	 if( j == start && dataElements > 0 ) {
	   l = data.lits[ --dataElements ]; 
	   if( config.ee_debug_out > 2) cerr << "c process old replace literal " << l << endl;
	   j--;
         }
	 
	 if( l == repr ) {
	   if( config.ee_debug_out > 2) cerr << "c do not process representative " << l << endl;
	   continue;
	 }
	 
	 data.log.log(eeLevel,"work on literal",l);
	 
	 // add to extension here!
	 if( !data.doNotTouch(var(l)) && ! data.ma.isCurrentStep(var(l)) && 
	   (data.list( l ).size() > 0 ||  data.list( ~l ).size() > 0) ) { // only add to extension, if clauses will be rewritten!
	  data.addToExtension( ~repr , l );
	  data.addToExtension( repr , ~l);
	  if( config.ee_debug_out > 2 ) cerr << "c added to extension: " << repr << " <=> " << l << endl;
	  data.ma.setCurrentStep(var(l)); // to not add same equivalence twice
	 } else {
	   if( config.ee_debug_out > 2 ) cerr << "c do not add to extension: " << repr << " <=> " << l << endl; 
	 }
	 
	 // if( getReplacement(l) == repr )  continue;
	 // TODO handle equivalence here (detect inconsistency, replace literal in all clauses, check for clause duplicates!)
	 for( int pol = 0; pol < 2; ++ pol ) { // do for both polarities!
	  vector<CRef>& list = pol == 0 ? data.list( l ) : data.list( ~l );
	  if( config.ee_debug_out > 2 ) cerr << "c rewrite clauses of lit " << ( pol == 0 ? l : ~l )<< endl;
	  for( int k = 0 ; k < list.size(); ++ k ) {
	    Clause& c = ca[list[k]];
	    if( c.can_be_deleted() ) {
	      if( config.ee_debug_out > 2 ) cerr << "c skip clause " << c << " it can be deleted already" << endl;
	      continue; // do not use deleted clauses!
	    }
	    data.log.log(eeLevel,"analyze clause",c);
	    if( config.ee_debug_out > 2 ) cerr << "c analyze clause " << c << endl;
	    bool duplicate  = false;
	    bool getsNewLiterals = false;
	    
	    if( data.outputsProof()) { // only if we do a proof, copy the clause!
	      proofClause.clear();
	      for( int m = 0 ; m < c.size(); ++ m ) proofClause.push_back(c[m]);
	    }
	    
	    // TODO: update counter statistics for all literals of the clause!
	    for( int m = 0 ; m < c.size(); ++ m ) {
	      if( c[m] == repr || c[m] == ~repr) { duplicate = true; continue; } // manage that this clause is not pushed into the list of clauses again!
	      const Lit tr = getReplacement(c[m]);
	      if( tr != c[m] ) getsNewLiterals = true;
	      c[m] = tr;
	    }
	    
	    c.sort(); // sort the clause!
	    c.updateExtraInformation( data.defaultExtraInfo() ); // since it cannot be traced which clauses participated, we assume the worst case to be on the safe side!
	    
	    int n = 1,removed=0;
	    for( int m = 1; m < c.size(); ++ m ) {
	      if( c[m-1] == ~c[m] ) { 
		if( config.ee_debug_out > 2 ) cerr << "c ee deletes clause " << c << endl;
		c.set_delete(true); 
		removedCls++;
		data.addToProof(proofClause,true); // delete the clause, if we do the proof
		goto EEapplyNextClause;
	      } // this clause is a tautology
	      if( c[m-1] != c[m] ) { c[n++] = c[m]; removed ++; }
	    }
	    c.shrink(c.size() - n);
	    if( config.ee_debug_out > 2 ) cerr << "c ee shrinked clause to " << c << endl;
	    modifiedFormula = true;
	    
	    data.addToProof(c); // add the reduced clause to the formula!
	    data.addToProof(proofClause,true); // delete the clause, if we do the proof
	    
	    if( c.size() == 2 )  { // take care of newly created binary clause for further analysis!
	      newBinary = true;
	      if( isToAnalyze[ var(c[0]) ] == 0 ) {
		eqDoAnalyze.push_back(~c[0]);
		if( config.ee_debug_out > 2 ) cerr << "c enable literal " << ~c[0] << endl;
		isToAnalyze[ var(c[0]) ] = 1;
		if( config.ee_debug_out > 2 ) cerr << "c EE re-enable ee-variable " << var(c[0])+1 << endl;
	      }
	      if( isToAnalyze[ var(c[1]) ] == 0 ) {
		eqDoAnalyze.push_back(~c[1]);
		if( config.ee_debug_out > 2 ) cerr << "c enable literal " << ~c[1] << endl;
		isToAnalyze[ var(c[1]) ] = 1;
		if( config.ee_debug_out > 2 ) cerr << "c EE re-enable ee-variable " << var(c[1])+1 << endl;
	      }
	    } else if (c.size() == 1 ) {
	      c.set_delete(true); // remove this clause from the current formula !
	      if( data.enqueue(c[0], data.defaultExtraInfo() ) == l_False ) return newBinary; 
	    } else if (c.size() == 0 ) {
	      data.setFailed(); 
	      if( config.ee_debug_out > 2 ) cerr << "c applying EE failed due getting an empty clause" << endl;
	      return newBinary; 
	    }
	    data.log.log(eeLevel,"clause after sort",c);
	    
	    if( c.size() > 1 &&  !duplicate ) {
  // 	    cerr << "c give list of literal " << (pol == 0 ? repr : ~repr) << " for duplicate check" << endl;
	      if( !hasDuplicate( data, data.list( (pol == 0 ? repr : ~repr)  ), c )  ) {
		data.list( (pol == 0 ? repr : ~repr) ).push_back( list[k] );
		if( getsNewLiterals ) {
		  if( data.addSubStrengthClause( list[k] ) && config.opt_eeSub ) resetVariables = true;
		}
	      } else {
		if( config.ee_debug_out > 2 ) cerr << "c clause[" << list[k] << "] has duplicates: " << c << endl;
		removedCls++;
		data.addToProof(c,true); // delete the clause, since we found duplicates
		c.set_delete(true);
		data.removedClause(list[k]);
		modifiedFormula = true;
	      }
	    } else {
  // 	    cerr << "c duplicate during sort" << endl; 
	    }
	    
  EEapplyNextClause:; // jump here, if a tautology has been found
	  }
	 } // end polarity
       
	 
	 // clear the occurrence lists, since there are no clauses in them any more!
	 assert( l != repr && "will not clear list of representative literal!" );
	 for( int pol = 0; pol < 2; ++ pol ) // clear both occurrence lists!
	   (pol == 0 ? data.list( l ) : data.list( ~l )).clear();
	 if( config.ee_debug_out > 2 ) cerr << "c cleared list of var " << var( l ) + 1 << endl;
	 
      }
      
       } // finished rewriting

       // TODO take care of untouchable literals!
	for( int j = 0 ; j < data.clss.size(); ++ j ) {
	  if( config.ee_debug_out > 2 ) cerr << "c clause added back: " << ca[data.clss[j]] << endl;
	  data.addClause( data.clss[j] );
	  data.getClauses().push( data.clss[j] );
	}
       
       for( int j = start ; j < i; ++ j ) {// set all equivalent literals
	 const Lit myReplace = getReplacement(ee[j]);
	 // add the equivalence to the proof, as single sequential clauses
	 if( data.outputsProof() && repr != ee[j] ) { // do not add trivial clauses to the proof!
	  data.addCommentToProof("remove equivalences from proof again");
	  proofClause.clear();proofClause.push_back( ~repr ); if( ee[j] != ~repr ) proofClause.push_back(ee[j]);
	  data.addToProof(proofClause, true);
	  proofClause[0] = ~proofClause[0]; if( ee[j] != ~repr ) proofClause[1] = ~proofClause[1];
	  data.addToProof(proofClause, true);
	 }
       }
       
       start = i+1;
       
       // the formula will change, thus, enqueue everything
       if( data.hasToPropagate() || ( config.opt_eeSub && subsumption.hasWork() ) ) {
	 resetVariables = true;
       }
// TODO necessary here?
       // take care of unit propagation and subsumption / strengthening
       if( data.hasToPropagate() ) { // after each application of equivalent literals perform unit propagation!
	 if( propagation.process(data,true) == l_False ) return newBinary;
       }
       if( config.opt_eeSub ){
	subsumption.process();
	if( data.hasToPropagate() ) { // after each application of equivalent literals perform unit propagation!
	  if( propagation.process(data,true) == l_False ) return newBinary;
	}
       }
       
     } // finished current class, continue with next EE class!
   }
   
   // TODO: take care of the doNotTouch literals inside the stack, which have been replaced still -> add new binary clauses!
   
   ee.clear(); // clear the stack, because all EEs have been processed
       
   // if force, or there has been equis:
       // take care of unit propagation and subsumption / strengthening
    if( data.hasToPropagate() ) { // after each application of equivalent literals perform unit propagation!
	 resetVariables = true;
	 newBinary = true; // potentially, there are new binary clauses
	 if( propagation.process(data,true) == l_False ) return newBinary;
    }
    if( config.opt_eeSub && subsumption.hasWork() ) {
      subsumption.process();
      newBinary = true; // potentially, there are new binary clauses
      resetVariables = true;
      if( data.hasToPropagate() ) { // after each application of equivalent literals perform unit propagation!
	resetVariables = true;
	newBinary = true; // potentially, there are new binary clauses
	if( propagation.process(data,true) == l_False ) return newBinary;
      }
    }

  }
  
    modifiedFormula = modifiedFormula || propagation.appliedSomething() || subsumption.appliedSomething();
    
    // the formula will change, thus, enqueue everything
    if( config.opt_eeFullReset && resetVariables ) {
    // re-enable all literals (over-approximation) 
      for( Var v = 0 ; v < data.nVars(); ++ v ) {
	  if( isToAnalyze[ v ] == 0 ) {
		eqDoAnalyze.push_back( mkLit(v,false) );
		if( config.ee_debug_out > 2 ) cerr << "c enable literal " << mkLit(v,false) << endl;
		isToAnalyze[ v ] = 1;
	  }
      }
    }
  
  if( config.ee_debug_out > 2 ) cerr << "c APLLYing Equivalences terminated with new binaries: " << newBinary << endl;
  return newBinary || force;
}

/** check whether on of the two clauses subsumes the other ! */
static bool ordered_subsumes (const Clause& c, const Clause & other) 
{
    int i = 0, j = 0;
    while (i < c.size() && j < other.size())
    {
        if (c[i] == other[j])
        {
            ++i;
            ++j;
        }
        // D does not contain c[i]
        else if (c[i] < other[j])
            return false;
        else
            ++j;
    }
    if (i == c.size())
        return true;
    else
        return false;
}

bool EquivalenceElimination::hasDuplicate(CoprocessorData& data, vector<CRef>& list, const Clause& c)
{
  bool irredundant = !c.learnt();
//   cerr << "c check for duplicates: " << c << " (" << c.size() << ") against " << list.size() << " candidates" << endl;
  for( int i = 0 ; i < list.size(); ++ i ) {
    Clause& d = ca[list[i]];
//     cerr << "c check " << d << " [del=" << d.can_be_deleted() << " size=" << d.size() << endl;
    if( d.can_be_deleted() || d.size() != c.size() ) continue;
    int j = 0 ;
    while( j < c.size() && c[j] == d[j] ) ++j ;
    if( j == c.size() ) { 
//       cerr << "c found partner" << endl;
      if( irredundant && d.learnt() ) {
	data.addCommentToProof("delete duplicate clause");
	data.addToProof(d,true);
	d.set_delete(true); // learned clauses are no duplicate for irredundant clauses -> delete learned!
	return false;
      }
      if( config.ee_debug_out > 2 ) cerr << "c find duplicate [" << list[i] << "]" << d << " for clause " << c << endl;
      return true;
    }
    if( config.opt_EE_checkNewSub ) { // check each clause for being subsumed -> kick subsumed clauses!
      if( d.size() < c.size() && (!d.learnt() || c.learnt()) ) { // do not remove a non-learnt clause by a learnt clause!
	if( ordered_subsumes(d,c) ) {
	  if( config.ee_debug_out > 1 ) cerr << "c clause " << c << " is subsumed by [" << list[i] << "] : " << d << endl;
	  return true; // the other clause subsumes the current clause!
	}
      } else if( d.size() > c.size() && (!c.learnt() || d.learnt() )) { // if size is equal, then either removed before, or not removed at all!
	if( ordered_subsumes(c,d) ) { 
	  d.set_delete(true);
	  data.addCommentToProof("delete subsumed clause");
	  data.addToProof(d,true);
	  data.removedClause(list[i]);
	  removedViaSubsubption ++;
	  list[i] = list.back(); list.pop_back(); --i; // remove clause from list!
	}
      }
    }
  }
  return false;
}


void EquivalenceElimination::writeAAGfile(CoprocessorData& data)
{
  // get the circuit!
  vector<Circuit::Gate> gates;
  Circuit circ(config,ca); 
  circ.extractGates(data, gates);
  unsigned char type [ data.nVars() ];
  memset( type,0, sizeof(unsigned char) * data.nVars() );
  
  for( int i = 0 ; i < gates.size(); ++ i ) {
    const Circuit::Gate& g = gates[i];
    if( g.getType() != Circuit::Gate::AND ) continue;
    type [ var(g.x()) ] = ( type [ var(g.x()) ] | 1 ); // set output
    type [ var(g.a()) ] = ( type [ var(g.a()) ] | 2 ); // set input
    type [ var(g.b()) ] = ( type [ var(g.b()) ] | 2 ); // set input
  }
  vector <Var> pureInputs;
  vector <Var> pureOutputs;
  
  for( Var v = 0 ; v < data.nVars(); ++v ) {
    if( type[v] == 1 ) pureOutputs.push_back(v);
    if( type[v] == 2 ) pureInputs.push_back(v);
  }
  cerr << "AAG:" << endl
       << " maxV=" << data.nVars()
       << " inputs=" << pureInputs.size()
       << " outputs=" << pureOutputs.size()
       << " gates=" << gates.size() << endl;
  
  ofstream AAG( config.opt_ee_aagFile );
  AAG << "aag "
      << data.nVars() << " "
      << pureInputs.size() << " "
      << "0 "
      << pureOutputs.size() << " "
      << gates.size() << endl;
  // input
  for( int i = 0 ; i< pureInputs.size(); ++ i )
    AAG << (pureInputs[i]+1)*2 << endl;
  // output
  for( int i = 0 ; i< pureOutputs.size(); ++ i )
    AAG << (pureOutputs[i]+1)*2 << endl;
  // gates
  for( int i = 0; i < gates.size(); ++ i ) {
    const Circuit::Gate& g = gates[i];
    int lx = (var( g.x()) + 1) * 2 + ( sign(g.x()) ? 1 : 0);
    int la = (var( g.a()) + 1) * 2 + ( sign(g.a()) ? 1 : 0);
    int lb = (var( g.b()) + 1) * 2 + ( sign(g.b()) ? 1 : 0);
    AAG << lx << " " << la << " " << lb << endl;
  }
  AAG.close();
}


void EquivalenceElimination::printStatistics(ostream& stream)
{
  stream << "c [STAT] EE " << eeTime << " s, " << steps << " steps " << equivalentLits << " ee-lits " << removedCls << " removedCls, " << removedViaSubsubption << " removedSubCls," << endl;
  if( config.opt_ee_level > 0 ) stream << "c [STAT] EE-gate " << gateTime << " s, " << gateSteps << " steps, " << gateExtractTime << " extractGateTime, " << endl;
}


void EquivalenceElimination::destroy()
{
  vector< Lit >().swap( eqStack);		
  vector< int32_t >().swap( eqNodeLowLinks);	
  vector< int32_t >().swap( eqNodeIndex);	
  vector< Lit >().swap( eqCurrentComponent);	

  vector<Lit>().swap( replacedBy);              
  
  vector<char>().swap( isToAnalyze);            
  vector<Lit>().swap( eqDoAnalyze);        
  
  if( eqLitInStack != 0 ) { free(eqLitInStack); eqLitInStack = 0; }
  
}
