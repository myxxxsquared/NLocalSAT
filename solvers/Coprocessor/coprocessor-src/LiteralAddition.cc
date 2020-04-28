/******************************************************************************[LiteralAddition.cc]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/LiteralAddition.h"

using namespace Coprocessor;

LiteralAddition::LiteralAddition( CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Coprocessor::Propagation& _propagation )
: Technique(_config, _ca,_controller)
, data(_data)
, propagation( _propagation )

, claTestedLits(0)
, claSteps(0)
, claExtendedClauses(0)
, claExtensions(0)
, possibleClaExtensions(0)

, alaSteps(0)
, alaTestedLits(0)
, alaExtensions(0)
{
  
}


void LiteralAddition::reset()
{
  
}
  
void LiteralAddition::asymemtricLiteralAddition()
{
  MethodClock mc (alaTime);
  LitOrderLAHeapLt comp(data, false); // use this sort criteria!
  Heap<LitOrderLAHeapLt> laHeap(comp);  // heap that stores the variables according to their frequency 
  
  // setup own structures
  laHeap.addNewElement(data.nVars() * 2); // set up storage, does not add the element
  laHeap.clear();

  if( config.opt_la_debug ) {
    cerr << "c before ALA formula" << endl;
    for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	cerr << "(" << i << ") (" << data.getClauses()[i] << ")" ;
	if( ca[data.getClauses()[i]].mark() != 0 ) cerr << " (ign) ";
	if( ca[data.getClauses()[i]].can_be_deleted() != 0 ) cerr << " (del) ";
	cerr << " " << ca[ data.getClauses()[i] ] << endl;
      }
  }

  MarkArray nextRound;
  vector<Lit> nextRoundLits;
  nextRound.create(2*data.nVars());
  
  // init
  for( Var v = 0 ; v < data.nVars(); ++ v ) // one literals that appear at least twice, otherwise it doesnt work
  {
    if( data[  mkLit(v,false) ] > 1 ) if( !laHeap.inHeap(toInt(mkLit(v,false))) )  nextRoundLits.push_back( mkLit(v,false) );
    if( data[  mkLit(v,true)  ] > 1 ) if( !laHeap.inHeap(toInt(mkLit(v,true))) )   nextRoundLits.push_back( mkLit(v,true) );
  }
  data.ma.resize(2*data.nVars());
  data.ma.nextStep();

  int iterations = 0;
  do {
    
    if ( iterations >= config.alaIterations ) break; // stop here!
    iterations ++;

    // re-init heap
    for( int i = 0 ; i < nextRoundLits.size(); ++ i ) {
      const Lit l = nextRoundLits[i];
      assert( !laHeap.inHeap(toInt(l)) && "literal should not be in the heap already!" );
      laHeap.insert( toInt(l) );
    }
    nextRoundLits.clear();
    nextRound.nextStep();
    
    
    // do LiteralAddition on all the literals of the heap
    while (laHeap.size() > 0 && (data.unlimited() || config.alaLimit > alaSteps) && !data.isInterupted() )
    {
	// interupted ?
	if( data.isInterupted() ) break;
	  
	const Lit right = toLit(laHeap[0]);
	assert( laHeap.inHeap( toInt(right) ) && "item from the heap has to be on the heap");
	laHeap.removeMin();

	alaTestedLits++; // count number of literals that have been tested for BCE
	// check whether a clause is a tautology wrt. the other clauses
	if( config.opt_la_debug ) cerr << "c CLA work on literal " << right << " with " << data.list(right).size() << " clauses " << endl;
	data.lits.clear(); // used for covered literal elimination
	const int listSize = data.list(right).size(); // do not process the newly generated clause here as well!
	for( int i = 0 ; i < listSize; ++ i ) 
	{
	  Clause& cfor = ca[ data.list(right)[i] ];
	  if( cfor.can_be_deleted() || cfor.learnt() ) continue; // do not work on uninteresting clauses!
	  
	  if( !config.ala_binary && cfor.size() == 2 ) continue; // do not perform ALA for binary clauses!

	  // perform check only for literals that occur least frequent!
	  int rightOcc = data.list(right).size();
	  bool isLeastFrequent = true;
	  for( int k = 0 ; k < cfor.size(); ++ k ) {
	    if( data.list( cfor[k] ).size() < rightOcc ) {
	      isLeastFrequent = false; break;
	    }
	  }
	  if( !isLeastFrequent ) continue; // do not work with this clause on that literal, because its not among the least frequent literals!
	  
	  data.lits.clear(); // collect the literals that could be added by CLA
	  
	  bool canCla = false; // yet, no resolvent has been produced -> cannot perform CLA
	  
	  // reference cfor is only valid until here, since inner loop adds clauses to ca!
	  for( int j = 0 ; j < data.list(right).size(); ++ j )
	  {
	    if( i == j ) continue; // do not work on the same literal twice!
	    Clause& c = ca[ data.list(right)[i] ];
	    Clause& d = ca[ data.list(right)[j] ];
	    if( config.opt_la_debug ) cerr << "c check " << c << " being contained in " << d << " with lit " << right << endl;
	    if( d.can_be_deleted() || d.learnt() ) continue; // do not work on uninteresting clauses!
	    if( d.size() != c.size() ) continue; // in this case, d cannot contain c \setminus e
	    alaSteps ++;
	    
	    // test whether all literals of c except on literal occur also in d!
	    int ci=0,di=0;
	    Lit e = lit_Undef;
	    bool failed = false;
	    while( ci < c.size() && di < d.size() )
	    {
	      if( c[ci] == d[di] ) { // same literal
		ci++; di ++; // move pointer
	      } else if ( c[ci] == ~ d[di] ) { // complement literal - would strengthen, do not want to have this here!
		failed = true; break;
	      } else if ( c[ci] < d[di] ) { // c[ci] is not inside d
		if( e != lit_Undef ) { // there has already been another different literal!
		  failed = true; break;
		} else { // this is the first time we have a different literal
		  e = c[ci];
		}
		ci ++;
	      } else if( d[di] < c[ci] ) {
		di ++; // literal d[di] is not in c[ci] ... not a problem!
	      }
	    }
	    if( config.opt_la_debug )  cerr << "c intermediate comparison: " << c << "[" << ci << "] and " << d << "[" << di << "], failed: " << failed << " lit e: " << e << endl;
	    
	    if( ci < c.size() ) // all literals inside di have to be consumed already here to make the above loop abort!
	    {
	      if( ci + 1 < c.size() || e != lit_Undef ) failed = true; // cannot extend with two literals!
	      else e = c[ci] ; // the remaining literal is the extension literal!
	    }
	    
	    if( !failed && e != lit_Undef ) { // can add literal ~e to clause d!
	      modifiedFormula = true;
	      alaExtensions ++;
	      data.lits.clear();
	      for( int k = 0 ; k < d.size(); ++ k) data.lits.push_back(d[k]);
	      data.lits.push_back( ~e );
	      if( config.opt_la_debug ) cerr << "c ALA with clause " << c << " turns " << d << " into " << data.lits << endl;
	      d.set_delete(true); // "remove" old clause
	      CRef cr = ca.alloc(data.lits, false ); // do not work on learnt clauses!
	      ca[cr].sort();
	      data.addClause( cr );
	      data.getClauses().push(cr);
	    }

	  }

	}
      // perform garbage collection
      data.checkGarbage();  
    }
  
  } while ( nextRoundLits.size() > 0 && (data.unlimited() || config.alaLimit > alaSteps) && !data.isInterupted() ); // repeat until all literals have been seen until a fixed point is reached!

  
  if( config.opt_la_debug ) {
    cerr << "c after ALA formula" << endl;
    for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	cerr << "(" << i << ") (" << data.getClauses()[i] << ")" ;
	if( ca[data.getClauses()[i]].mark() != 0 ) cerr << " (ign) ";
	if( ca[data.getClauses()[i]].can_be_deleted() != 0 ) cerr << " (del) ";
	cerr << " " << ca[ data.getClauses()[i] ] << endl;
      }
  }
  
}

  
void LiteralAddition::coverdLiteralAddition()
{
  MethodClock mc (claTime);
  LitOrderLAHeapLt comp(data, config.orderComplements); // use this sort criteria!
  Heap<LitOrderLAHeapLt> laHeap(comp);  // heap that stores the variables according to their frequency
  
  // setup own structures
  laHeap.addNewElement(data.nVars() * 2); // set up storage, does not add the element
  laHeap.clear();

  if( config.opt_la_debug ) {
    cerr << "c before CLA formula" << endl;
    for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	cerr << "(" << i << ") (" << data.getClauses()[i] << ")" ;
	if( ca[data.getClauses()[i]].mark() != 0 ) cerr << " (ign) ";
	if( ca[data.getClauses()[i]].can_be_deleted() != 0 ) cerr << " (del) ";
	cerr << " " << ca[ data.getClauses()[i] ] << endl;
      }
  }

  MarkArray nextRound;
  vector<Lit> nextRoundLits;
  nextRound.create(2*data.nVars());
  
  // init
  for( Var v = 0 ; v < data.nVars(); ++ v )
  {
    if( data.doNotTouch(v) ) continue; // do not consider variables that have to stay fixed!
    if( data[  mkLit(v,false) ] > 0 ) if( !laHeap.inHeap(toInt(mkLit(v,false))) )  nextRoundLits.push_back( mkLit(v,false) );
    if( data[  mkLit(v,true)  ] > 0 ) if( !laHeap.inHeap(toInt(mkLit(v,true))) )   nextRoundLits.push_back( mkLit(v,true) );
  }
  data.ma.resize(2*data.nVars());
  data.ma.nextStep();

  int iterations = 0;
  do {
    
    if ( iterations >= config.claIterations ) break; // stop here!
    iterations ++;

    // re-init heap
    for( int i = 0 ; i < nextRoundLits.size(); ++ i ) {
      const Lit l = nextRoundLits[i];
      assert( !laHeap.inHeap(toInt(l)) && "literal should not be in the heap already!" );
      laHeap.insert( toInt(l) );
    }
    nextRoundLits.clear();
    nextRound.nextStep();
    
    
    // do LiteralAddition on all the literals of the heap
    while (laHeap.size() > 0 && (data.unlimited() || config.claLimit > claSteps) && !data.isInterupted() )
    {
	// interupted ?
	if( data.isInterupted() ) break;
	  
	const Lit right = toLit(laHeap[0]);
	assert( laHeap.inHeap( toInt(right) ) && "item from the heap has to be on the heap");
	laHeap.removeMin();
	  
	if( data.doNotTouch(var(right)) ) continue; // do not consider variables that have to stay fixed!

	claTestedLits++; // count number of literals that have been tested for BCE
	// check whether a clause is a tautology wrt. the other clauses
	const Lit left = ~right; // complement
	if( config.opt_la_debug ) cerr << "c CLA work on literal " << right << " with " << data.list(right).size() << " clauses " << endl;
	data.lits.clear(); // used for covered literal elimination
	const int listSize = data.list(right).size(); // do not process the newly generated clause here as well!
	for( int i = 0 ; i < listSize; ++ i ) 
	{
	  Clause& c = ca[ data.list(right)[i] ];
	  if( c.can_be_deleted() ) continue; // do not work on uninteresting clauses!
	  
	  int rightOcc = data.list(right).size();
	  bool isLeastFrequent = true;
	  for( int k = 0 ; k < c.size(); ++ k ) {
	    if( data.list( c[k] ).size() < rightOcc ) {
	      isLeastFrequent = false; break;
	    }
	  }
	  if( !isLeastFrequent ) continue; // do not work with this clause on that literal, because its not among the least frequent literals!
	  
	  data.lits.clear(); // collect the literals that could be added by CLA
	  
	  bool canCla = false; // yet, no resolvent has been produced -> cannot perform CLA
	  for( int j = 0 ; j < data.list(left).size(); ++ j )
	  {
	    Clause& d = ca[ data.list(left)[j] ];
	    if( d.can_be_deleted() ) continue; // do not work on uninteresting clauses!
	    claSteps ++;
	    if( ! tautologicResolvent( c,d,right ) ) {
	      if( !canCla ) { // simply copy all literals from d except right into data.lits
		for( int k = 0 ; k < d.size(); ++ k ) {
		  if(d[k] != left) data.lits.push_back( d[k] );
		}
		canCla = true; // remember that we added some literals
	      } else {
		// build intersection of data.lits and d
		data.ma.nextStep();
		for( int k = 0 ; k < d.size(); ++ k ) data.ma.setCurrentStep( toInt(d[k]) ); // mark all literals of this clause
		// keep literals, that occurred before, and in this clause d
		int keptCle = 0;
		for( int k = 0 ; k < data.lits.size(); ++ k ) {
		  if( data.ma.isCurrentStep( toInt(data.lits[k]) ) ) {
		    data.lits[ keptCle++ ] = data.lits[k];
		  }
		}
		data.lits.resize( keptCle ); // remove all the other literals
		// if intersection is empty, drop the clause!
		if( data.lits.size() == 0 ) break;
	      }
	    } else {
	      // tautologic resolvent, nothing special here! 
	    }
	  }
	  
	  if( data.lits.size() > 0 && canCla ) { // there is something to be added for the clause c!
	    // add all literals of c to data.lits, sort, add as clause
	    data.ma.nextStep();
	    
	    const int oldPossibleClaExtensions = possibleClaExtensions;
	    possibleClaExtensions += data.lits.size();
	    
	    // have a filter here that removes some of the literals, if data.lits is too large!
	    if( data.lits.size() > config.claStepSize ) { // reduce number of literals somehow
	      int keptLiterals = 0;
	      for( int k = 0 ; k < data.lits.size(); k++) {
		if( rand() % 1000 < 600 ) { // keep some 60 %
		  data.lits[keptLiterals++] = data.lits[k];
		}
	      }
	      if( keptLiterals > config.claStepMax ) keptLiterals = config.claStepMax; // cut off the remaining literals
	      if( keptLiterals == 0 ) { // have at least one literal!
		data.lits[0] = data.lits[ rand() % data.lits.size() ]; // select one randomly!
		keptLiterals = 1;
	      }
	      data.lits.resize( keptLiterals );
	    }
	    
	    
	    for( int k = 0 ; k < data.lits.size(); k++) data.ma.setCurrentStep( toInt(data.lits[k]) );
	    const int oldClaExtensions = claExtensions;
	    claExtensions += data.lits.size(); // size of extension
	    bool isTaut = false;
	    for( int k = 0 ; k < c.size(); k++) {
	      if( data.ma.isCurrentStep( toInt( ~c[k] ) ) )
	      {
		isTaut = true;
		data.lits.push_back( c[k] );
	      } else if ( !data.ma.isCurrentStep( toInt( c[k] ) ) ) {
		data.lits.push_back( c[k] );
	      }
	    }
	    
	    if( !isTaut ) { // do not want to perform CCE here!
	      claExtendedClauses ++;
	      CRef newClause = ca.alloc(data.lits,false); // destroys reference for clause c!
	      ca[ newClause ].sort();
	    
	      // add new clause to proof (subsumed by the other, so should be fine!)
	      ca[ data.list(right)[i] ].set_delete(true);
	      data.addCommentToProof("extended by applying CLA");
	      data.addToProof( ca[ newClause ] ); // add the new longer clause!
	      data.addToProof( ca[ data.list(right)[i] ] ,true); // delete this clause from the proof!
	      // add old clause to extension stack
	      data.addToExtension( data.list(right)[i], right );
	      // remove old clause, since it should not subsume the other clause!
	      if( config.opt_la_debug ) cerr << "c CLA turned clause " << ca[ data.list(right)[i] ] << " into the new clause " << ca[newClause] << endl;
	      // add new clause
	      data.addClause( newClause );
	      data.getClauses().push( newClause );
	      
	      // set up the next iteration!
	      const Clause & e = ca[ newClause ]; // all literals in the new clause increased the size of the possible resolvents
	      for( int k = 0 ; k < e.size(); ++ k ) {
		if( !nextRound.isCurrentStep( toInt(e[k])) ) {
		  nextRound.setCurrentStep( toInt(e[k]) );
		  nextRoundLits.push_back( e[k] );
		}
	      }
	      
	    } else {
	      claExtensions = oldClaExtensions; // undo calculation
	      possibleClaExtensions = oldPossibleClaExtensions;
	      // CCE could be applied!
	    }
	  }
	}

      // perform garbage collection
      data.checkGarbage();  
	
    }
  
  } while ( nextRoundLits.size() > 0 && (data.unlimited() || config.claLimit > claSteps) && !data.isInterupted() ); // repeat until all literals have been seen until a fixed point is reached!

  
  if( config.opt_la_debug ) {
    cerr << "c after CLA formula" << endl;
    for( int i = 0 ; i < data.getClauses().size(); ++ i ) {
	cerr << "(" << i << ") (" << data.getClauses()[i] << ")" ;
	if( ca[data.getClauses()[i]].mark() != 0 ) cerr << " (ign) ";
	if( ca[data.getClauses()[i]].can_be_deleted() != 0 ) cerr << " (del) ";
	cerr << " " << ca[ data.getClauses()[i] ] << endl;
      }
  }
  
}

  
bool LiteralAddition::process()
{
  assert( (config.opt_la_cla || config.opt_la_ala ) && "something should be done in this method!" );
  
  MethodClock mc (laTime);
  
  if( ! performSimplification() ) return false; // do not do anything?!
  modifiedFormula = false;
  
  // do not simplify, if the formula is considered to be too large!
  if( !data.unlimited() && ( data.nVars() > config.opt_la_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_la_cls && data.nTotLits() > config.opt_la_lits) ) return false;

  // run UP first!
  if( config.opt_la_debug ) cerr << "c LA run unit propagation" << endl;
  propagation.process(data, true); // propagate, if there's something to be propagated
  modifiedFormula = modifiedFormula  || propagation.appliedSomething();
  if( !data.ok() ) return modifiedFormula;
  
  if( config.opt_la_cla ) coverdLiteralAddition();
  if( config.opt_la_ala ) asymemtricLiteralAddition();
    
  // run BCE here again to remove the new blocked clauses, if there have been any!
  return modifiedFormula;
}
    
bool LiteralAddition::tautologicResolvent(const Clause& c, const Clause& d, const Lit l)
{
  int i = 0, j = 0;
  while ( i < c.size() && j < d.size() ) 
  {
    if( c[i] == l ) { // skip this literal!
      i++;
    } else if( d[j] == ~l ) { // skip this literal!
      j++;
    } else if( c[i] == d[j] ) { // same literal
      i++; j++;
    } else if( c[i] == ~d[j] ) { // complementary literal -> tautology!
      return true; 
    } else if( c[i] < d[j] ) {
      i++;
    } else if( d[j] < c[i]  ) {
      j ++;
    }
  }
  return false; // a complementarly literal was not found in both clauses
}
    
    
void LiteralAddition::printStatistics(ostream& stream)
{
  cerr << "c [STAT] CLA " << claTime.getCpuTime() << " seconds, " << claSteps << " steps, " << claTestedLits << " testLits, " << claExtendedClauses << " extClss, " << claExtensions << " extLits, " << possibleClaExtensions << " possibles, " << endl;
  cerr << "c [STAT] ALA " << alaTime.getCpuTime() << " seconds, " << alaSteps << " steps, " << alaTestedLits << " testLits, " << alaExtensions << " extensions, " << endl;
}

void LiteralAddition::giveMoreSteps()
{
  claSteps = claSteps < config.opt_bceInpStepInc ? 0 : claSteps - config.opt_bceInpStepInc;
}
  
void LiteralAddition::destroy()
{
  
}