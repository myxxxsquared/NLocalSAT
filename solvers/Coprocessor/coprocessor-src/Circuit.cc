/**************************************************************************************[Circuit.cc]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Circuit.h"


using namespace Coprocessor;

Circuit::Circuit(CP3Config& _config, ClauseAllocator& _ca)
: config( _config), ca (_ca), big(0)
{}

void Circuit::extractGates(CoprocessorData& data, vector< Gate >& gates)
{
  // create BIG
  if( big != 0 ) delete big;
  big = new BIG( );
  big->create(ca,data.nVars(),data.getClauses(),data.getLEarnts());
  
  if( config.circ_Implied ) big->generateImplied(data);
  
  if( config.circ_debug_out ) {
    cerr << "c sampled BIG:" << endl;
    for( Var v =  0 ; v < data.nVars(); ++ v ) {
      for ( int p = 0 ; p < 2; ++ p ) {
	const Lit l = mkLit( v, p==1 );
	cerr << "c " << l << "  [" << big->getStart(l) << ", " << big->getStop(l) << "]" << endl;
      }
    }
    for( Var v =  0 ; v < data.nVars(); ++ v ) {
      for ( int p = 0 ; p < 2; ++ p ) {
	const Lit l = mkLit( v, p==1 );
	cerr << "c " << l << " -> ";
	for( int i = 0 ; i < big->getSize(l); ++ i ) cerr << " " << big->getArray(l)[i] ;
	cerr << endl;
      }
    }
  }
  
  // create the list of all ternary / quadrary clauses
  ternaries.resize( data.nVars() * 2 );
  quads.resize( data.nVars() * 2 );
  for ( int v = 0 ; v < 2*data.nVars(); ++v )
  {
    ternaries[v].clear();
    quads[v].clear();
  }
  for ( int p = 0 ; p < 2; ++ p ) {
    vec<CRef>& list = p == 0 ? data.getClauses() : data.getLEarnts() ;
    for( int i = 0 ; i < list.size(); ++ i ) {
      const Clause& c = ca[ list[i] ];
      if( c.can_be_deleted() ) continue;
      if( c.size() ==3 ) {
	for( int j = 0 ; j < 3; ++ j )
	  ternaries[ toInt(c[j]) ].push_back( ternary(j==0 ? c[2] : c[0] ,
                                                      j==1 ? c[2] : c[1]) );
      } else if (c.size() == 4 ) {
	for( int j = 0 ; j < 4; ++ j ) 
	  quads[ toInt(c[j]) ].push_back( quad( j == 0 ? c[3] : c[0],
						 j == 1 ? c[3] : c[1],
					         j == 2 ? c[3] : c[2]) );
      }
    }
  }
  
  // try to find all gates with output variable v for all the variables  
  for ( Var v = 0 ; v < data.nVars(); ++v )
    getGatesWithOutput(v,gates, data);
}

void Circuit::getGatesWithOutput(const Var v, vector< Circuit::Gate >& gates, CoprocessorData& data)
{
//   cerr << "check gates for variable " << v << endl;
  data.ma.resize(2*data.nVars());

  if( config.circ_AND ) getANDGates(v,gates, data);
  if( config.circ_ITE ) getITEGates(v,gates, data);
  if( config.circ_XOR ) getXORGates(v,gates, data);

  if( config.circ_ExO) getExOGates(v,gates, data);
  if( config.circ_FASUM ) getFASUMGates(v,gates, data);
  if( config.circ_debug_out ) cerr << "c after variable " << v+1 << " found " << gates.size() << " gates" << endl;
}

void Circuit::getANDGates(const Var v, vector< Circuit::Gate >& gates, CoprocessorData& data)
{
  if( config.circ_debug_out ) cerr << "c try to find AND gate for variable " <<  v + 1 <<  " (found so far:" << gates.size() << ")[ok?: " << data.ok() << "]" << endl;
  vec<Lit> learnt_clause;
  // check for v <-> A and B
  // cerr << "c check AND gates with variable " << v+1 << endl;
  for( int p = 0; p < 2 ; ++ p ) {
    data.ma.nextStep();
    data.lits.clear();
    Lit pos = mkLit( v, p == 1 ); // pos -> a AND b AND ... => binary clauses [-pos, a],[-pos,b], ...
    if( config.circ_debug_out ) cerr << "c with lit " << pos << endl;
    Lit* list = big->getArray(pos);
    const int listSize = big->getSize(pos);
    data.ma.setCurrentStep( toInt(~pos) ); 
    if( config.circ_debug_out ) cerr << "c mark literal " << ~pos << endl;
    // find all binary clauses for gate with positive output "pos"
    for( int i = 0 ; i < listSize; ++i ) {
     data.ma.setCurrentStep( toInt(list[i]) ); 
     data.lits.push_back( list[i] );
     if( config.circ_debug_out ) cerr << "c mark literal " << list[i] << endl;
    }
    if( data.lits.size() > 1 ) { // work on found binary clauses!

    // TODO: do not do blocked clause addition here, but only if all the other techniques did not reveal the BCA-gate
    bool foundBlockedCandidate = false;
      if( config.circ_genAND ) {
	// cerr << "c genMethod" << endl;
	const vector<CRef>& cList = data.list(pos);  // all clauses C with pos \in C
	for( int i = 0 ; i < cList.size(); ++i ) {   // there can be multiple full encoded gates per variable
	  const Clause& c = ca[ cList[i] ];
	  if( c.can_be_deleted() || c.size () < 3 || c.size() > data.lits.size()+1 ) continue; // new clauses that provide not too much literals
	  if( config.circ_debug_out ) cerr << "c consider clause " << c << endl;
	  int marked = 0;
	  for ( int j = 0 ; j < c.size(); ++j ) 
	    if( data.ma.isCurrentStep( toInt(~c[j]) )) {
	      marked ++; // check whether all literals inside the clause are marked
	      if( config.circ_debug_out ) cerr << "c hit literal " << ~c[j] << endl;
	    }
	    else if ( big->implies( pos, ~c[j] ) ) { 
	      marked ++;  
	      if( config.circ_debug_out ) cerr << "c imply literal " << pos << " -> "  << ~c[j] << endl;
	    }
	    else {
	  //    cerr << "literal " << ~c[j] << " is not marked, and literal " << c[j] << " is not implied by literal " << pos << endl;
	      break;
	    }
	  if( marked == c.size() ) {
	    gates.push_back( Gate( c, c.size() == 3 ? Gate::AND : Gate::GenAND, Gate::FULL, pos ) ); // add the gate
	    if( config.circ_debug_out ) {
	      cerr << "c found FULL AND gate with output var " << v + 1 << endl; 
	      cerr << "clause " << c << " leads to gate: ";
	      gates[ gates.size() -1 ].print(cerr);
	    }
	    data.log.log( 1, "clause for gate" ,c );
	    if( marked == data.lits.size() ) foundBlockedCandidate = true;
	  } else {
	    //cerr << "c marked=" << marked << " while size is " << c.size() << endl;
	  }
	}
      } else {
	//cerr << "c ternary method" << endl;
	const vector<ternary>& cList = ternaries[ toInt(pos) ]; // all clauses C with pos \in C
	for( int i = 0 ; i < cList.size(); ++i ) {  // there can be multiple gates per variable
	  const ternary& c = cList[i];
	  // cerr << "consider clause [" << pos << ", " << c.l1 << ", " << c.l2 << "]" << endl;
	  // either, literal is marked (and thus in binary list), or its implied wrt. sampled BIG
	  if( ( data.ma.isCurrentStep(toInt(~c.l1)) || big->implies(pos, ~c.l1 ) ) // since implied does not always work, also check alternative!
	    &&( data.ma.isCurrentStep(toInt(~c.l2)) || big->implies(pos, ~c.l2 ) ) ){
	    gates.push_back( Gate( pos, c.l1, c.l2, Gate::AND, Gate::FULL) ); // add the gate
	    if( config.circ_debug_out ) { 
	      cerr << "c found FULL ternary only AND gate with output var " << v + 1 << endl;
	      cerr << " implied: " << pos << " -> " << c.l1 << " : " << big->implies(pos, ~c.l1 ) << endl; 
	      cerr << " implied: " << pos << " -> " << c.l2 << " : " << big->implies(pos, ~c.l2 ) << endl; 
	      cerr << "clause [" << pos << "," << c.l1 << "," << c.l2 << "] leads to gate: ";
	      gates[ gates.size() -1 ].print(cerr);
	    }
	    if( data.lits.size() == 2 ) foundBlockedCandidate = true;
	  }
	}
      }
      if( ! foundBlockedCandidate && config.circ_BLOCKED ) {
	if( data.lits.size() > 2 && ! config.circ_genAND ) continue;
	int presentClauses = 0;
	for( int j = 0 ; j < data.list(~pos).size(); ++ j ) {
	  const Clause& c = ca[ data.list(~pos)[j] ];
	  if( c.can_be_deleted() ) continue;
	  if( c.size() != 2 ) { presentClauses = -1; break; }
	  presentClauses ++;
	}
	if( presentClauses == data.lits.size() ) // all clauses with ~pos are binary and define one half of the gate!
	{ // all occurrences in binary clauses!
	  if( config.circ_AddBlocked ) {
	    learnt_clause.clear();
	    for( int j = 0 ; j < data.lits.size(); ++ j )
	      learnt_clause.push( ~data.lits[j] );
	    learnt_clause.push( pos );
	    if( !config.circ_genAND ) { assert( learnt_clause.size() == 3 && "only binary and-gates are allowed" ); }
	    // todo: have method to add new clause!
            if( learnt_clause.size() == 3 ) { // push ternaries!
	      ternaries[ toInt(learnt_clause[0]) ].push_back(ternary (learnt_clause[1],learnt_clause[2]));
	      ternaries[ toInt(learnt_clause[1]) ].push_back(ternary (learnt_clause[0],learnt_clause[2]));
	      ternaries[ toInt(learnt_clause[2]) ].push_back(ternary (learnt_clause[0],learnt_clause[1]));
	    } else if( learnt_clause.size() == 4 ) { // push quads
	      cerr << "c ADDING QUADS IS NOT PROPERLY IMPLEMENTED YET!!" << endl;
	      continue;
	    }
	    // if this code is reached, then the gate can be added, and blocked clause addition has been executed properly!
	    gates.push_back( Gate(data.lits, (data.lits.size() == 2 ? Gate::AND : Gate::GenAND), Gate::POS_BLOCKED, pos) );
	    if( config.circ_debug_out ) {
	      cerr << "c found posBlocked AND gate with output var " << v + 1 << endl;
	      cerr << "clause [";
	      for( int abc = 0; abc < learnt_clause.size(); ++ abc ) cerr << learnt_clause[abc] << " ";
	      cerr << "] leads to gate: ";
	      gates[ gates.size() -1 ].print(cerr);
	    }
	    CRef cr = ca.alloc(learnt_clause, false); // create as learnt clause (theses clauses have to be considered for inprocessing as well, see "inprocessing rules" paper!
	    data.addClause(cr);
	    data.getClauses().push(cr);
	    
	    if( learnt_clause.size() == 3 ) {
	      ternaries[ toInt(learnt_clause[0]) ].push_back( ternary(learnt_clause[1],learnt_clause[2]) );
	      ternaries[ toInt(learnt_clause[1]) ].push_back( ternary(learnt_clause[0],learnt_clause[2]) );
	      ternaries[ toInt(learnt_clause[2]) ].push_back( ternary(learnt_clause[0],learnt_clause[1]) );
	    }
	    // TODO: add ternary clause to ternaries!
	  }
	}
      }
    // only look for blocked if enabled, and for more than ternary, if enabled
    } else if(config.circ_BLOCKED && (! config.circ_genAND || data.lits.size() == 2 )) { // handle case where all binary clauses are blocked (and removed) and only the large clause is present
      // [a,-b,-c],[-a,b],[-a,c] : binary clauses are blocked if there is no other occurrence with positive a!!
      int count = 0;
      for( int i = 0 ; i < data.list(pos).size(); ++i ) 
	count = ( ca[ data.list(pos)[i] ].can_be_deleted() ? count : count + 1 );
      if( count == 1 ) {
	if( config.circ_debug_out ) cerr << "c BLOCKED Generic Gates IS NOT PROPERLY IMPLEMENTED YET!!" << endl;
	continue;
	// TODO: if blocked clause addition is performed with binary clauses, the BIG has to be updated!
	gates.push_back( Gate( data.lits, data.lits.size() == 2 ? Gate::AND : Gate::GenAND, Gate::NEG_BLOCKED, pos ) );
	if( config.circ_debug_out ) cerr << "c found NEG_BLOCKED AND gate with output var " << v + 1 << endl; 
        if( config.circ_AddBlocked ) {
	  // be careful with the clauses that have to be added! this will change the BIG!    
        }
      }
    }
  } // end pos/neg for loop
}

void Circuit::getExOGates(const Var v, vector< Circuit::Gate >& gates, CoprocessorData& data)
{
  for( int p = 0; p < 2 ; ++ p ) {
    Lit pos = mkLit( v, p == 1 );
    vector<CRef>& list = data.list(pos);
    for( int i = 0 ; i < list.size(); ++ i ) {
      const Clause& c = ca[list[i]]; 
      if( c.can_be_deleted() || c.size() == 2 ) continue;
      data.ma.nextStep();
      bool cont = false;
      for( int j = 0 ; j < c.size() ; ++ j ) {
	if( var(c[j]) < v ) { cont = true; break; } // not smallest variable in this clause!
	data.ma.setCurrentStep( toInt( ~c[j] ) );
      }
      if( cont ) continue;
      
      if( config.circ_BLOCKED )
      {
	// for each variable this clause is the only positive occurrence!
	bool found = true;
	int count = 0 ;
	for( int j = 0 ; j < c.size(); ++ j ) {
	  const Lit&l = c[j];
	  vector<CRef>& lList = data.list(l);
	  count = 0 ;
	  for( int k = 0 ; k < lList.size(); ++ k ) {
	    const Clause& ck = ca[lList[k]];
	    if( ck.can_be_deleted() ) continue;
	    if ( count ++ == 2 || lList[k] != list[i] ) // not the current clause, or more than one clause
	      { found = false; break; }
	  }
	  assert( (!found || count == 1) && "if for the current literal the situation for blocked has been found, one clause has been found" );
	}
	if( found ) {
	  gates.push_back( Gate( c, Gate::ExO, Gate::NEG_BLOCKED ) );
	}
	
      }
      
      bool found = true;
      for( int j = 0 ; j < c.size() ; ++ j ) {
	const Lit& l = c[j];
	const Lit* lList = big->getArray(l);
	const int lListSize = big->getSize(l);
	int count = 0;
	for( int k = 0 ; k < lListSize; ++ k )
	  count = (data.ma.isCurrentStep( toInt(lList[k]) ) || big->implies(l, lList[k]) ) ? count+1 : count;
	if( count + 1 < c.size() ) { found = false; break; } // not all literals can be found by this literal!
      }
      if( !found ) continue;
      else gates.push_back( Gate( c, Gate::ExO, Gate::FULL ) );
    }
    
    if( !config.circ_BLOCKED ) continue;
    // check whether the binary clauses of this variable produce another blocked gate
    Lit * pList = big->getArray(pos);
    const int pListSize = big->getSize(pos);
    data.lits.clear(); // will be filled with all the literals that form an amo with pos
    data.lits.push_back( ~pos );
    for( int j = 0 ; j < pListSize; ++ j )
      data.lits.push_back( pList[j] );
    for( int j = 0 ; j < data.lits.size(); ++ j )
    {
      const Lit l = data.lits[j];
      data.ma.nextStep();
      Lit * lList = big->getArray(~l);
      const int lListSize = big->getSize(~l);
      data.ma.setCurrentStep( toInt(l) ); // mark all literals that are implied by l
      for( int k = 0 ; k < lListSize; ++ k )
        data.ma.setCurrentStep( toInt(lList[k]) );
      int kept = 0;         // store number of kept elements
      int continueHere = 0; // store where to proceed
      for( int k = 0 ; k < data.lits.size(); ++ k ){
	const Lit dl = data.lits[k];
	if( data.ma.isCurrentStep( toInt(dl) ) 
	  || big->implies(l,dl) ) { // check, if the current literal is marked, or if its implied via BIG
	  continueHere = dl == l ? kept : continueHere; 
	  data.lits[kept++] = data.lits[k];
	} else {
	  // cerr << "c did not find " << dl << " in list of " << ~l << endl; 
	}
      }
      data.lits.resize(kept); // keep only the elements that are still marked!
      j = continueHere;       // ++j from for loop is still called
    }
    // check smallest criterion:
    for( int j = 0 ; j < data.lits.size(); ++ j )
      if( var(data.lits[j]) < v ) { data.lits.clear(); break; }
    if( data.lits.size() < 3 )  continue; // only consider clauses with more literals!
    // check whether for each literal there are only these occurrences of binary clauses in the formula
    bool found = true;
    int count = 0;
    for( int j = 0 ; j < data.lits.size(); ++ j )
    {
      const Lit& l = data.lits[j];
      vector<CRef>& lList = data.list(l);
      count = 0 ;
      for( int k = 0 ; k < lList.size(); ++ k ) {
	const Clause& ck = ca[lList[k]];
	if( ck.can_be_deleted() ) continue;
	if ( count ++ == data.lits.size() || ck.size() != 2 ) // not the current clause, or more than one clause
	  { found = false; break; }
      }
      // count has to be data.lits.size(), otherwise data structures are invalid!
      assert( (!found || count + 1== data.lits.size()) && "if for the current literal the situation for blocked has been found, exactly the n binary clauses have to be found!" );
    }
    if( found ) {
      for( int j = 0 ; j < data.lits.size() ; j++ ) data.lits[j] = ~data.lits[j];
      gates.push_back( Gate( data.lits, Gate::ExO, Gate::POS_BLOCKED ) );
    }
  }
}


void Circuit::getFASUMGates(const Var v, vector< Circuit::Gate >& gates, CoprocessorData& data)
{
// clauses to look for:
//    a  b  c  d == 0
//   -a -b  c  d == 1
//   -a  b -c  d == 2
//    a -b -c  d == 3
//   -a  b  c -d == 4
//    a -b  c -d == 5
//    a  b -c -d == 6
//   -a -b -c -d == 7
  int oldGates = gates.size();
  // check for v <-> ITE( s,t,f )
  for( int p = 0; p < 2 ; ++ p ) {
    Lit a = mkLit( v, p == 1 ); // XOR(a,b,c) = 1
    const vector<quad>& cList = quads[ toInt(a) ]; // all clauses C with pos \in C
    bool found [8]; found[0] = true; // found first clause!
    for( int i = 0 ; i < cList.size(); ++ i ) 
    {
      if( config.circ_debug_out ) cerr << "c check quad " << i << "/" << cList.size() << endl;
      const quad& current = cList[i];
      // check size occurrence:
      if( var(current.l1) < var(a) || var(current.l2) < var(a) || var(current.l3) < var(a) ) continue; // do not consider this order of this quad!
      // reset
      for( int j = 1; j < 8; ++j ) found [j] = false;
      // scan for the clauses!
      const Lit b = current.l1; const Lit c = current.l2; const Lit d = current.l3;
      // check all binary clauses!
      if( big->isChild( a, d) || big->implies( a, d) ) { found[1] = found[2] = true; }
      if( big->isChild( a,~d) || big->implies( a,~d) ) { found[4] = found[7] = true; }
      if( big->isChild(~a, d) || big->implies(~a, d) ) { found[3] = true; } // part of the initial quadrary!
      if( big->isChild(~a,~d) || big->implies(~a,~d) ) { found[5] = found[6] = true; }
      if( big->isChild( a, c) || big->implies( a, c) ) { found[1] = found[4] = true; }
      if( big->isChild( a,~c) || big->implies( a,~c) ) { found[2] = found[7] = true; }
      if( big->isChild(~a, c) || big->implies(~a, c) ) { found[5] = true; } // part of the initial quadrary!
      if( big->isChild(~a,~c) || big->implies(~a,~c) ) { found[3] = found[6] = true; }
      if( big->isChild( a, b) || big->implies( a, b) ) { found[2] = found[4] = true; }
      if( big->isChild( a,~b) || big->implies( a,~b) ) { found[1] = found[7] = true; }
      if( big->isChild(~a, b) || big->implies(~a, b) ) { found[6] = true; } // part of the initial quadrary!
      if( big->isChild(~a,~b) || big->implies(~a,~b) ) { found[3] = found[5] = true; }      
      if( big->isChild( b, d) || big->implies( b, d) ) { found[1] = found[3] = true; }
      if( big->isChild( b,~d) || big->implies( b,~d) ) { found[5] = found[7] = true; }
      if( big->isChild(~b, d) || big->implies(~b, d) ) { found[2] = true; } // part of the initial quadrary!
      if( big->isChild(~b,~d) || big->implies(~b,~d) ) { found[4] = found[6] = true; }      
      if( big->isChild( b, c) || big->implies( b, c) ) { found[1] = found[5] = true; }
      if( big->isChild( b,~c) || big->implies( b,~c) ) { found[3] = found[7] = true; }
      if( big->isChild(~b, c) || big->implies(~b, c) ) { found[4] = true; } // part of the initial quadrary!
      if( big->isChild(~b,~c) || big->implies(~b,~c) ) { found[2] = found[6] = true; }      
      if( big->isChild( c, d) || big->implies( c, d) ) { found[2] = found[3] = true; }
      if( big->isChild( c,~d) || big->implies( c,~d) ) { found[6] = found[7] = true; }
      if( big->isChild(~c, d) || big->implies(~c, d) ) { found[1] = true; } // part of the initial quadrary!
      if( big->isChild(~c,~d) || big->implies(~c,~d) ) { found[4] = found[5] = true; }      
      if( config.circ_debug_out ) cerr << "c finished binaries" << endl;
      // gates that have not been found are looked for via ternary and if not succesful via quadrary
      Lit lits[4];
      for( int j = 1; j < 8; ++ j ) {
	if( found[j] == true ) continue; // already found this clause!
	switch(j) { // setup literals to look for
	  case 1: lits[0] = ~a; lits[1] = ~b; lits[2] =  c; lits[3] =  d; break;
	  case 2: lits[0] = ~a; lits[1] =  b; lits[2] = ~c; lits[3] =  d; break;
	  case 3: lits[0] =  a; lits[1] = ~b; lits[2] = ~c; lits[3] =  d; break;
	  case 4: lits[0] = ~a; lits[1] =  b; lits[2] =  c; lits[3] = ~d; break;
	  case 5: lits[0] =  a; lits[1] = ~b; lits[2] =  c; lits[3] = ~d; break;
	  case 6: lits[0] =  a; lits[1] =  b; lits[2] = ~c; lits[3] = ~d; break;
	  case 7: lits[0] = ~a; lits[1] = ~b; lits[2] = ~c; lits[3] = ~d; break;
	}
	if( config.circ_debug_out ) cerr << "c try to find quad: [" << lits[0] << ", " << lits[1] << ", " << lits[2] << ", " << lits[3] << "]" << endl;
	for( int ind = 0; ind < 2; ++ ind ) { // index of literal to iterate over
	  const vector<ternary>& tList = ternaries[ toInt(lits[0]) ]; // all clauses C with pos \in C
	  for( int ti = 0 ; ti < tList.size(); ++ ti ) 
	  {
	    const ternary tern = tList[ti];
	    if( config.circ_debug_out ) cerr << "c check with ternaries of lit " << lits[0] << " : " << ti << "/" << tList.size() << " [" << lits[0] << "," << tern.l1 << "," << tern.l2 << "]"<< endl;
	    if( tern.l1 == lits[1] && (tern.l2 == lits[2] || tern.l2 == lits[3] ) ) { found[j] = true; goto HASUMnextJ; }
	    if( tern.l1 == lits[2] && (tern.l2 == lits[1] || tern.l2 == lits[3] ) ) { found[j] = true; goto HASUMnextJ; }
	    if( tern.l1 == lits[3] && (tern.l2 == lits[2] || tern.l2 == lits[1] ) ) { found[j] = true; goto HASUMnextJ; }
	  }
          // done? swap!
          const Lit tmp = lits[0]; lits[0] = lits[1]; lits[1] = tmp;
	}
	// swap back in case the ternary attempt failed
	{
	  const vector<quad>& qList = quads[ toInt(lits[0]) ]; // all clauses C with pos \in C
	  for( int qi = 0 ; qi < qList.size(); ++ qi ) 
	  {
	    const quad& qQuad = qList[qi];
	    if( config.circ_debug_out ) cerr << "c check sub quad " << qi << "/" << qList.size() << ": " << qQuad.l1 << "," << qQuad.l2 << "," << qQuad.l3 << endl;
	    if( qQuad.l1 == lits[1] && qQuad.l2 == lits[2] && qQuad.l3 == lits[3] ) // since ordered, there can be only one candidate!
	      { found[j] = true; break; }
	  }
	}
HASUMnextJ:;
        if( found[j] && config.circ_debug_out ) cerr << "c found clause " << j << endl;
      }

      // if not all clauses found, check for blocked!
      
      // check whether current has been found!
      int count = 0;
      for( int j = 0 ; j < 8; ++ j ) if( found[j] ) count ++;
      
      if( config.circ_debug_out ) cerr << "c found " << count << " clauses" << endl;
      
      if( count < 4 ) continue; // need at least 4 clauses to have a chance for blocked!
      if( count == 8 ) { // found a full gate!
	data.lits.resize(4);
	data.lits[0] = a;data.lits[1] = b;data.lits[2] = c;data.lits[3] = d;
	gates.push_back( Gate(data.lits, Gate::FA_SUM, Gate::FULL) );
	continue;
      }
      
      if( config.circ_BLOCKED ) {
	if( config.circ_debug_out ) cerr << "c find blocked gate?" << endl;
	// depending on the found clauses, four block variants can occur -> select the right literal!
        Lit blockLit = lit_Undef ;
             if( found[0] && found[3] && found[5] && found[6] ) blockLit = a;
	else if( found[1] && found[2] && found[4] && found[7] ) blockLit = ~a;
	else if( found[0] && found[2] && found[4] && found[6] ) blockLit = b;
	else if( found[1] && found[3] && found[5] && found[7] ) blockLit = ~b;
	else if( found[0] && found[1] && found[4] && found[5] ) blockLit = c;
	else if( found[2] && found[3] && found[6] && found[7] ) blockLit = ~c;
	else if( found[0] && found[1] && found[2] && found[3] ) blockLit = d;
	else if( found[4] && found[5] && found[6] && found[7] ) blockLit = ~d;
	if( config.circ_debug_out ) cerr << "c block lit for gate: " << blockLit << endl;
	if( blockLit == lit_Undef ) continue; // no opportunity for blocking!

	// check whether the literal "blockLit" appears exactly four times in quad clauses, and not else!
	vector<CRef>& list = data.list(blockLit);
	int count = 0;
	for( int j = 0 ; j < list.size(); ++ j ) {
	  const Clause& c = ca[ list[j] ];
	  if( c.can_be_deleted() ) continue;
	  if( c.size() != 4 )  { count = 0; break; }
	  count ++;
	}
	
	if( count == 4 ) {
	  data.lits.resize(4);
	  data.lits[0] = a;data.lits[1] = b;data.lits[2] = c;data.lits[3] = d;
	  gates.push_back( Gate(data.lits, Gate::FA_SUM, found[0] ? Gate::NEG_BLOCKED : Gate::POS_BLOCKED) );
	}
      }
    }
      
  }
  
  // TODO remove redundant gates!
  for( int i = oldGates + 1; i < gates.size(); ++ i ) {
    for( int j = oldGates ; j < i; ++ j ) {
      // ordered -> only one comparison necessary
      if(  var(gates[i].x()) == var(gates[j].x())
	&& var(gates[i].a()) == var(gates[j].a()) 
	&& var(gates[i].b()) == var(gates[j].b()) 
	&& var(gates[i].c()) == var(gates[j].c()) )
      {
	// gates have same variables, check for same polarity. if true, kick later gate out!
	bool pol = sign( gates[i].a() ) ^ sign( gates[i].b() ) ^ sign( gates[i].c() ) ^ sign( gates[i].x() );
	if( pol == sign( gates[j].a() ) ^ sign( gates[j].b() ) ^ sign( gates[j].c() ) ^ sign( gates[j].x() ) )
	{ // gates are equivalent! XOR(a,b,c) with same polarity
	  gates[i] = gates[ gates.size() - 1 ];
	  gates.pop_back();
	  --i; break;
	} else {
	  if( config.circ_debug_out ) cerr << "c pair of unsatisfiable FASUM gates: " << endl;
	  gates[i].print(cerr);
	  gates[j].print(cerr);
	  data.setFailed();
	  return;
	  assert( false && "found a pair of gates that has to be unsatisfiable!" ); 
	}
      }
    }
  }
}

void Circuit::getITEGates(const Var v, vector< Circuit::Gate >& gates, CoprocessorData& data)
{
  // ITE(s,t,f) == ITE(-s,f,t) => scanning for these gates is simple
  
 // possible clauses:
 // -s,-t,x     s,-f,x    (red)-t,-f,x for positive
 // -s,t,-x     s,f,-x    (red)t,f,-x  for negative
 // reduced forms:
 // -s,-t,x       -f,x  // latter subsumes the above ternary clause -> ITE gate is entailed!
 // t,-s,-x       f,-x  // latter subsumes the above ternary clause -> ITE gate is entailed!
 //  
  int oldGates = gates.size();
  // check for v <-> ITE( s,t,f )
  for( int p = 0; p < 2 ; ++ p ) {
    data.ma.nextStep();
    Lit pos = mkLit( v, p == 1 ); // pos -> a AND b AND ... => binary clauses [-pos, a],[-pos,b], ...
    const vector<ternary>& cList = ternaries[ toInt(pos) ]; // all clauses C with pos \in C
    for( int i = 0 ; i < cList.size(); ++i ) {  // there can be multiple gates per variable
      data.lits.clear(); // will store the candidates for 'f'
      const ternary& c = cList[i]; // ternary has the variables X, S and T
      for( int posS = 0 ; posS < 2; posS ++ ) { // which of the other two literals is the selector?
	   Lit s = posS == 0 ? ~c.l1 : ~c.l2;
	   Lit t = posS == 0 ? ~c.l2 : ~c.l1;
	   Lit x = pos;
	   if( config.circ_debug_out ) cerr << "try to find ["<<i<<"] " << x << " <-> ITE( " << s << "," << t << ", ?)" << endl;
	   // TODO: continue here
	   // try to find f by first checking binary clauses, afterwards check ternary clauses!
	   // if allowed, also try to find by blocked!

	   data.ma.nextStep();
	   data.lits.clear();
	   // collect all other 'f' candidates in the ternary list!
	   for( int j = 0 ; j < cList.size(); ++ j ) {
	     if( i == j ) continue;
	     const ternary& cand = cList[j]; // ternary has the variables X, S and T
	     if( config.circ_debug_out ) cerr << "candidate ["<<j<<"] : [" << x << "," << cand.l1 << "," << cand.l2 << "]" << endl;
	     if( cand.l1 == s || cand.l2 == s ) {
	       Lit fCandidate = ~toLit(cand.l1.x ^ cand.l2.x ^ s.x);
	       bool sameVar = (var(fCandidate) == var(s)) || (var(fCandidate) == var(t));
	       if( (!sameVar || config.circ_NegatedI) && ! data.ma.isCurrentStep( toInt(fCandidate) ) ) {
	         data.lits.push_back(fCandidate); 
		 data.ma.setCurrentStep(toInt(fCandidate) );
		 if( config.circ_debug_out ) cerr << "found f-candidate: " << fCandidate << " sameVar=" << sameVar << endl;
	       }
	     }
	   }
	   // check all binary clauses with [x,?] as ? = -f
	   int preBinaryFs = data.lits.size();
	   if( true ) { // TODO: binary representations cannot be applied with blocked!
	    Lit * list = big->getArray(~x);
	    const int listSize = big->getSize(~x);
	    for( int j = 0 ; j < listSize; ++ j ) {
	      if( data.ma.isCurrentStep(toInt(list[j])) ) continue; // do not add literals twice!
	      data.lits.push_back( ~list[j] );
	      if( config.circ_debug_out ) cerr << "added candidate " << ~list[j] << " by implication " << ~pos << " -> " << list[j] << endl;
	    }
	   }
	   int countPos = 0;
	   bool nonTernary = false;
	   bool redundantTernary = false;
	   // try to verify f candidates!
	   if( config.circ_BLOCKED ) { // try to extract blocked gates!
             if( config.circ_debug_out ) cerr << "c blocked check with candidates: " << data.lits.size() << " including ternary cands: " << preBinaryFs << endl;
	     if( data.lits.size() == 1 && preBinaryFs == 1) { // ITE gate can be blocked only if there is a single f candidate!
	      for( int j = 0 ; j < data.list( pos ).size(); ++ j ) {
		const Clause& bClause = ca[data.list(pos)[j]];
		if( bClause.can_be_deleted() ) continue;
		countPos = countPos + 1; 
		nonTernary = (bClause.size() != 3) ? true : nonTernary;
		if( (~data.lits[0] == bClause[0] || ~data.lits[0] == bClause[1] || ~data.lits[0] == bClause[2] )
		  && (~t == bClause[0] || ~t == bClause[1] || ~t == bClause[2] ) )
		    redundantTernary = true;
	      }
	      if(  !nonTernary && (countPos == 2 || (countPos == 3 && redundantTernary)) ) {
		if( config.circ_debug_out ) cerr << "c current ITE gate is implied with blocked clause! ternaries: " << countPos << " found redundant: " << redundantTernary << endl; 
		// Lit x, Lit s, Lit t, Lit f, const Coprocessor::Circuit::Gate::Type _type, const Coprocessor::Circuit::Gate::Encoded e
		gates.push_back( Gate(x,s,t,data.lits[0], Gate::ITE, Gate::NEG_BLOCKED) );
		continue;
	      }
	      if( config.circ_debug_out ) cerr << "counted occurrences: " << countPos << " including " << nonTernary << " nonTernary clauses, found redundant: " << redundantTernary << endl;
	     }
	   }
	   // current gate is not blocked -> scan for remaining clauses
	   for( int j = 0 ; j < data.lits.size(); ++ j ) {
	    const Lit& f = data.lits[j];
	    if( config.circ_debug_out ) cerr << "c verify cand[" << j << "] = " << f << endl;
	    // look for these clauses (or binary versions!) -s,t,-x     s,f,-x (or f,-x)
	    vector<ternary>& nList = ternaries[ toInt( ~pos ) ];
	    bool foundFirst=false, foundSecond=false;
	    for( int k = 0 ; k < nList.size(); ++ k )  {
		const ternary& cand = nList[k];
		if( config.circ_debug_out ) cerr << "c check ternary " << ~pos << "," << cand.l1 << "," << cand.l2 << "  1st: " << foundFirst << " 2nd: " << foundSecond << endl;
		if( (cand.l1 == ~s || cand.l2 == ~s)  && ( cand.l1.x ^ cand.l2.x ^ (~s).x == t.x ) ) foundFirst = true;
		else if ((cand.l1 == s || cand.l2 == s)  && ( cand.l1.x ^ cand.l2.x ^ s.x == f.x ) ) foundSecond = true;
	    }
	    if( ! foundFirst || ! foundSecond ) {
	      if( config.circ_debug_out ) cerr << "c found not all in ternaries" << endl;
	      if( ! foundFirst ) { // try to find clause [t,-x], or [-s,-x]
		if( big->isOneChild(x,t,~s) )
		  { foundFirst = true; break; }
	      }
	      if(!foundFirst) foundFirst = (big->implies(x,t) || big->implies(x,~s) ) ? true : foundFirst;
	      if( ! foundSecond ) { // try to find clause [f,-x] or [s,-x]
	        if( big->isOneChild(x,f,s) )
		  { foundSecond = true; break; }
	      }
	      if(!foundSecond) foundSecond = (big->implies(x,f) || big->implies(x,s) ) ? true : foundSecond;
	    }
	    if( !foundFirst || !foundSecond ) { // f candidate not verified -> remove gate!!
              if( config.circ_debug_out ) cerr << "c could not verify " << data.lits[j] << " 1st: " << foundFirst << " 2nd: " << foundSecond << endl;
	      data.lits[j] = data.lits[ data.lits.size() -1 ];
	      data.lits.pop_back();
	      --j;
	    }
	   }
	   // add all and gates!
	   for( int j = 0 ; j < data.lits.size(); ++ j ) {
	     gates.push_back( Gate(x,s,t,data.lits[j], Gate::ITE, Gate::FULL) );
	   }
      }
    }
  
  }
  
  // check redundancy!
  for( int i = oldGates + 1; i < gates.size(); ++ i ) {
    for( int j = oldGates ; j < i; ++ j ) {
      if( var(gates[j].s()) == var(gates[i].s()) ) {
	if((   gates[j].s() == ~gates[i].s() 
	    && gates[j].x() ==  gates[i].x() 
	    && gates[j].f() ==  gates[i].t()
	    && gates[j].t() ==  gates[i].f() )  
	 || (  gates[j].s() ==  gates[i].s() 
	    && gates[j].x() == ~gates[i].x() 
	    && gates[j].t() == ~gates[i].t() 
	    && gates[j].f() == ~gates[i].f() )
	 || (  gates[j].s() == ~gates[i].s() 
	    && gates[j].x() == ~gates[i].x() 
	    && gates[j].t() == ~gates[i].f() 
	    && gates[j].f() == ~gates[i].t() ) )
	{ // gates are equivalent! ITE(s,t,f) = ITE(-s,f,t) = -ITE(s,-t,-f) = -ITE(-s,-f,-t)
	  gates[i] = gates[ gates.size() - 1 ];
	  gates.pop_back();
	  --i; break;
	}
      }
    }
  }
}

void Circuit::getXORGates(const Var v, vector< Circuit::Gate >& gates, CoprocessorData& data)
{
  // cerr << "c find XOR for variable " << v+1 << endl;
  int oldGates = gates.size();
  for( int p = 0; p < 2 ; ++ p ) {
    Lit a = mkLit( v, p == 1 ); // XOR(a,b,c) = 1
    const vector<ternary>& cList = ternaries[ toInt(a) ]; // all clauses C with pos \in C
    bool found [4]; found[0] = true; // found first clause!
    for( int i = 0 ; i < cList.size(); ++ i ) 
    {
      found[1] = found[2] = found[3] = false;
      bool binary = false;
      const Lit b = cList[i].l1; const Lit c = cList[i].l2;
      if( config.circ_debug_out ) { 
	cerr << endl << "c check [" << i << "/" << cList.size() << "] for "
	<< "[0](" <<  a << "," <<  b << "," <<  c << ")" << endl
	<< "[1](" <<  a << "," << ~b << "," << ~c << ")" << endl
	<< "[2](" << ~a << "," << ~b << "," <<  c << ")" << endl
	<< "[3](" << ~a << "," <<  b << "," << ~c << ")" << endl;
      }
      if( var(b) == var(c) || var(b) == var(a) || var(a) == var(c) ) continue; // just to make sure!
      //test whether all the other clauses can be found as well
      for( int j = i+1; j < cList.size(); ++ j ) {
	const ternary& tern = cList[j];
	if( (tern.l1 == ~b || tern.l2 == ~b) && ( tern.l1 == ~c || tern.l2 == ~c ) )
	  { found[1] = true; 
	    if( config.circ_debug_out ) cerr << "c found 1 with " << a << "," << tern.l1 << "," << tern.l2 << endl;
	    break; }
      }
      if( config.circ_debug_out )  if( found[1] ) cerr << "c found first clause as ternary" << endl;
      if ( !found[1] ) { // check for 2nd clause in implications
	if( big->implies(~a,~b) || big->implies(~a,~c)  ) {
	  found[1] = true;
	  if( config.circ_debug_out ) cerr << "c found 1 with " << ~a << " ->" << ~b << " or " << ~c << endl;
	}
	else { // not found in big
	  if( big->isOneChild(~a,~b,~c ) )
	    { found[1] = true; binary=true;
	      if( config.circ_debug_out ) cerr << "c found 1 with oneChild " << ~a << " ->" << ~b << " or " << ~c << endl;
	      break; }
	  else  { // found[1] is still false!
	    if( big->implies(b,~c) ) {
	      if( config.circ_debug_out ) cerr << "c found 1 with " << b << " ->" << ~c << endl;
	      found[1] = true;
	    }
	    else {
		if( big->isChild(b,~c) )
		  { found[1] = true; 
		    if( config.circ_debug_out ) cerr << "c found 1 with " << b << " ->" << ~c << endl;
		    binary=true;break; 
		  }
	    }
	  }
	}
      }
      if( !found[1] ) continue; // this clause does not contribute to an XOR!
      // cerr << "c found first two clauses, check for next two" << endl;
      // check whether we can find the other's by blocked clause analysis
      if( !binary && config.circ_BLOCKED ) {
	  int countPos = 0;
	  for( int j = 0 ; j < data.list( a ).size(); ++ j ) {
	    const Clause& aClause = ca[data.list(a)[j]];
	    if( aClause.can_be_deleted() ) continue;
	    if( aClause.size() != 3 ) { countPos = 3; break; }
	    countPos = countPos + 1; 
	  }
	  if(  countPos == 2 ) {
	    if( config.circ_debug_out ) cerr << "c current XOR gate is implied with blocked clauses! ternaries: " << countPos << endl; 
	    // Lit x, Lit s, Lit t, Lit f, const Coprocessor::Circuit::Gate::Type _type, const Coprocessor::Circuit::Gate::Encoded e
	    if( config.circ_debug_out ) cerr << "c blocked XOR gate " << a << "," << b << "," << c << endl;
	    gates.push_back( Gate(a,b,c, Gate::XOR, Gate::POS_BLOCKED) );
	    continue;
	  }
     }
     // TODO: find full representation!
     const vector<ternary>& naList = ternaries[ toInt(~a) ]; // all clauses C with pos \in C
     for( int j = 0; j < naList.size(); ++ j ) {
	const ternary& tern = naList[j];
	if( (tern.l1 == ~b || tern.l2 == ~b) && ( tern.l1 == c || tern.l2 == c ) ) // found [-a,-b,c]
	  { 
	    found[2] = true; 
	    if( config.circ_debug_out ) cerr << "c found 2 with " << ~a << "," << tern.l1 << "," << tern.l2 << endl;
	  }
	else if( (tern.l1 == b || tern.l2 == b) && ( tern.l1 == ~c || tern.l2 == ~c ) ) // found [-a,b,-c]
	  { found[3] = true;
	    if( config.circ_debug_out ) cerr << "c found 3 with " << ~a << "," << tern.l1 << "," << tern.l2 << endl;
	  }
     }
     if( config.circ_debug_out )  cerr << "c found in ternaries: 3rd: " << (int)found[2] << " 4th: " << (int)found[3] << endl;
     if ( !found[2] ) { // check for 2nd clause in implications
	if( big->implies(a,~b) || big->implies(a,c) ) { 
	  binary=true; 
	  found[2] = true; 
	  if( config.circ_debug_out ) cerr << "c found 2 with " << a << "->" << ~b << " or " << c << endl;
	}
	else {
	  if( big->isOneChild(a,~b,c) )
	    { 
	      found[2] = true; binary=true;
	      if( config.circ_debug_out ) cerr << "c found 2 with oneChild" << a << "->" << ~b << " or " << c << endl;
	      break; 
	    }
	  else { // found[2] is still false!
	    if( big->implies(b,c) ) { binary=true; found[2] = true; 
	      if( config.circ_debug_out ) cerr << "c found 2 with " << b << " -> " << c << endl;
	    }
	    else {
	      if( big->isChild(b,c) ){ found[2] = true; binary=true;
	      if( config.circ_debug_out ) cerr << "c found 2 with " << b << " ->* " << c << endl;
	      break; }
	    }
	  }
	}
     }
     if( !found[2] ) continue; // clause [-a,-b,c] not found
     if ( !found[3] ) { // check for 2nd clause in implications for [-a,b,-c]
	if( big->implies(a,b) || big->implies(a,~c) ) { binary=true; found[3] = true; 
	  if( config.circ_debug_out ) cerr << "c found 3 with " << a << " -> " << b << " or " << ~c << endl;
	}
	else {
	  if( big->isOneChild(a,b,~c)){ found[3] = true; binary=true;
	  if( config.circ_debug_out ) cerr << "c found 3 with one child" << a << " -> " << b << " or " << ~c << endl;
	  break; }
	  else {
	    if( big->implies(~b,~c) ) { binary=true; found[3] = true; 
	      if( config.circ_debug_out ) cerr << "c found 3 with " << ~b << " -> " << ~c << endl;
	    }
	    else {
	      if( big->isChild(~b,~c) )
	      { found[3] = true; binary=true;
	      if( config.circ_debug_out ) cerr << "c found 3 with " << ~b << " ->* " << ~c << endl;
	      break; }
	    }
	  }
	}
      }
      if( !found[3] ) continue; // clause [-a,b,-c] not found
      if( var(a) < var(c) && var(a) < var(b))
      { // for fully encoded gates we do not need to add all, but only one representation
        if( config.circ_debug_out ) cerr << "c current XOR gate is fully encodeds: " << found[0] << "," << found[1] << "," << found[2] << "," << found[3] << "," << endl; 
        gates.push_back( Gate(a,b,c, Gate::XOR, Gate::FULL) );
      }
    }
  }
  
  // remove redundant gates!
  for( int i = oldGates + 1; i < gates.size(); ++ i ) {
    for( int j = oldGates ; j < i; ++ j ) {
      if( // all variables are the same
	var(gates[i].a()) == var(gates[j].a()) && (
	     ( var(gates[i].b()) == var(gates[j].b()) && var(gates[i].c()) == var(gates[j].c())  )
	  || ( var(gates[i].c()) == var(gates[j].b()) && var(gates[i].b()) == var(gates[j].c()) )
	)
      )
      {
	// gates have same variables, check for same polarity. if true, kick later gate out!
	bool pol = sign( gates[i].a() ) ^ sign( gates[i].b() ) ^ sign( gates[i].c() );
	// if same pol, than one is obsolete
	if( pol == sign( gates[j].a() ) ^ sign( gates[j].b() ) ^ sign( gates[j].c() ) )
	{ // gates are equivalent! XOR(a,b,c) with same polarity
	  gates[i] = gates[ gates.size() - 1 ];
	  gates.pop_back();
	  --i; break;
	} else {
	  // if different pol, combining both gates leads to UNSAT!
	  cerr << "c pair of unsatisfiable XOR gates: " << endl;
	  gates[i].print(cerr);
	  gates[j].print(cerr);
	  data.setFailed();
	  return;
	  assert( false && "found a pair of gates that has to be unsatisfiable!" ); 
	}
      } 
    }
  }
}

Circuit::Gate::~Gate()
{
}


Circuit::Gate::Gate(const Clause& c, const Circuit::Gate::Type _type, const Circuit::Gate::Encoded e, const Lit output)
: inQueue(false), touched(0), type(_type), encoded(e)
{
  if( _type == Gate::GenAND || _type == Gate::ExO ) {
    data.e.size = (type == Gate::ExO ? c.size() : c.size() - 1); 
    //if( config.circ_debug_out ) cerr << "c create generic clause gate with " << data.e.size << " inputs" <<  endl;
    assert( (type != Gate::ExO || output == lit_Undef ) && "ExO gates do not have an output" );
    data.e.x = output; // in case of ExO, it should be lit_Undef
    data.e.externLits = (Lit*) malloc( data.e.size * sizeof(Lit) );
    int j = 0;
    for( int i = 0; i < c.size(); ++ i )
      if( c[i] != output ) data.e.externLits[j++] = (type == Gate::ExO) ? c[i] : ~c[i];
  } else if ( _type == Gate::XOR ) {
    assert( c.size() == 3 && "xor clause has to have four literals" );
    data.lits[0] = output;
    int j = 1;
    for( int i = 0 ; i < 3; ++i )
      if( c[i] != output ) data.lits[j++] = c[i];
  } else if ( _type == Gate::ITE ) {
    assert( false && "this constructor is not suitable for ITE gates!" );
  } else if ( _type == Gate::FA_SUM ) {
    assert( c.size() == 4 && "full adder sum clause has to have four literals" );
    for( int i = 0 ; i < 4; ++i )
      data.lits[i] = c[i];
  } else if ( _type == AND ) {
    assert( c.size() == 3 && "AND gate can only be generated from a ternary clause" );
    //if( config.circ_debug_out ) cerr << "c create AND gate from ternary clause" << endl;
    x() = output;
    a() = c[0] == output ? ~c[1] : ~c[0];
    b() = c[0] == output || c[1] == output ? ~c[2] : ~c[1];
  }
}

Circuit::Gate::Gate(const vector< Lit >& c, const Circuit::Gate::Type _type, const Circuit::Gate::Encoded e, const Lit output)
: inQueue(false), touched(0), type(_type), encoded(e)
{
  if( _type == Gate::GenAND || _type == Gate::ExO ) {
    data.e.size = c.size(); 
    assert( (type != Gate::ExO || output == lit_Undef ) && "ExO gates do not have an output" );
    //if(  config.circ_debug_out) cerr << "c create generic vector gate with " << data.e.size << " inputs with output " << output <<  endl;
    data.e.x = output; // in case of ExO, it should be lit_Undef
    data.e.externLits = (Lit*) malloc( data.e.size * sizeof(Lit) );
    for( int i = 0; i < c.size(); ++ i )
      data.e.externLits[i] = (type == Gate::ExO) ? c[i] : ~c[i];
  } else if ( _type == Gate::XOR ) {
    assert( c.size() == 3 && "xor clause has to have four literals" );
    data.lits[0] = output;
    int j = 1;
    for( int i = 0 ; i < 3; ++i )
      if( c[i] != output ) data.lits[j++] = c[i];
  } else if ( _type == Gate::ITE ) {
    assert( false && "this constructor is not suitable for ITE gates!" );
  } else if ( _type == Gate::FA_SUM ) {
    assert( c.size() == 4 && "full adder sum clause has to have four literals" );
    for( int i = 0 ; i < 4; ++i )
      data.lits[i] = c[i];
  } else if ( _type == AND ) {
    x() = output;
    a() = c[0] == output ? c[1] : c[0];
    b() = c[0] == output || c[1] == output ? c[2] : c[1];
  }
}

Circuit::Gate::Gate(Lit _x, Lit _s, Lit _t, Lit _f, const Circuit::Gate::Type _type, const Circuit::Gate::Encoded e)
: inQueue(false),touched(0), type(_type), encoded(e)
{
  assert( (_type == ITE || _type == FA_SUM) && "This constructur can be used for ITE gates only" );
  x() = _x; s() = _s; t() = _t; f() = _f;
}

Circuit::Gate::Gate(Lit _x, Lit _a, Lit _b, const Circuit::Gate::Type _type, const Circuit::Gate::Encoded e)
: inQueue(false), touched(0), type(_type), encoded(e)
{
//  assert( false && "This constructor is not yet implemented (should be for faster construction!)" );
  assert( (type == AND || type == XOR ) && "This constructor can only be used for AND or XOR gates" );
  if( type == AND ) {x() = _x; a() =  ~_a; b() = ~_b; }
  else { c() = _x; a() =  _a; b() = _b; }
}

Circuit::Gate& Circuit::Gate::operator=(const Circuit::Gate& other)
{
  inQueue = other.inQueue;
  touched = other.touched;
  type = other.type;
  encoded = other.encoded;
  if( type == ExO || type == GenAND ) {
    data.e.x = other.data.e.x;
    data.e.externLits = other.data.e.externLits;
    data.e.size = other.data.e.size;
  } else {
    for( int i = 0 ; i < 4; ++ i ) {
      data.lits[i] = other.data.lits[i]; 
    }
  }
  return *this;
}

Circuit::Gate::Gate(const Circuit::Gate& other)
{
  inQueue = other.inQueue;
  touched = other.touched;
  type = other.type;
  encoded = other.encoded;
  if( type == ExO || type == GenAND ) {
    data.e.x = other.data.e.x;
    data.e.externLits = other.data.e.externLits;
    data.e.size = other.data.e.size;
  } else memcpy( data.lits, other.data.lits, sizeof(Lit) * 4 );
}

void Circuit::Gate::destroy()
{
  if( (type == Gate::GenAND || type == Gate::ExO ) && data.e.externLits != 0  ) 
  {  ::free ( data.e.externLits ); data.e.externLits = 0 ; }
}

void Circuit::Gate::invalidate()
{
  destroy();
  type = Gate::INVALID;
}


void Circuit::Gate::print(ostream& stream) const
{
  switch( encoded ) {
    case FULL:        stream << "full "; break;
    case POS_BLOCKED: stream << "posB "; break;
    case NEG_BLOCKED: stream << "negB "; break;
  }
  if( type != XOR && type != ExO && type != FA_SUM) {
    stream << getOutput() << " <-> ";
    switch( type ) {
      case AND:    stream << "AND( " << a() << " , " << b() << " )" << endl; break;
      case GenAND: stream << "g-AND("; 
        for( int i = 0 ;  i < data.e.size; ++ i ) 
	  stream << " " << data.e.externLits[i] ;
	stream << " )" << endl;
        break;
      case ITE:    stream << "ITE( " << s() << " , " << t() << " , " << f() << " )" << endl; break;
      default: break; // nothing to be done here ...
    }
  } else if( type == XOR ) {
    stream << "XOR( " << a() << " , " << b() << " " << c() << " )" << endl;
  } else if( type == ExO ) {
    stream << "ExO("; 
    for( int i = 0 ;  i < data.e.size; ++ i ) stream << " " << data.e.externLits[i] ;
    stream << " )" << endl;
  } else {
    stream << "XOR( ";
    for( int i = 0 ; i < 4; ++ i ) cerr << " " << data.lits[i];
    cerr << ")" << endl;
  }
}
