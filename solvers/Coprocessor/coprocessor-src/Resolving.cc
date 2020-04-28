/*************************************************************************************[Resolving.h]
Copyright (c) 2012, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Resolving.h"

using namespace Coprocessor;


Resolving::Resolving(CP3Config& _config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Propagation& _propagation)
: Technique(_config, _ca,_controller)
, data(_data)
, propagation(_propagation)
, processTime(0)
, addedTern2(0)
, addedTern3(0)
, addedBinaries(0)
, res3steps(0)
, add2steps(0)
, removedViaSubsubption(0)
, detectedDuplicates(0)
, resHeap(data)
{

}

void Resolving::giveMoreSteps()
{
  res3steps = res3steps < config.opt_res3_inpStepInc ? 0 : res3steps - config.opt_res3_inpStepInc;
  add2steps = add2steps < config.opt_add2_inpStepInc ? 0 : add2steps - config.opt_add2_inpStepInc;
}


bool Resolving::process(bool post)
{
  MethodTimer mt( &processTime );
  
  if( ! performSimplification() ) return false; // do not do anything?!
  modifiedFormula = false;
  
 
  if( ! post ) {
    // do not simplify, if the formula is considered to be too large!
    if( !data.unlimited() && ( data.nVars() > config.opt_ternResolve_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_ternResolve_cls && data.nTotLits() > config.opt_ternResolve_lits) ) return false;
    ternaryResolve();
  }
  
  if( config.opt_add2_red_start || post ) {
    if( config.opt_add2_red ) {
      // do not simplify, if the formula is considered to be too large!
      if( !data.unlimited() && ( data.nVars() > config.opt_addRedBins_vars && data.getClauses().size() + data.getLEarnts().size() > config.opt_addRedBins_cls && data.nTotLits() > config.opt_addRedBins_lits) ) return false;
      addRedundantBinaries(); 
    }
  }
  
  if( data.hasToPropagate() ) {
    propagation.process(data,true);
    modifiedFormula = modifiedFormula || propagation.appliedSomething(); 
  }
  return modifiedFormula;
}

void Resolving::printStatistics(ostream& stream)
{
  stream << "c [STAT] RES " 
      << processTime << " s, " 
      << addedTern2 + addedTern3 + addedBinaries << " cls+, " 
      << addedBinaries << " bin+, " 
      << addedTern2 << " tern2+, "
      << addedTern3 << " tern3+, "
      
      << res3steps << " res3teps, "
      << removedViaSubsubption << " subsCls, "
      << detectedDuplicates << " duplicates, "
      << endl;
}

void Resolving::ternaryResolve()
{
  // deque<Var> activeVariables;
  
  resHeap.addNewElement( data.nVars() );
  resHeap.clear();
  data.ma.resize( data.nVars() );
  for( Var v = 0; v < data.nVars(); ++v ) {
    if( data[mkLit(v,false)] > 0 && data[mkLit(v,true)] > 0 ) {
      resHeap.insert(v);
    }
  }
  seen.assign( data.nVars() *2 , 0); // which literals have been seen already?
  vector<int> toIgnore( data.nVars() *2 , 0); // how many clauses in the list are ternary
  vec<Lit> resolvent; // store result of resolution here
  
  const int moveSize =  config.opt_res3_use_binaries ? 2 : 3;
  
  // setup occurrence lists to work with interesting clauses only in algorithm later
  for( Var v  = 0; v < data.nVars(); ++v ) {
   for( int p = 0 ; p < 2 ; ++ p ) 
   {
     const Lit l = mkLit( v, p == 1 );
    vector<CRef>& cls = data.list(l);
    int j = 0;
    for( int i = 0 ; i < cls.size(); ++ i ) {
      const Clause& c = ca[cls[i]];
      if( c.can_be_deleted() ) { // remove clauses that do not belong into the list!
	cls[i] = cls[ cls.size() - 1 ];
	cls.pop_back(); --i;
      } else if ( (!config.opt_add2_red_lea && c.learnt() )  // use learnt clauses?
	|| (c.size() != 3 && c.size() != moveSize) ) { // if enabled, also move binary clauses to back!
	CRef tmp = cls[i]; // move nonternary clauses to front!
	cls[i] = cls[j];
	cls[j++] = tmp;
	continue;
      }
    }
    // initially, seen clauses is 0, but toIgnore are not considered
    toIgnore[ toInt(l) ] = j;
    seen[ toInt(l) ] = j;
   }
  }
  
  // sort activeVariables according to size!
  
  while( resHeap.size() > 0 && !data.isInterupted() 
    && (data.unlimited() || addedTern2 + addedTern3 < config.opt_res3_newCls )
    && (data.unlimited() || res3steps < config.opt_res3_steps )
  )
  {
    // FIXME: garbage collection, cannot be done because of ignore structures!
    const Var v = (Var)resHeap[0];
    resHeap.removeMin();
        
    if( config.res3_debug_out ) cerr << "c process variable " << v+1 << " vars[" << data[v] << "]" << endl;
    
    const Lit p = mkLit(v,false);
    const Lit n = mkLit(v,true);
    
    for( int i = toIgnore[ toInt(p) ]; i < data.list( p ). size(); ++ i ) {
      for( int j = toIgnore[ toInt(n) ]; j < data.list( n ). size(); ++ j ) {
	if( i < seen[ toInt(p) ] && j < seen[ toInt(n) ] ) continue; // do not re-check already seen clauses!
	resolvent.clear();
	const Clause& c = ca[data.list(p)[i]];
	if( c.can_be_deleted() ) continue;
	const Clause& d = ca[data.list(n)[j]];
	if( d.can_be_deleted() ) continue;
	res3steps++;
	if( !data.unlimited() && res3steps > config.opt_res3_steps ) goto endTernResolve;
	if( resolve( c,d, v, resolvent) ) continue;
	if( config.res3_debug_out ) cerr << "c resolved " << c << " with " << d << endl;
	if( resolvent.size() == 0 ) {
	  data.setFailed(); return; 
	} else if( resolvent.size() == 1 ){
	 if( data.enqueue(resolvent[0]) == l_False ) return;
	} else if( resolvent.size() < 4 && // use resolvent only, if it has less then 4 literals
	  !hasDuplicate(data.list(resolvent[0]),resolvent) ) { // and if this clause is not already in the data structures!
	  // add clause here! 
	  const bool becomeLearnt = c.learnt() || d.learnt();
	  CRef cr = ca.alloc(resolvent, becomeLearnt); 
	  if( config.res3_debug_out ) cerr << "c add clause " << ca[cr] << endl;
	  data.addClause(cr);
	  data.addSubStrengthClause(cr);
	  if( becomeLearnt ) {
	    data.getLEarnts().push(cr);
	  } else {
	    data.getClauses().push(cr);
	  }
	  if(resolvent.size() == 2 ) addedTern2 ++;
	  else addedTern3 ++;
	  
	  if( config.opt_res3_reAdd ) {
	    // add variables of resolvent back to queue, if not there already
	    for( int k = 0 ; k < resolvent.size(); ++ k ) {
	      const Var rv = var(resolvent[k]);
	      if(!resHeap.inHeap(rv) ) resHeap.insert(rv);
	    }
	  }
	}
      }
    }

    // store which clauses have been handles already
    seen[ toInt(p) ] = data.list(p).size();
    seen[ toInt(n) ] = data.list(n).size();
  } // next variable!
  
endTernResolve:;
  
}

bool Resolving::resolve(const Clause & c, const Clause & d, const int v, vec<Lit> & resolvent)
  {
    unsigned i = 0, j = 0;
    while (i < c.size() && j < d.size())
    {   
        if (c[i] == mkLit(v,false))      ++i;   
        else if (d[j] == mkLit(v,true))  ++j;
        else if (c[i] < d[j])
        {
           if (checkPush(resolvent, c[i]))
                return true;
           else ++i;
        }
        else 
        {
           if (checkPush(resolvent, d[j]))
              return true;
           else
                ++j; 
        }
    }
    while (i < c.size())
    {
        if (c[i] == mkLit(v,false))    ++i;   
        else if (checkPush(resolvent, c[i]))
            return true;
        else 
            ++i;
    }
    while (j < d.size())
    {
        if (d[j] == mkLit(v,true))     ++j;
        else if (checkPush(resolvent, d[j]))
            return true;
        else                           ++j;

    }
    return false;
  } 

bool Resolving::checkPush(vec<Lit> & ps, const Lit l)
{
    if (ps.size() > 0)
    {
        if (ps.last() == l)
         return false;
        if (ps.last() == ~l)
         return true;
    }
    ps.push(l);
    return false;
}
  
bool Resolving::ordered_subsumes (const vec<Lit>& c, const Clause & other) const
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

bool Resolving::ordered_subsumes (const Clause & c, const vec<Lit>& other) const
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
  
bool Resolving::hasDuplicate(vector<CRef>& list, const vec<Lit>& c)
{
  for( int i = 0 ; i < list.size(); ++ i ) {
    Clause& d = ca[list[i]];
    if( d.can_be_deleted() || (!config.opt_res3_use_subs && d.size() != c.size()) ) continue;
    int j = 0 ;
    if( d.size() == c.size() ) {
      while( j < c.size() && c[j] == d[j] ) ++j ;
      if( j == c.size() ) { 
	detectedDuplicates ++;
	return true;
      }
    }
    if( config.opt_res3_use_subs ) { // check each clause for being subsumed -> kick subsumed clauses!
      if( d.size() < c.size() ) {
	detectedDuplicates ++;
	if( ordered_subsumes(d,c) ) return true; // the other clause subsumes the current clause!
      } if( d.size() > c.size() ) { // if size is equal, then either removed before, or not removed at all!
	if( ordered_subsumes(c,d) ) { 
	  d.set_delete(true);
	  data.removedClause(list[i]);
	  removedViaSubsubption ++;
	}
      }
    }
  }
  return false;
}


void Resolving::addRedundantBinaries()
{
  seen.assign( data.nVars() *2 , 0); // which literals have been seen already?
  data.ma.resize( data.nVars() *2 );
  vector < vector<Lit> > big (data.nVars() *2) ;
  
  if( config.res3_debug_out ) cerr << "add redundant binaries" << endl;
  
  // create big
  for( int p = 0 ; p < 2 ; ++ p ) 
  {
    vec<CRef>& cls = p == 0 ? data.getClauses() : data.getLEarnts();
    for( int i = 0 ; i < cls.size(); ++ i ) {
      const Clause& c = ca[cls[i]];
      if( c.can_be_deleted() || c.size() != 2 ) continue;
      big[ toInt(~c[0]) ].push_back( c[1] );
      big[ toInt(~c[1]) ].push_back( c[0] );
    }
  }
  // count how many literals have been seens already
  for( Var v  = 0; v < data.nVars(); ++v ) {
    seen[ toInt(mkLit(v,false)) ] = big[toInt(mkLit(v,false))].size();
    seen[ toInt(mkLit(v,true)) ] = big[toInt(mkLit(v,true))].size();
  }
  
  // for each literal, create its "binary" trail, and then add partially redundant clauses
  for( Var v  = 0; v < data.nVars() &&  !data.isInterupted() ; ++v ) {
    for( int p = 0 ; p < 2 ; ++ p ) 
    {
      const Lit startLit = mkLit(v, p == 1);
     // cerr << "c start for lit " << startLit << endl;
      data.ma.nextStep();
      data.ma.setCurrentStep( toInt(startLit) );
      data.lits.clear();
      
      for( int i = 0 ; i < big[ toInt(startLit) ].size(); ++ i ) {
	const Lit l = big[ toInt(startLit) ][i];
	// not twice!
	if( data.ma.isCurrentStep( toInt(l) ) ) continue;
	data.ma.setCurrentStep( toInt(l) );
	if( config.res3_debug_out ) cerr << "c found direct " << l << endl;
	data.lits.push_back(l);
      }
      int directLits = data.lits.size();
      
      if( config.res3_debug_out ) cerr << "c direct lits: " << directLits << endl;
      // no need to work on "empty" trails (no transitive literals)
      if( data.lits.size() == 0 ) continue;
      int level = 1;
      data.lits.push_back(lit_Undef);
      for( int i = 0 ; i < data.lits.size(); ++ i ) {
	const Lit l = data.lits[i];
	// cerr << "c check lit: " << l << " [" << i << "/" << data.lits.size() << "]" << endl;
	// add new levels or abort!
	if( l == lit_Undef )
	  if( i+1 < data.lits.size() && data.lits[i+1] != lit_Undef ) { data.lits.push_back(lit_Undef); level ++; continue;}
	  else break;
	
	// work only on "old" literals!
	for( int j = 0 ; j < big[ toInt(l) ].size(); ++ j ) {
	  const Lit k = big[ toInt(l) ][j];
	  if( data.ma.isCurrentStep( toInt(k) ) ) continue;
	  data.ma.setCurrentStep( toInt(k) );
	  data.lits.push_back(k);
	  if( config.res3_debug_out ) cerr << "c found transitive " << startLit << " -> " << k  << "  @ " << level << " via " << l << endl;
	}
	
      }
      
      // remove lit_undefs from list!
      for( int i = directLits ; i < data.lits.size(); ++ i ) 
	if( data.lits[i] == lit_Undef ) {
	  data.lits[i] = data.lits[ data.lits.size() - 1]; data.lits.pop_back(); --i;
	}
      
      if( config.res3_debug_out ) cerr << "c found " << data.lits.size() << " new (" << directLits << " direct) literals for " << startLit << " with " << level << " levels" << endl;
      
      int use = config.opt_add2_red_level ? (level * config.opt_add2_percent) : (config.opt_add2_percent * ( data.lits.size() - directLits ) );
      
      // cerr << "c use new literals: " << use << endl;
      
      assert( use <= data.lits.size() && "used literals have to be less than the ones in the found list" );
      
      // shuffle some literals to the front!
      for( int i = directLits; i < use+directLits; ++ i ) {
	int r = i + rand() % (data.lits.size() - i );
	if( config.res3_debug_out ) cerr << "c swap " << i << " and " << r << " out of " << data.lits.size() << endl;
	const Lit tmp = data.lits[i];
	data.lits [ i ] = data.lits [ r ];
	data.lits[r] = tmp;
      }
      
      // add both directionr to avoid adding twice!
      for( int i = directLits; i < use+directLits; ++ i ) {
	  big[ toInt(startLit) ].push_back( data.lits[i] );
	  big[ toInt( ~data.lits[i]) ].push_back( ~startLit );
	  if( config.res3_debug_out ) cerr  << "c add " << startLit << " -> " << data.lits[i] << endl;
	  if( config.res3_debug_out ) cerr  << "c add " << ~data.lits[i] << " -> " << ~startLit << endl;
      }
    }
  }
  
  vec<Lit> ps;
  ps.push();ps.push();
  // add the new clauses to the formula / data structures!
  for( Var v  = 0; v < data.nVars(); ++v ) {
    for( int p = 0 ; p < 2 ; ++ p ) 
    {
      const Lit thisLit = mkLit(v, p == 1);
      ps[0] = ~thisLit;
      for( int j =  seen[ toInt(thisLit) ]; j < big[ toInt(thisLit) ].size() ; ++ j ) {
	  const Lit k = big[ toInt(thisLit) ][j];
	  ps[1] = k;
	  if( k < thisLit ) continue;
	  assert( thisLit < k && "add only ordered clauses!" );
	  const CRef cr = ca.alloc(ps,false); // not a learnt clause!
	  addedBinaries ++;
	  data.addClause(cr);
	  data.getClauses().push(cr);
	  modifiedFormula = true;
	  if( config.res3_debug_out ) cerr << "c added " << ca[cr] << endl;
      }
    }
  }
}


void Resolving::destroy()
{
  vector<int>().swap( seen );
}
