/****************************************************************************************[Dense.cc]
Copyright (c) 2013, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Dense.h"

#include <fstream>
#include <sstream>

using namespace std;
using namespace Coprocessor;

Dense::Dense(CP3Config &_config, ClauseAllocator& _ca, ThreadController& _controller, CoprocessorData& _data, Propagation& _propagation)
: Technique(_config, _ca,_controller)
, data(_data)
, propagation( _propagation )
, globalDiff(0)
{}

void Dense::compress(const char* newWhiteFile)
{
  if( propagation.process(data) == l_False ) data.setFailed();
  if( !data.ok() ) return;
 
  if( config.dense_debug_out ) {
    cerr << "c dense compress" << endl;
  }
  
  Compression compression;
  compression.variables = data.nVars();
  compression.mapping = (Var*)malloc( sizeof(Var) * (data.nVars()) );
  for( Var v = 0; v < data.nVars(); ++v ) compression.mapping[v] = -1;
  
  uint32_t* count = (uint32_t*)malloc( (data.nVars()) * sizeof(uint32_t) );
  memset( count, 0, sizeof( uint32_t) * (data.nVars()) );
  // count literals occuring in clauses
  
  for( int s = 0 ; s < 2; ++ s ) {
    vec<CRef>& list = s == 0 ? data.getClauses() : data.getLEarnts();
    for( uint32_t i = 0 ; i < list.size(); ++i ) {
      Clause& clause = ca[ list[i] ];
      if( clause.can_be_deleted() || clause.learnt() ) continue; // consider only clauses in the formula!
      uint32_t j = 0 ;
      for( ; j < clause.size(); ++j ){
	const Lit l = clause[j];
	
	if( config.dense_debug_out && l_Undef != data.value(l) ) cerr << "c DENSE found assigned literal " << l << " in clause ["<< data.getClauses()[i] << "] : " << clause << " learned?: " << clause.learnt() << endl ;
	assert( l_Undef == data.value(l) && "there cannot be assigned literals");
	assert(var(l) < data.nVars() );
	
	count[ var(l) ] ++;
      }
      // found empty clause?
      if( clause.size() == 0 ) { data.setFailed(); }
    }
  }
 
  uint32_t diff = 0;
  for( Var v = 0 ; v < data.nVars(); v++ ){
    assert( diff <= v && "there cannot be more variables that variables that have been analyzed so far");
    if( count[v] != 0 || data.doNotTouch(v) || 
      ( data.value(mkLit(v,false)) != l_Undef && (config.opt_dense_keep_assigned) ) ) // do not drop assigned variables!
    { // do not rewrite the trail!
      compression.mapping[v] = v - diff;
      if( config.dense_debug_out && data.doNotTouch(v)) cerr << "c mapping for variable " << v+1 << " is: " << compression.mapping[v]+1 << endl;
    }
    else { 
      diff++; 
      if ( config.dense_debug_out  ) {
	if(data.doNotTouch(v)) cerr << "c do not touch variable will be dropped: " << v+1 << " mapping: " << compression.mapping[v]+1 << endl;
	else cerr << "c variable " << v+1 << " occurrs " << count[v] << " times, and is undefined: " << (data.value(mkLit(v,false)) == l_Undef) << endl;
      }
      assert( compression.mapping[v] == -1 );
    }
  }
  
  // formula is already compact, or not too loose
  if( diff == 0 || ( config.opt_dense_fragmentation > 1.0 + ( (diff * 100)  / data.nVars()  ) ) ) {
    if( config.dense_debug_out > 0 ) cerr << "c [DENSE] no fragmentation, do not compress!" << endl;
    
    if( config.opt_dense_store_forward ) {
      if( config.dense_debug_out ) cerr << "c store forward mapping " << endl;
      forward_mapping.resize( data.nVars(), -1 ); // initially, set to -1 for no mapping (dropped)
      for( Var v = 0; v < data.nVars() ; v++ )
	forward_mapping[v] = compression.mapping[v]; // store everything into the new mapping file!
    }
    
    free( count ); // do not need the count array any more
    return;
  }
  
  // first, take care of the undo stack that has been created until this compression
  adoptUndoStack();
  globalDiff += diff;
  
  // replace everything in the clauses
  if( config.dense_debug_out > 0 ) cerr << "c [DENSE] compress clauses" << endl;
  for( int s = 0 ; s < 2; ++ s ) {
    vec<CRef>& list = s == 0 ? data.getClauses() : data.getLEarnts();
    for( uint32_t i = 0 ; i < list.size(); ++i ){
      Clause& clause = ca[ list[i] ];
      if( clause.can_be_deleted() ) continue;
      assert( clause.size() > 1 && "do not rewrite unit clauses!" );
      if( config.dense_debug_out > 1 ) cerr << "c [DENSE] rewrite clause [" << list[i] << "] " << clause << endl;
      for( uint32_t j = 0 ; j < clause.size(); ++j ){
	const Lit l = clause[j];
	if( clause.learnt() && compression.mapping[ var(l) ] == -1 ) { // drop this clause because the current variable is not present in the formula any more!
	  if( config.dense_debug_out > 1 ) cerr << "c [DENSE] into deleted clause, because variable " << var(l) << " does not occur in non-learned clauses" << endl;
	  clause.set_delete(true); break;
	}
	// if( debug > 1 ) cerr << "c compress literal " << l.nr() << endl;
	assert( compression.mapping[ var(l) ] != -1 && "only move variable, if its not moved to -1" );
	const bool p = sign(l);
	const Var v= compression.mapping[ var(l)];
	clause[j] = mkLit( v, p );
	// polarity of literal has to be kept
	assert( sign(clause[j]) == p && "sign of literal should not change" );
      }
      if( config.dense_debug_out > 1 ) cerr << "c [DENSE] into [" << list[i] << "]           " << clause << endl;
    }
  }
  
  if( newWhiteFile != 0 ) {
    cerr << "c work with newWhiteFile " << newWhiteFile << endl;
    ofstream file;
    file.open( newWhiteFile, ios::out );
    // dump info
    // file << "original variables" << endl;
    for( Var v = 0; v < data.nVars(); ++ v )
      if( data.doNotTouch(v) ) file << compression.mapping[ v ] << endl;
    file.close();
  }
  
  // compress trail, so that it can still be used!
  if( config.dense_debug_out ) {
    cerr << "c before trail: "; 
    for( uint32_t i = 0 ; i < data.getTrail().size(); ++ i ) cerr << " " << data.getTrail()[i];
    cerr << endl;
  }
  
  // erase all top level units after backup!
  // keep the literals that are not removed!
  int j = 0; // count literals that stay on trail!
  for( int i = 0 ; i < data.getTrail().size(); ++ i ) {
    const Lit l  = data.getTrail()[i];
    if( count[var(l)] != 0 || data.doNotTouch(var(l)) || config.opt_dense_keep_assigned ) {
      const bool p = sign(l);
      const Var v= compression.mapping[ var(l) ];
      if( config.dense_debug_out ) cerr << "c move literal " << l << " from " << i << " to pos " << j << " as " << mkLit( v, p ) << endl;
      data.getTrail()[j++] = mkLit( v, p ); // keep the modified literal!
    } else {
      compression.trail.push_back(data.getTrail()[i] );
      data.resetAssignment( var(data.getTrail()[i]) ); 
    }
  }
  data.getTrail().shrink( data.getTrail().size() - j ); // do not clear, but resize to keep the literals that have been kept!
  propagation.reset(data); // reset propagated literals in UP

  free( count ); // do not need the count array any more
  
  if( config.dense_debug_out ) {
    cerr << "c final trail: "; 
    for( uint32_t i = 0 ; i < data.getTrail().size(); ++ i ) cerr << " " << data.getTrail()[i];
    cerr << endl;
  }

  if( config.opt_dense_store_forward ) {
    if( config.dense_debug_out) cerr << "c store forward mapping " << endl;
    forward_mapping.resize( data.nVars(), -1 ); // initially, set to -1 for no mapping (dropped)
    for( Var v = 0; v < data.nVars() ; v++ )
      forward_mapping[v] = compression.mapping[v]; // store everything into the new mapping file!
  }
  
  
  // rewriting everything finnished
  // invert mapping - and re-arrange all variable data
  for( Var v = 0; v < data.nVars() ; v++ )
  {
    if(! config.opt_dense_keep_assigned ) assert( (data.doNotTouch(v) || data.value( mkLit( v, false) ) == l_Undef) && "there is no assigned variable allowed " );
//	    if( v+1 == data.nVars() ) cerr << "c final round with variable " << v+1 << endl;
    if ( compression.mapping[v] != -1 ){
      if( config.dense_debug_out ) cerr << "c map " << v+1 << " to " << compression.mapping[v] + 1 << endl;
//      if( v+1 == data.nVars() ) cerr << "c final round with move" << endl;
      // cerr << "c move intern var " << v << " to " << compression.mapping[v] << endl;
      data.moveVar( v, compression.mapping[v], v+1 == data.nVars() ); // map variable, and if done, re-organise everything
      if(! config.opt_dense_keep_assigned ) assert( (data.doNotTouch(compression.mapping[ v ]) || data.value( mkLit(compression.mapping[ v ],false) ) == l_Undef ) && "there is no assigned variable allowed " );
      // invert!
      compression.mapping[ compression.mapping[v] ] = v;
      // only set to 0, if needed afterwards
      if( compression.mapping[ v ] != v ) compression.mapping[ v ] = -1;
    } else {
      if( config.dense_debug_out ) cerr << "c remove variable " << v+1  << endl;
//      if( v+1 == data.nVars() ) cerr << "c final round without move" << endl;
      // any variable that is not replaced should have l_Undef
      if( v+1 == data.nVars() ) data.moveVar( v-diff, v-diff, true ); // compress number of variables!
    }
  }

  // after full compression took place, set known assignments again!
  for( int i = 0 ; i < data.getTrail().size(); ++ i ) {
    data.enqueue( data.getTrail()[i] ); // put rewritten literals back on the trail!
  }
  
  if( data.nVars() + diff != compression.variables ) {
    cerr << "c number of variables does not match: " << endl
	 << "c diff= " << diff << " old= " << compression.variables << " new=" << data.nVars() << endl;
  }
  assert( data.nVars() + diff == compression.variables  && "number of variables has to be reduced" );
  
  compression.postvariables = data.nVars(); // store number of post-variables
  map_stack.push_back( compression );
  
  data.didCompress(); // notify data about compression!
  
  return; 
}

void Dense::decompress(vec< lbool >& model)
{
  if( config.dense_debug_out ) {
    cerr << "c dense decompress, model to work on: ";
    for( int i = 0 ; i < model.size(); ++ i ) cerr << (model[i] == l_True ? i+1 : -i-1) << " ";
    cerr << endl;
  }
  if( map_stack.size() == 0 && config.dense_debug_out ) cerr << "c no decompression" << endl;
  // walk backwards on compression stack!
  for( int i = map_stack.size() - 1; i >= 0; --i ) {
    Compression& compression = map_stack[i];
    if( config.dense_debug_out ) cerr << "c [DENSE] change number of variables from " << model.size() << " to " << compression.variables << endl;
    // extend the assignment, so that it is large enough
    if( model.size() < compression.variables ){
      model.growTo( compression.variables, l_False  );
      while( data.nVars() < compression.variables ) 
	data.nextFreshVariable('o');
    }
    // backwards, because variables will increase - do not overwrite old values!
    for( int v = compression.variables-1; v >= 0 ; v-- ){
      // use inverse mapping to restore the already given polarities (including UNDEF)
	if( compression.mapping[v] != v && compression.mapping[v] != -1 ) {
	  if( config.dense_debug_out ) cerr << "c move variable " << v+1 << " to " << compression.mapping[v] + 1  << " -- falsify " << v+1 << endl;
	  
	  model[ compression.mapping[v] ] =  model[ v ];
	  // set old variable to some value
	  model[v] = l_False;
	} else {
	  if( model[v] == l_Undef ) {
	    model[v] = l_False; 
	    if( config.dense_debug_out ) cerr << "c falsify " << v+1 << endl;
	  }
	}
    }
    
    // write trail assignments back
    for( int j = 0 ; j < compression.trail.size(); ++ j ) {
      if ( sign( compression.trail[j] ) ) model[ var(compression.trail[j]) ] = l_False;
      else model[ var(compression.trail[j]) ] = l_True;
      if( config.dense_debug_out ) cerr << "c satisfy " << compression.trail[j] << endl;
    }
  }
  if( config.dense_debug_out ) {
    cerr << "c decompressed model: ";
    for( int i = 0 ; i < model.size(); ++ i ) cerr << (model[i] == l_True ? i+1 : -i-1) << " ";
    cerr << endl;
  }
}

void Dense::adoptUndoStack()
{
  if( config.dense_debug_out ) {
    cerr << "c dense adopt undo stack" << endl;
  }
  
  vector< Lit >& extend = data.getUndo();
  const int compressed = data.getLastCompressUndoLits();
  if( compressed == -1 ){
    if( config.dense_debug_out ) cerr << "c no compression yet, so no need to decompress undo info" << endl;
    return; // nothing to be done, because no compression yet!
  }

  if( config.dense_debug_out > 1 ){
    cerr << "c adopt undo stack" << endl;
    cerr << "stack: " << extend << endl;
  }
  
  int start = data.getLastDecompressUndoLits();
  if( start == -1 ) start = data.getLastCompressUndoLits();
  assert( start >= 0 && "at least one compress or adopt has been done already" );
  if( config.dense_debug_out ) cerr << "c rewrite undo stack from " << start << " to " << extend.size() << endl;
  for( uint32_t i = start; i < extend.size(); ++ i ) {
    if( extend[i] != lit_Undef ) { // rewrite each literal of the extension step
	if( config.dense_debug_out ) cerr << "c rewrite " << extend[i] << endl;
	Var v = var(extend[i]);
	for( int j = map_stack.size() - 1; j >= 0; --j ) {
	  Compression& compression = map_stack[j];
	  if( v < compression.postvariables ) v = compression.mapping[v];
	  else v = compression.variables + v - compression.postvariables; // v is a fresh variable since the last compression, hence, handle this variable as such!
	}
	extend[i] = mkLit( v, sign(extend [i]) );
	if( config.dense_debug_out ) cerr << "c             into " << extend[i] << endl;
    }
  }
  if( config.dense_debug_out > 1 ) cerr << "stack: " << extend << endl;
  // store that this decompression has been done
  data.didDecompressUndo();  
}

bool Dense::writeUndoInfo(const string& filename) {

  if( config.dense_debug_out ) {
    cerr << "c write undo info" << endl;
  }
  
  ofstream file( filename.c_str(), ios_base::out);
  if( ! file ) {
    cerr << "c ERROR: could not open map - undo file " << filename << endl;
    return false;
  }

  if( map_stack.size() == 0 ) { file.close();return true; } // nothing to write -> clear file!
  
  // for each mapping, write two lines in the file
  for( int i = 0 ; i < map_stack.size(); ++ i ) {
    Compression& compression = map_stack[i];
    file << "p cnf " << compression.variables << " " << compression.trail.size() + 1 << endl;
    for( int j = 0 ; j < compression.variables; ++ j ) file << compression.mapping[j] + 2 << " "; // since we are also using -1 and 0 
    file << "0" << endl;
    for( int j = 0 ; j < compression.trail.size(); ++ j ) {
      file <<  compression.trail[j] << " 0" << endl;
    }
  }

  file.close();
  return true;
}

/** parse a clause from string and store it in the literals vector
 *
 */
static int parseClause( const string& line, vector<Lit>& literals ) 
{
	uint32_t ind = 0;
	// skip whitespaces
	while( ind < line.size() && line[ind] == ' ' ) ++ind;
	// parse numbers
	while(line.size() > ind)	// read each single number
	{
		// cerr << "c FP check(" << lines << "," << ind << "): " << line[ind] << endl;
		int32_t number = 0;
		bool negative = false;
		
		while ( ind < line.size() && line[ind] == '-')
		{
			negative = true;
			ind++;
		}
		// read next number here
		while( ind < line.size() && line[ind] >= '0' && line[ind] <= '9' )
		{
			number *=10;
			number += line[ind++] - '0';
		}
		
		if( number == 0 ) break;	// there may be some symbols behind a 0, but they do not matter
		
		// put right sign on the number
		// number = (negative) ? 0 - number : number;

		const Lit lit1 = mkLit( number - 1, negative );
		literals.push_back( lit1 );

		
		// skip whitespaces
		while(line[ind] == ' ') ind++;
	}
	return 0;
}

  
  
bool Dense::readUndoInfo(const string& filename) {
 vector<Lit> literals;
 string line;
 
 assert( map_stack.size() == 0 && "do not load undo information, if there is already information present!");
 
  ifstream file( filename.c_str(), ios_base::in);
  if( ! file ) {
    cerr << "c WARNING: could not open undo file " << filename << " (might not have been created)" << endl;
    return false;
  } else {
    cerr << "c opened var map " << filename << " for reading ... " << endl; 
  }

  int parsedClauses = 0;
  int promisedClauses = -1;
  int variables = 0;

  
  bool pLine = false;
 while( getline( file, line ) ) {

   if( line.find( "c" ) == 0 ) continue; // comments are fine!
   
   pLine = !pLine; // per line that can be worked on, change the line that is expected
   if( pLine ) {
    if( line.find( "p cnf" ) == 0 ) {
      stringstream s(line.substr(5));
      s >> variables >> promisedClauses;
    }  else {
      cerr << "c WARNING: did not find expected p cnf information" << endl;
      exit(-1);
    }
   }
   else if( !pLine )  {
     parsedClauses ++;
     // there is a clause!
     literals.clear();
     parseClause( line , literals );
     Compression compression;
     compression.variables = variables;
     compression.mapping = (Var*)malloc( sizeof(Var) * (variables) );
     for( Var v = 0; v < variables; ++v ) compression.mapping[v] = -1;
     for( int i = 0 ; i < literals.size(); ++ i ) {
       compression.mapping[i] = ((int) var(literals[i])) - 1; // since we have been shifting before as well, but now differnt internal representation
     }
     
     for( int i = 1 ; i < promisedClauses; ++ i ) { // one clause has been read already
	if( !getline( file, line ) ) { cerr << "c ERROR: cannot read all clauses from variable map!" << endl; exit(-1); }
	literals.clear();
	parseClause( line , literals );
	if( literals.size() != 1 ) { cerr << "c ERROR: parsed assignment clause is not unit!" << endl; exit(-1); }
	compression.trail.push_back(literals[0]);
     }
     cerr << "c parsed compression with " << variables << " variables and " << promisedClauses << " clauses" << endl;
     map_stack.push_back( compression );
   }
 }
 cerr << "c undo var map stack with " << map_stack.size() << " elements" << endl;
 return false;
}

void Dense::printStatistics( ostream& stream )
{
  cerr << "c [STAT] DENSE " << globalDiff << " gaps" << endl;
}
 
Lit Dense::giveNewLit(const Lit& l) const
{
  if( forward_mapping.size() == 0 ) return lit_Error;
  else return 
    forward_mapping[ var(l) ] == -1 ?
      lit_Undef : mkLit( forward_mapping[ var(l) ], sign(l) );
}

 
 
void Dense::destroy()
{
  
}