/********************************************************************************[OutputFormula.cc]
Copyright (c) 2012, Kilian Gebhardt, Norbert Manthey, All rights reserved.
**************************************************************************************************/

#include "coprocessor-src/Coprocessor.h"
#include <stdio.h>

#include <sstream>
#include <fstream>

using namespace std;

using namespace Coprocessor;

void Preprocessor::outputFormula(const char *file, const char *varMap)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    printFormula(f);
    fclose(f);
}

void Preprocessor::getCNFinfo(int& vars, int& cls)
{
    if( !data.ok() ) { // unsat
      vars = solver->nVars(); cls = 1; return;
    }
  
    vec<Lit> & trail = solver->trail;
    vec<CRef> & clauses = solver->clauses;
    
    // count level 0 assignments 
    int level0 = 0;
    for (int i = 0; i < trail.size(); ++i)
    {
        if ((solver->level)(var(trail[i])) == 0) 
        {
            ++level0;
        }
    }
    
    vars = solver->nVars();
    cls = level0 + clauses.size();
}

void Preprocessor::printFormula(FILE * fd, bool clausesOnly) 
{
    if( !data.ok() ) { // unsat
      if( ! clausesOnly ) fprintf(fd,"p cnf 0 1\n0\n");
      else fprintf(fd,"0\n"); // print the empty clause!
      return;
    }
  
    vec<Lit> & trail = solver->trail;
    vec<CRef> & clauses = solver->clauses;
    
    if( ! clausesOnly ) { // calc and print header if necessary
      // count level 0 assignments 
      int level0 = 0;
      for (int i = 0; i < trail.size(); ++i)
      {
	  if ((solver->level)(var(trail[i])) == 0) 
	  {
	      ++level0;
	  }
      }
      // print header, if activated
      fprintf(fd,"p cnf %u %i\n", (solver->nVars()) ,level0 + clauses.size());
    }
    // print assignments
    for (int i = 0; i < trail.size(); ++i)
    {
        if ((solver->level)(var(trail[i])) == 0)
        {
            printLit(fd,  toInt(trail[i]));
            fprintf(fd,"0\n");
        }
    }
    // print clauses
    for (int i = 0; i < clauses.size(); ++i)
    {
        printClause(fd, clauses[i]);
    }   
}

inline void Preprocessor::printClause(FILE * fd, CRef cr) 
{
    Clause & c = ca[cr];
    if (c.mark()) return;
    stringstream s;
    for (int i = 0; i < c.size(); ++i)
      s << c[i] << " ";
    s << "0" << endl;
    
    fprintf(fd, "%s", s.str().c_str() );
    
}

inline void Preprocessor::printLit(FILE * fd, int l) 
{
    if (l % 2 == 0)
        fprintf(fd, "%i ", (l / 2) + 1);
    else
        fprintf(fd, "-%i ", (l/2) + 1);
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

int Preprocessor::parseModel(const string& filename)
{
  
  
 int solution = 0;
 vector<Lit> literals;
 string line;
 
 bool foundS = false;
 
  istream* fileptr;

  // open for reading
  if( filename == "" )
  {
    fileptr = &cin;
    cerr << "c parse model from stdin" << endl;
  } else {
    fileptr = new ifstream( filename.c_str(), ios_base::in);
    if( ! (*fileptr ) ) {
	cerr << "c ERROR: could not open model file " << filename << endl;
	return -1;
    }
    cerr << "c parse model from " << filename << endl;
  }

  istream& file = *fileptr;
 
  bool standartSAT = true;
 while( getline( file, line ) ) {
   // cerr << "c process line " << line << endl;
   // check satisfiability
    if( line.find( "s" ) == 0 ) { 
      foundS = true;
      if( line.find( "UNSATISFIABLE" ) != string::npos)
      {
	solution = 20;
	break;
      } else if( line.find( "UNKNOWN" ) != string::npos ) { 
	solution = 0;
	break;
      } else {
	solution = 10;
      }
    } else if( line.find( "UNSAT" ) == 0 ) {
      cerr << "c found non-standart UNSAT answer" << endl;
      solution = 20;
      foundS = true;
      break;
    } else if( line.find( "SAT" ) == 0 ) {
      cerr << "c found non-standart SAT answer" << endl;
      solution = 10;
      standartSAT = false;
      foundS = true;
      continue; // do not proceed on this line!
    }
    // check model
    if( line.find( "v" ) == 0 ) {
      literals.clear();
      parseClause( line.substr(2) , literals );
      for( uint32_t i = 0 ; i < literals.size(); ++i ) {
	// consider only variables of the original formula
	if( var(literals[i]) >= solver->model.size() ) {
	  solver->model.growTo( var(literals[i]) + 1);
	}
	// set polarity for other literals
	solver->model[ var(literals[i]) ] =  sign(literals[i]) ? l_False : l_True ;
      }
    } else if ( !standartSAT ) {
      // try to read the model in minisat/glucose format 
      cerr << "c try to extract non-standart model" << endl;
      literals.clear();
      parseClause( line , literals );
      cerr << "c found " << literals.size() << " values" << endl;
      for( uint32_t i = 0 ; i < literals.size(); ++i ) {
	// consider only variables of the original formula
	if( var(literals[i]) >= solver->model.size() ) {
	  solver->model.growTo( var(literals[i]) + 1);
	}
	// set polarity for other literals
	solver->model[ var(literals[i]) ] =  sign(literals[i]) ? l_False : l_True ;
      }
    }
    // ignore all the other lines
 }
 
 if( !foundS ) cerr << "c WARNING: could not find any solution information!" << endl;
 if( solution == 10 && !foundS ) cerr << "c WARNING: could not find any variable value information!" << endl;
 if( !standartSAT ) cerr << "c WARNING: result based on non-standart solution!" << endl;
 
 return solution;
}

bool Preprocessor::parseUndoInfo(const string& filename) {
  
 vector<Lit> literals;
 string line;
 
 bool foundP = false;
 
  ifstream file( filename.c_str(), ios_base::in);
  if( ! file ) {
    cerr << "c ERROR: could not open undo file " << filename << endl;
    return false;
  }

  int parsedClauses = 0;
  int promisedClauses = -1;

 while( getline( file, line ) ) {

   if( line.find( "p cnf" ) == 0 ) {
     stringstream s(line.substr(5));
     s >> formulaVariables >> promisedClauses;
     foundP = true;
   } else if( line.find( "c" ) == 0 ) {
     continue;
   } else {
     parsedClauses ++;
     // there is a clause!
     literals.clear();
     parseClause( line , literals );
     data.addToExtension( literals, literals[0] );
   }
 }
 
 if( !foundP ) {
   cerr << "c no file header found";
   return false;
 } else if( promisedClauses == - 1 || promisedClauses != parsedClauses) {
    cerr << "c ERROR: not sufficiently many clauses given in the file";
    return false;
 }
 
 dense.readUndoInfo( filename + ".map" );
 
 return true;
}

bool Preprocessor::writeUndoInfo(const string& filename, int originalVariables) {
 
  assert( solver->decisionLevel() == 0 && "cannot write undo information during search!" );
  
  ofstream file( filename.c_str(), ios_base::out);
  if( ! file ) {
    cerr << "c ERROR: could not open undo file " << filename << endl;
    return false;
  }

 int promisedClauses = 0;
 int writtenClauses = 0;
 const vector<Lit>& undo = data.getUndo();
 
 for( int i = 0 ; i < undo.size(); ++ i )
   if( undo[i] == lit_Undef ) promisedClauses ++;
 

 cerr << "c write undo for " << promisedClauses << " clauses and " <<  solver->trail.size() << " units" << endl;
   
 promisedClauses += solver->trail.size();
 
 if( originalVariables == -1 || ( formulaVariables < originalVariables ) ) { // use the formula variables, if they are smaller
  file << "p cnf " << formulaVariables << " " << promisedClauses << endl;
 } else {
  file << "p cnf " << formulaVariables << " " << promisedClauses << endl;
 }

 assert( (undo.size() == 0 || undo[0] == lit_Undef) && "first undo symbol has to be a lit_Undef");
 
 for( int i = 1; i < undo.size(); ++ i ) {
   stringstream s;
   while( i < undo.size() && undo[i] != lit_Undef) {
     s << undo[i] << " ";
     ++i;
   }
   s << "0" << endl;
   writtenClauses ++;
   file << s.str();
 }
 
 if( solver->trail.size() > 0 ) {
  stringstream s;
  for( int i = 0; i < solver->trail.size(); ++ i )
  {
      s << solver->trail[i] << " 0" << endl;
  }
  file << s.str();
 }
 
 return dense.writeUndoInfo( filename + ".map" );
}