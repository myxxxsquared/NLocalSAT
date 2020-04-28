/*
 * Debug.h
 *
 *  Created on: Jan 18, 2013
 *      Author: tirrolo
 */

#ifndef PCASSODEBUG_H_
#define PCASSODEBUG_H_

#include <iostream>
#include "mtl/Vec.h"
#include "core/SolverTypes.h"

using namespace std;
using namespace Minisat;

namespace Debug {

static const int verbosity = 0;

inline void
PRINTLN(vec<Lit>& v){
	if(verbosity > 0){
			for( int i = 0; i < v.size(); i++ )
				cerr << (sign(v[i]) ? "-" : "") << var(v[i])+1 << " ";
			cerr << endl;
	}
}
inline void
PRINTLN(vec<Lit>& v, unsigned int limit){
	if(verbosity > 0){
		for( int i = 0; i < limit; i++ )
			cerr << (sign(v[i]) ? "-" : "") << var(v[i])+1 << " ";
		cerr << endl;
	}
}
inline void
PRINTLN(Lit& l){
	if(verbosity > 0){
		cerr << (sign(l) ? "-" : "") << var(l)+1 << " ";
		cerr << endl;
	}
}
inline void PRINTLN(string s){
	if(verbosity > 0) cerr << s << endl;
}
inline void PRINTLN(const char* s){
	if(verbosity > 0) cerr << s << endl;
}
inline void PRINTLN(int i){
	if(verbosity > 0) cerr << i << endl;
}
inline void PRINT(string s){
	if(verbosity > 0) cerr << s;
}
inline void PRINT(const char* s){
	if(verbosity > 0) cerr << s;
}
inline void PRINT(int i){
	if(verbosity > 0) cerr << i;
}
inline void STOP(void){
	assert(false);
}
inline void PRINTLN_DEBUG(vec<Lit>& v){
	if( verbosity > 2 )
		PRINTLN(v);
}
inline void
PRINTLN_DEBUG(Lit& l){
	if(verbosity > 2){
		cerr << (sign(l) ? "-" : "") << var(l)+1 << " ";
		cerr << endl;
	}
}
inline void PRINTLN_DEBUG(string s){
	if(verbosity > 2) cerr << s << endl;
}
inline void PRINTLN_DEBUG(const char* s){
	if(verbosity > 2) cout << s << endl;
}
inline void PRINT_DEBUG(string s){
	if(verbosity > 2) cerr << s;
}
inline void PRINT_DEBUG(const char* s){
	if(verbosity > 2) cout << s;
}
inline void PRINTLN_DEBUG(int i){
	if(verbosity > 2) cout << i << endl;
}
inline void PRINTLN_NOTE(vec<Lit>& v){
	if( verbosity > 1 )
		PRINTLN(v);
}
inline void
PRINTLN_NOTE(Lit& l){
	if(verbosity > 1){
		cerr << (sign(l) ? "-" : "") << var(l)+1 << " ";
		cerr << endl;
	}
}
inline void PRINTLN_NOTE(string s){
	if(verbosity > 1) cerr << s << endl;
}
inline void PRINTLN_NOTE(const char* s){
	if(verbosity > 1) cout << s << endl;
}
inline void PRINT_NOTE(string s){
	if(verbosity > 1) cerr << s;
}
inline void PRINT_NOTE(const char* s){
	if(verbosity > 1) cout << s;
}
inline void PRINTLN_NOTE(int i){
	if(verbosity > 1) cout << i << endl;
}
inline void PRINT_NOTE(int i){
	if(verbosity > 1) cout << i;
}

} /* namespace davide */
#endif /* DEBUG_H_ */
