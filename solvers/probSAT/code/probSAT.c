/**
 * probSAT version SAT14
 * uses only break!
 * code author: Adrian Balint
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/times.h>
#include <string.h>
#include <limits.h>
#include <float.h>
#include <getopt.h>
#include <signal.h>


// #define USE_PREDICT

#ifdef USE_PREDICT
int *network_predict;
double predict_time;

double predict_desc = 1.0;
#endif


#define MAXCLAUSELENGTH 10000
#define STOREBLOCK  20000
# undef LLONG_MAX
#define LLONG_MAX  9223372036854775807
#define BIGINT long long int
#define ABS(a) (((a) < 0) ? (-a) : (a))

#define GETOCCPOS(L) (2*abs(L)-(L<0))
void (*initLookUpTable)() = NULL;
void (*pickAndFlipVar)() = NULL;
int (*pickClauseIndex)() = NULL;
/*--------*/

/*----Instance data (independent from assignment)----*/
/** The numbers of variables. */
int numVars;
/** The number of clauses. */
int numClauses;
/** The number of literals. */
int numLiterals;
/** The value of the variables. The numbering starts at 1 and the possible values are 0 or 1. */
char *atom;
/** The clauses of the formula represented as: clause[clause_number][literal_number].
 * The clause and literal numbering start both at 1. literal and clause 0  is sentinel*/
int **clause;
/**min and max clause length*/
int maxClauseSize;
int minClauseSize;
/** The number of occurrence of each literal.*/
int *numOccurrence;
/** The clauses where each literal occurs. For literal i : occurrence[i+MAXATOMS][j] gives the clause =
 * the j'th occurrence of literal i.  */
int **occurrence;
int maxNumOccurences = 0; //maximum number of occurrences for a literal
/*--------*/

/**----Assignment dependent data----*/
/** The number of false clauses.*/
int numFalse;
/** Array containing all clauses that are false. Managed as a list.*/
int *falseClause;
/** whereFalse[i]=j tells that clause i is listed in falseClause at position j.  */
int *whereFalseOrCritVar;
/** The number of true literals in each clause. */
unsigned short *numTrueLit;
/*the number of clauses the variable i will make unsat if flipped
 * in the non-caching code breaks[i] is the break value of variable i-th variable
 * from the clause*/
int *breaks;
int *breaks2;
int bestVar;

/*----probSAT variables----*/
/** Look-up table for the functions. The values are computed in the initProbSAT method.*/

double probsBreak[MAXCLAUSELENGTH];
double probsBreak2[MAXCLAUSELENGTH];


/** contains the probabilities of the variables from one unsatisfied clause*/
double *probs;

/**probSAT parameters*/
double cb1; //parameter for break
double cb2; //parameter for break2

double eps = 1.0;
int fct = 0; //function to use 0= poly 1=exp
int caching = 0;
unsigned short randomC = 1;
int xor=0;
/*--------*/

/*----Input file variables----*/
FILE *fp;
char *fileName;
/*---------*/

/** Run time variables variables*/BIGINT seed;
BIGINT maxTries = LLONG_MAX;
BIGINT maxFlips = LLONG_MAX;
BIGINT flip;
BIGINT totalFlips=0;
int run = 1;
int try = 0;
int printSol = 0;
double tryTime;
double totalTime = 0.;
long ticks_per_second;

int bestNumFalse;
//parameters flags - indicates if the parameters were set on the command line
int cm_spec = 0, cb_spec = 0, cb2_spec = 0, fct_spec = 0, caching_spec = 0;
/*------statistic variables------*/
long vmrss, vmsize;
//BIGINT statdec1 = 0, statdec2 = 0, statdec3 = 0; //0<-1 1<-2 2-<3
//BIGINT statinc0 = 0, statinc1 = 0, statinc2 = 0; //0->1 1->2 2->3

int get_memory_usage_kb(long* vmrss_kb, long* vmsize_kb) {
	/* Get the the current process' status file from the proc filesystem */
	FILE* procfile = fopen("/proc/self/status", "r");

	long to_read = 8192;
	char buffer[to_read];
	int read = fread(buffer, sizeof(char), to_read, procfile);
	if (!read) {
		fprintf(stderr, "c an error occurred while reading memory usage!");
		return 0;
	}
	fclose(procfile);

	short found_vmrss = 0;
	short found_vmsize = 0;
	char* search_result;

	/* Look through proc status contents line by line */
	char delims[] = "\n";
	char* line = strtok(buffer, delims);

	while (line != NULL && (found_vmrss == 0 || found_vmsize == 0)) {
		search_result = strstr(line, "VmRSS:");
		if (search_result != NULL)
		{
			sscanf(line, "%*s %ld", vmrss_kb);
			found_vmrss = 1;
		}

		search_result = strstr(line, "VmSize:");
		if (search_result != NULL)
		{
			sscanf(line, "%*s %ld", vmsize_kb);
			found_vmsize = 1;
		}

		line = strtok(NULL, delims);
	}

	return (found_vmrss == 1 && found_vmsize == 1) ? 0 : 1;
}


void allocateMemory() {
	// Allocating memory for the instance data (independent from the assignment).
	numLiterals = numVars * 2;
	atom = (char*) malloc(sizeof(char) * (numVars + 1));
	clause = (int**) malloc(sizeof(int*) * (numClauses + 1));
	numOccurrence = (int*) malloc(sizeof(int) * (numLiterals + 1));
	occurrence = (int**) malloc(sizeof(int*) * (numLiterals + 2));

	// Allocating memory for the assignment dependent data.
	falseClause = (int*) malloc(sizeof(int) * (numClauses + 1));
	whereFalseOrCritVar = (int*) malloc(sizeof(int) * (numClauses + 1));
	numTrueLit = (unsigned short*) malloc(sizeof(unsigned short) * (numClauses + 1));

#ifdef USE_PREDICT
	network_predict = (int*) malloc(sizeof(int) * (numVars + 1));
#endif
}

void parseFile() {
	register int i, j;
	int lit, r;
	int clauseSize;
	int tatom;
	char c;
	long filePos;
	long totalOcc = 0;
	fp = NULL;
	fp = fopen(fileName, "r");
	if (fp == NULL) {
		fprintf(stderr, "c Error: Not able to open the file: %s\n", fileName);
		exit(-1);
	}

	// Start scanning the header and set numVars and numClauses
	for (;;) {
		c = fgetc(fp);
		if (c == 'c') //comment line - skip content
			do {
				c = fgetc(fp); //read the complete comment line until a eol is detected.
			} while ((c != '\n') && (c != EOF));
		else if (c == 'p') { //p-line detected
			if ((fscanf(fp, "%*s %d %d", &numVars, &numClauses))) //%*s should match with "cnf"
				break;
		} else {
			printf("c No parameter line found! Computing number of atoms and number of clauses from file!\n");
			r = fseek(fp, -1L, SEEK_CUR); //try to unget c
			if (r == -1) {
				fprintf(stderr, "c Error: Not able to seek in file: %s", fileName);
				exit(-1);
			}
			filePos = ftell(fp);
			if (r == -1) {
				fprintf(stderr, "c Error: Not able to obtain position in file: %s", fileName);
				exit(-1);
			}
			numVars = 0;
			numClauses = 0;
			for (; fscanf(fp, "%i", &lit) == 1;) {
				if (lit == 0)
					numClauses++;
				else {
					tatom = abs(lit);
					if (tatom > numVars)
						numVars = tatom;
				}
			}
			printf("c numVars: %d numClauses: %d\n", numVars, numClauses);

			r = fseek(fp, filePos, SEEK_SET); //try to rewind the file to the beginning of the formula
			if (r == -1) {
				fprintf(stderr, "c Error: Not able to seek in file: %s", fileName);
				exit(-1);
			}

			break;
		}
	}
	// Finished scanning header.
	//allocating memory to use!
	allocateMemory();

#ifdef USE_PREDICT
	int fileName_len = strlen(fileName);
	char *fileName_predict = (char*)malloc(fileName_len + 2);
	strcpy(fileName_predict, fileName);
	fileName_predict[fileName_len] = '_';
	fileName_predict[fileName_len+1] = 0;
	FILE *fpredict = fopen(fileName_predict, "r");
	free(fileName_predict);

	int predict_num_vars=-1, predict_num_clauses=-1;
	fscanf(fpredict, "%d %d %lf", &predict_num_vars, &predict_num_clauses, &predict_time);
	if(predict_num_vars != numVars)
	{
		printf("c Wrong Predcit File");
		exit(-1);
	}

	for(int thisi = 0; thisi < numVars; ++thisi)
		fscanf(fpredict, "%d", &network_predict[thisi]);

	printf("p");
	for(int i = 0; i < numVars; ++i)
		printf(" %d", network_predict[i]);
	printf("\n");
	fprintf(stderr, "loaded predict\n");
#endif

	maxClauseSize = 0;
	minClauseSize = MAXCLAUSELENGTH;
	int *numOccurrenceT = (int*) malloc(sizeof(int) * (numLiterals + 1));

	int freeStore = 0;
	int *tempClause = 0;
	for (i = 0; i < numLiterals + 1; i++) {
		numOccurrence[i] = 0;
		numOccurrenceT[i] = 0;
	}

	for (i = 1; i <= numClauses; i++) {
		if (freeStore < MAXCLAUSELENGTH) {
			tempClause = (int*) malloc(sizeof(int) * STOREBLOCK);
			freeStore = STOREBLOCK;
		}
		clause[i] = tempClause;
		clauseSize = 0;
		do {
			r = fscanf(fp, "%i", &lit);
			if (lit != 0) {
				clauseSize++;
				*tempClause++ = lit;
				numOccurrenceT[GETOCCPOS(lit)]++;
				if (numOccurrenceT[GETOCCPOS(lit)] > maxNumOccurences)
					maxNumOccurences = numOccurrenceT[GETOCCPOS(lit)];
				totalOcc++;
			} else {
				*tempClause++ = 0; //0 sentinel as literal!
			}
			freeStore--;
		} while (lit != 0);
		if (clauseSize > maxClauseSize)
			maxClauseSize = clauseSize;
		if (clauseSize < minClauseSize)
			minClauseSize = clauseSize;
	}
	occurrence[0] = (int*) malloc(sizeof(int) * (totalOcc + numLiterals + 2));
	int occpos = 0;
	for (i = 0; i < numLiterals + 1; i++) {
		occurrence[i] = (occurrence[0] + occpos);
		occpos += numOccurrenceT[i] + 1;
	}

	for (i = 1; i <= numClauses; i++) {
		j = 0;
		while ((lit = clause[i][j])) {
			occurrence[GETOCCPOS(lit)][numOccurrence[GETOCCPOS(lit)]++] = i;
			j++;
		}
		occurrence[GETOCCPOS(lit)][numOccurrence[GETOCCPOS(lit)]] = 0; //sentinel at the end!
	}
	probs = (double*) malloc(sizeof(double) * (maxClauseSize + 1));

	breaks = (int*) malloc(sizeof(int) * (numVars + 1));
	breaks2 = (int*) malloc(sizeof(int) * (numVars + 1));
	free(numOccurrenceT);
	free(numOccurrence);
	fclose(fp);
}

void init() {
	register int i, j;
	int critLit = 0, critLit2 = 0, lit;
	numFalse = 0;
	for (i = 1; i <= numClauses; i++) {
		numTrueLit[i] = 0;
		whereFalseOrCritVar[i] = 0;
	}

	for (i = 1; i <= numVars; i++) {
#ifdef USE_PREDICT
			atom[i] = ((rand() % 100 > 90) ? 1 : 0) ^ network_predict[i-1];
#else
			atom[i] = rand() % 2;
#endif
		breaks[i] = 0;
		breaks2[i] = 0;
	}
	//pass trough all clauses and apply the assignment previously generated
	for (i = 1; i <= numClauses; i++) {
		j = 0;
		critLit = 0;
		while ((lit = clause[i][j])) {
			if (atom[abs(lit)] == (lit > 0)) {
				numTrueLit[i]++;
				if (critLit) //we have already critlit1 set so we set now critli2
					critLit2 = lit;
				else
					//we set the first critLit
					critLit = lit;
				if (xor) {
					whereFalseOrCritVar[i] ^= abs(lit); //all satisfying variables are stored as xor in critVarX
				}
			}
			j++;
		}
		if (numTrueLit[i] == 2) { //we have to set the break2 value of critlit and critlit2 because a flip of these 2 will make the clause 1-sat
			breaks2[abs(critLit)]++;
			breaks2[abs(critLit2)]++;
		} else if (numTrueLit[i] == 1) {
			//if the clause has only one literal that causes it to be sat,
			//then this var. will break the sat of the clause if fliped.
			breaks[abs(critLit)]++;
			if (!xor) {
				whereFalseOrCritVar[i] = abs(critLit);
			}
		} else if (numTrueLit[i] == 0) {
			//add this clause to the list of unsat caluses.
			falseClause[numFalse] = i;
			whereFalseOrCritVar[i] = numFalse;
			numFalse++;
		}
	}
}



/** Checks whether the assignment from atom is a satisfying assignment.*/
int checkAssignment() {
	register int i, j;
	int sat, lit;
	for (i = 1; i <= numClauses; i++) {
		sat = 0;
		j = 0;
		while ((lit = clause[i][j])) {
			if (atom[abs(lit)] == (lit > 0))
				sat = 1;
			j++;
		}
		if (sat == 0)
			return 0;
	}
	return 1;
}


static int pickClauseRandom() {
	return rand() % numFalse;
}
//pick a clause with the flip counter and not randomly
static int pickClauseF() {
	return flip % numFalse;
}

// do not cache the break1 and break2 values
// but compute them on the fly

void pickAndFlipNCb2() {
	int bestVar;
	int rClause = falseClause[pickClauseIndex()]; //select clause according to pickClause heuristic
	double randPosition;
	double sumProb = 0;
	int xMakesSat = 0;
	int i = 0;
	int *ptr; //occurrence pointer
	int *lptr = &clause[rClause][0]; //literal pointer
	int lit;
	int iclause;
	while ((lit = (*lptr))) {
		breaks[i] = 0;
		breaks2[i] = 0;
		ptr=&occurrence[GETOCCPOS(-lit)][0];
		while ((iclause=*ptr)){
			if (numTrueLit[iclause] == 1)
				breaks[i]++;
			else
				if (numTrueLit[iclause]==2)
					breaks2[i]++;
			ptr++;
		}
		probs[i] = probsBreak[breaks[i]]*probsBreak2[breaks2[i]];
		sumProb += probs[i];
		i++;
		lptr++;
	}
	randPosition = (double) (rand()) / (RAND_MAX + 1.0) * sumProb;
	for (i = i - 1; i != 0; i--) {
		sumProb -= probs[i];
		if (sumProb <= randPosition)
			break;
	}
	bestVar = abs(clause[rClause][i]);

	//flip bestvar
	if (atom[bestVar])
		xMakesSat = -bestVar; //if bestVar=1 then all clauses containing -bestVar will be made sat after fliping bestVar
	else
		xMakesSat = bestVar; //if bestVar=0 then all clauses containing bestVar will be made sat after fliping bestVar
	atom[bestVar] = 1 - atom[bestVar];
	//1. Clauses that contain xMakeSAT will get SAT if not already SAT
	ptr = &occurrence[GETOCCPOS(xMakesSat)][0];
	while ((iclause = *ptr)) {
		//if the clause is unsat it will become SAT so it has to be removed from the list of unsat-clauses.
		if (numTrueLit[iclause] == 0) {
			//remove from unsat-list
			falseClause[whereFalseOrCritVar[iclause]] = falseClause[--numFalse]; //overwrite this clause with the last clause in the list.
			whereFalseOrCritVar[falseClause[numFalse]] = whereFalseOrCritVar[iclause];
		}
		numTrueLit[iclause]++; //the number of true Lit is increased.
		ptr++;
	}
	//2. all clauses that contain the literal -xMakesSat=0 will not be longer satisfied by variable bestVar
	//all this clauses contained bestVar as a satisfying literal
	ptr = &occurrence[GETOCCPOS(-xMakesSat)][0];
	while ((iclause = *ptr)) {
		if (numTrueLit[iclause] == 1) { //then xMakesSat=1 was the satisfying literal.
			falseClause[numFalse] = iclause;
			whereFalseOrCritVar[iclause] = numFalse;
			numFalse++;
		}
		numTrueLit[iclause]--;
		ptr++;
	}
}

// do not cache the break values but compute them on the fly
//(this is also the default implementation of WalkSAT in UBCSAT)
void pickAndFlipNC() {
	int bestVar;
	int rClause = falseClause[pickClauseIndex()]; //select clause according to pickClause heuristic
	double randPosition;
	double sumProb = 0;
	int xMakesSat = 0;
	int i = 0;
	int *ptr; //occurrence pointer
	int *lptr = &clause[rClause][0]; //literal pointer
	int lit;
	int iclause;
	while ((lit = (*lptr))) {
		breaks[i] = 0;
		ptr=&occurrence[GETOCCPOS(-lit)][0];
		while ((iclause=*ptr)){
			if (numTrueLit[iclause] == 1)
				breaks[i]++;
			ptr++;
		}
		probs[i] = probsBreak[breaks[i]];
		sumProb += probs[i];
		i++;
		lptr++;
	}
	randPosition = (double) (rand()) / (RAND_MAX + 1.0) * sumProb;
	for (i = i - 1; i != 0; i--) {
		sumProb -= probs[i];
		if (sumProb <= randPosition)
			break;
	}
	bestVar = abs(clause[rClause][i]);

	//flip bestvar
	if (atom[bestVar])
		xMakesSat = -bestVar; //if bestVar=1 then all clauses containing -bestVar will be made sat after fliping bestVar
	else
		xMakesSat = bestVar; //if bestVar=0 then all clauses containing bestVar will be made sat after fliping bestVar
	atom[bestVar] = 1 - atom[bestVar];
	//1. Clauses that contain xMakeSAT will get SAT if not already SAT
	ptr = &occurrence[GETOCCPOS(xMakesSat)][0];
	while ((iclause = *ptr)) {
		//if the clause is unsat it will become SAT so it has to be removed from the list of unsat-clauses.
		if (numTrueLit[iclause] == 0) {
			//remove from unsat-list
			falseClause[whereFalseOrCritVar[iclause]] = falseClause[--numFalse]; //overwrite this clause with the last clause in the list.
			whereFalseOrCritVar[falseClause[numFalse]] = whereFalseOrCritVar[iclause];
		}
		numTrueLit[iclause]++; //the number of true Lit is increased.
		ptr++;
	}
	//2. all clauses that contain the literal -xMakesSat=0 will not be longer satisfied by variable bestVar
	//all this clauses contained bestVar as a satisfying literal
	ptr = &occurrence[GETOCCPOS(-xMakesSat)][0];
	while ((iclause = *ptr)) {
		if (numTrueLit[iclause] == 1) { //then xMakesSat=1 was the satisfying literal.
			falseClause[numFalse] = iclause;
			whereFalseOrCritVar[iclause] = numFalse;
			numFalse++;
		}
		numTrueLit[iclause]--;
		ptr++;
	}
}

//Caching variant the break values of all variables are known in advance
//and are updated during the flip part
void pickAndFlipX(){
	int var;
	int rClause = falseClause[pickClauseIndex()];
	double sumProb = 0.0;
	double randPosition;
	register int i;
	int iclause;
	int *optr; //occurence pointer
	int xMakesSat; //tells which literal of x will make the clauses where it appears sat.
	i = 0;
	int *lptr = &clause[rClause][0]; //literal pointer
	while ((var = abs(*lptr))) {
		probs[i] = probsBreak[breaks[var]];
		sumProb += probs[i];
		i++;
		lptr++;
	}
	randPosition = (double) (rand()) / (RAND_MAX + 1.0) * sumProb;
	for (i = i - 1; i != 0; i--) {
		sumProb -= probs[i];
		if (sumProb <= randPosition)
			break;
	}
	bestVar = abs(clause[rClause][i]);

	//flip bestvar
	if (atom[bestVar])
		xMakesSat = -bestVar; //if bestVar=1 then all clauses containing -bestVar will be made sat after fliping bestVar
	else
		xMakesSat = bestVar; //if bestVar=0 then all clauses containing bestVar will be made sat after fliping bestVar
	atom[bestVar] = 1 - atom[bestVar];

	//1. all clauses that contain the literal xMakesSat will become SAT, if they where not already sat.
	optr = &occurrence[GETOCCPOS(xMakesSat)][0];
	while ((iclause = *optr)) {
		//if the clause is unsat it will become SAT so it has to be removed from the list of unsat-clauses.
		if (numTrueLit[iclause] == 0) {
			//remove from unsat-list
			falseClause[whereFalseOrCritVar[iclause]] = falseClause[--numFalse]; //overwrite this clause with the last clause in the list.
			whereFalseOrCritVar[falseClause[numFalse]] = whereFalseOrCritVar[iclause];
			whereFalseOrCritVar[iclause] = 0;
			//the score of x has to be decreased by one because x is critical and will break this clause if fliped.
			breaks[bestVar]++;
		} else {
			//if the clause is satisfied by only one literal then the score has to be increased by one for this var.
			//because fliping this variable will no longer break the clause
			if (numTrueLit[iclause] == 1) {
				breaks[whereFalseOrCritVar[iclause]]--;
			}
		}
		numTrueLit[iclause]++; //the number of true Lit is increased.
		whereFalseOrCritVar[iclause] ^= bestVar; //add the new satisfying variable to the critVar xor stack
		optr++;
	}
	//2. all clauses that contain the literal -xMakesSat=0 will not be longer satisfied by variable bestVar
	//all this clauses contained bestVar as a satisfying literal
	optr = &occurrence[GETOCCPOS(-xMakesSat)][0];
	while ((iclause = *optr)) {
		whereFalseOrCritVar[iclause] ^= bestVar; //remove the variable from the critVarX xor stack
		if (numTrueLit[iclause] == 1) { //then xMakesSat=1 was the satisfying literal.
			//this clause gets unsat.
			falseClause[numFalse] = iclause;
			whereFalseOrCritVar[iclause] = numFalse;
			numFalse++;
			//the score of bestVar has to be increased by one because it is not breaking any more for this clause.
			breaks[bestVar]--;
			//find which literal is true and make it critical and decrease its score
		} else if (numTrueLit[iclause] == 2) {
			//statdec2++;
			//by xor with the bestvar we have only one single variable in critVar and do not have to search for it
			breaks[whereFalseOrCritVar[iclause]]++;
		}
		numTrueLit[iclause]--;
		optr++;
	}
}

void pickAndFlipNX(){ //no Xor caching
	int var;
	int rClause = falseClause[pickClauseIndex()];
	//printFalseClause(rClause);
	double sumProb = 0.0;
	double randPosition;
	register int i;
	int iclause;
	int *optr; //occurence pointer
	int xMakesSat; //tells which literal of x will make the clauses where it appears sat.
	i = 0;
	int *lptr = &clause[rClause][0]; //literal pointer
	while ((var = abs(*lptr))) {
		probs[i] = probsBreak[breaks[var]];
		sumProb += probs[i];
		i++;
		lptr++;
	}
	randPosition = (double) (rand()) / (RAND_MAX + 1.0) * sumProb;
	for (i = i - 1; i != 0; i--) {
		sumProb -= probs[i];
		if (sumProb <= randPosition)
			break;
	}
	bestVar = abs(clause[rClause][i]);

	//flip bestvar
	if (atom[bestVar])
		xMakesSat = -bestVar; //if bestVar=1 then all clauses containing -bestVar will be made sat after fliping bestVar
	else
		xMakesSat = bestVar; //if bestVar=0 then all clauses containing bestVar will be made sat after fliping bestVar
	atom[bestVar] = 1 - atom[bestVar];

	//1. all clauses that contain the literal xMakesSat will become SAT, if they where not already sat.
	optr = &occurrence[GETOCCPOS(xMakesSat)][0];
	while ((iclause = *optr)) {
		//if the clause is unsat it will become SAT so it has to be removed from the list of unsat-clauses.
		if (numTrueLit[iclause] == 0) {
			//remove from unsat-list
			falseClause[whereFalseOrCritVar[iclause]] = falseClause[--numFalse]; //overwrite this clause with the last clause in the list.
			whereFalseOrCritVar[falseClause[numFalse]] = whereFalseOrCritVar[iclause];
			//whereFalseOrCritVar[iclause] = 0;
			//the score of x has to be decreased by one because x is critical and will break this clause if fliped.
			breaks[bestVar]++;
			whereFalseOrCritVar[iclause] = bestVar; //this variable is now critically responsible to make the sat. the clause
		} else {
			//if the clause is satisfied by only one literal then the score has to be increased by one for this var.
			//because fliping this variable will no longer break the clause
			if (numTrueLit[iclause] == 1) {
				breaks[whereFalseOrCritVar[iclause]]--;
			}
		}
		numTrueLit[iclause]++; //the number of true Lit is increased.
		optr++;
	}
	//2. all clauses that contain the literal -xMakesSat=0 will not be longer satisfied by variable bestVar
	//all this clauses contained bestVar as a satisfying literal
	optr = &occurrence[GETOCCPOS(-xMakesSat)][0];
	while ((iclause = *optr)) {
		if (numTrueLit[iclause] == 1) { //then xMakesSat=1 was the satisfying literal.
			//this clause gets unsat.
			falseClause[numFalse] = iclause;
			whereFalseOrCritVar[iclause] = numFalse;
			numFalse++;
			//the score of bestVar has to be increased by one because it is not breaking any more for this clause.
			breaks[bestVar]--;
			//statdec1++;
			//find which literal is true and make it critical and decrease its score
		} else if (numTrueLit[iclause] == 2) {
			//by xor with the bestvar we have only one single variable in critVar and do not have to search for it
			//breaks[whereFalseOrCritVar[iclause]]++;
			lptr = &clause[iclause][0];
			while ((var = abs(*lptr))) {
				if (((*lptr > 0) == atom[var])) { //x can not be the var anymore because it was flipped //&&(xMakesSat!=var)
					whereFalseOrCritVar[iclause] = var;
					breaks[var]++;
					break;
				}
				lptr++;
			}
		}
		numTrueLit[iclause]--;
		optr++;
	}
}


double elapsed_seconds(void) {
	double answer;
	static struct tms prog_tms;
	static long prev_times = 0;
	(void) times(&prog_tms);
	answer = ((double) (((long) prog_tms.tms_utime) - prev_times)) / ((double) ticks_per_second);
	prev_times = (long) prog_tms.tms_utime;
	return answer;
}


void printEndStatistics() {
	printf("\nc EndStatistics:\n");
	printf("c %-30s: %-9lli\n", "numFlips", flip);
	printf("c %-30s: %-8.2f\n", "avg. flips/variable", (double) totalFlips / (double) numVars);
	printf("c %-30s: %-8.2f\n", "avg. flips/clause", (double) totalFlips / (double) numClauses);
	fprintf(stderr, "c %-30s: %-9i\n", "totalTries", try);
	fprintf(stderr, "c %-30s: %-9lli\n", "totalFlips", totalFlips);
	fprintf(stderr, "c %-30s: %-8.0f\n", "flips/sec", (double) totalFlips / totalTime );
	fprintf(stderr, "c %-30s: %-8.3fsec\n", "Total CPU Time", totalTime);
}

void printFormulaProperties() {
	printf("\nc %-20s:  %s\n", "instance name", fileName);
	printf("c %-20s:  %d\n", "number of variables", numVars);
	printf("c %-20s:  %d\n", "number of literals", numLiterals);
	printf("c %-20s:  %d\n", "number of clauses", numClauses);
	printf("c %-20s:  %d\n", "MaxNumOccurences", maxNumOccurences);
	printf("c %-20s:  %d\n", "MaxClauseSize", maxClauseSize);
	printf("c %-20s:  %d\n", "MinClauseSize", minClauseSize);
	printf("c %-20s:  %6.4f\n", "Ratio", (float) numClauses / (float) numVars);
}

void printProbs() {
	int i;
	printf("c Probs values:\n");
	printf("c  ");
	for (i = 0; i <= 10; i++)
		printf(" %7i |", i);

	printf("\nc b");
	for (i = 0; i <= 10; i++) {
		if (probsBreak[i] != 0)
			printf(" %-6.5f |", probsBreak[i]);
	}
	printf("\n");
}

void printSolverParameters() {
	printf("\nc probSAT SC14 parameteres: \n");
	printf("c %-20s: %-20s\n", "using:", "only break");
	if (fct == 0)
		printf("c %-20s: %-20s\n", "using:", "polynomial function");
	else
		printf("c %-20s: %-20s\n", "using:", "exponential function");

	printf("c %-20s: %6.6f\n", "cb1", cb1);
	printf("c %-20s: %6.6f\n", "cb2", cb2);
	if (fct == 0) { //poly
		printf("c %-20s: %-20s\n", "function:", "probsBreak[break] = pow((eps + break), -cb1)*pow((eps + break), -cb2);");
		printf("c %-20s: %6.6f\n", "eps", eps);
	} else { //exp
		printf("c %-20s: %-20s\n", "function:", "probsBreak[break] = pow(cb1, -break)*pow(cb2, -break);");
	}
	if (caching)
		printf("c %-20s: %-20s\n", "using:", "caching of break values");
	else
		printf("c %-20s: %-20s\n", "using:", "no caching of break values");
	if (xor){
		printf("c %-20s: %-3s\n", "XOR implementation", "yes");
	}else{
		printf("c %-20s: %-3s\n", "XOR implementation", "no");
	}
	if (randomC)
		printf("c %-20s: %-20s\n", "using:", "random clause selection");
	else
		printf("c %-20s: %-20s\n", "using:", "flipCounter clause selection");
	printf("\nc general parameteres: \n");
	printf("c %-20s: %lli\n", "maxTries", maxTries);
	printf("c %-20s: %lli\n", "maxFlips", maxFlips);
	printf("c %-20s: %lli\n", "seed", seed);
	printf("c %-20s: \n", "-->Starting solver");
	fflush(stdout);
}

void printSolution() {
	register int i;
#ifdef USE_PREDICT
	int samerate = 0;
#endif
	printf("v ");
	for (i = 1; i <= numVars; i++) {
		if (atom[i] == 1)
			printf("%d ", i);
		else
			printf("%d ", -i);
#ifdef USE_PREDICT
		if(atom[i] == network_predict[i-1])
			samerate += 1;
#endif
	}
	printf("0\n");
#ifdef USE_PREDICT
	printf("c %lf\n", (double)samerate / (double)numVars);
#endif
}

void printStatsEndFlip() {
	if (numFalse < bestNumFalse) {
		bestNumFalse = numFalse;
	}
}
void printUsage() {
	printf("\n----------------------------------------------------------\n");
	printf("probSAT version SC14\n");
	printf("Authors: Adrian Balint, Uwe Schöning\n");
	printf("Ulm University - Institute of Theoretical Computer Science \n");
	printf("2014\n");
	printf("----------------------------------------------------------\n");
	printf("\nUsage of probSAT:\n");
	printf("./probSAT [options] <DIMACS CNF instance> [<seed>]\n");
	printf("\nprobSAT options:\n");
	printf("which function to use:\n");
	printf("--fct <0,1> : 0 =  polynomial; 1 = exponential [default = 0]\n");
	printf("--eps <double_value> : eps>0 (only valid when --fct 0)[default = 1.0]\n");
	printf("which constant to use in the functions:\n");
	printf("--cb1 <double_value> : constant for break [default = k dependet]\n");
	printf("--cb2 <double_value> : constant for break2 [default = 0 or 1 depending on the function]\n");
	printf("\nFurther options:\n");
	printf("--caching <0,1>, -c<0,1>  : use caching of break values \n");
	printf("--randomc , -r  : select unsat clause randomly (default: select it with the flip counter) \n");
	printf("--xor <0,1>  : use xor implementation \n");
	printf("--runs <int_value>, -t<int_value>  : maximum number of tries \n");
	printf("--maxflips <int_value> , -m<int_value>: number of flips per try \n");
	printf("--printSolution, -a : output assignment\n");
	printf("--help, -h : output this help\n");
	printf("----------------------------------------------------------\n\n");
}

void initPoly() {
	int i;
	for (i = 0; i <= maxNumOccurences; i++) {
		probsBreak[i] = pow((eps + i), -cb1);
		probsBreak2[i] = pow((1+i),-cb2);
	}
}

void initExp() {
	int i;
	for (i = 0; i <= maxNumOccurences; i++) {
		probsBreak[i] = pow(cb1, -i);
		probsBreak2[i] = pow(cb2, -i);
	}
}

void parseParameters(int argc, char *argv[]) {
	//define the argument parser
	static struct option long_options[] = {
			{"xor", required_argument, 0, 'x' },
			{"cb2", required_argument, 0, 2 },
			{"randomc", no_argument, 0, 'r' },
			{"fct", required_argument, 0, 'f' },
			{"caching", required_argument, 0, 'c' },
			{"eps", required_argument, 0, 'e' },
			{"cb1", required_argument, 0,'b' },
			{"runs", required_argument, 0, 't' },
			{"maxflips", required_argument, 0, 'm' },
			{"printSolution", no_argument, 0, 'a' },
			{"help",no_argument, 0, 'h' },
			{ 0, 0, 0, 0 } };

	while (optind < argc) {
		int index = -1;
		struct option * opt = 0;
		int result = getopt_long(argc, argv, "f:e:c:b:t:m:ahrx", long_options, &index); //
		if (result == -1)
			break; /* end of list */
		switch (result) {
		case 'x': //use xor caching
			xor = atoi(optarg);
			break;
		case 'h':
			printUsage();
			exit(0);
			break;
		case 'r': //select clause randomly
			randomC = 1;
			break;
		case 'c':
			caching = atoi(optarg);
			caching_spec = 1;
			break;
		case 'f':
			fct = atoi(optarg);
			fct_spec = 1;
			break;
		case 'e':
			eps = atof(optarg);
			if (eps <= 0) {
				printf("\nERROR: eps should >0!!!\n");
				exit(0);
			}
			break;
		case 'b':
			cb_spec = 1;
			break;
		case 2:
			cb2 = atof(optarg);
			cb2_spec = 1;
			break;
		case 't': //maximum number of tries to solve the problems within the maxFlips
			maxTries = atoi(optarg);
			break;
		case 'm': //maximum number of flips to solve the problem
			maxFlips = atoi(optarg);
			break;
		case 'a': //print assignment for variables at the end
			printSol = 1;
			break;
		case 0: /* all parameter that do not */
			/* appear in the optstring */
			opt = (struct option *) &(long_options[index]);
			printf("'%s' was specified.", opt->name);
			if (opt->has_arg == required_argument)
				printf("Arg: <%s>", optarg);
			printf("\n");
			break;
		default:
			printf("parameter not known!\n");
			printUsage();
			exit(0);
			break;
		}
	}
	if (optind == argc) {
		printf("ERROR: Parameter String not correct!\n");
		printUsage();
		exit(0);
	}
	fileName = *(argv + optind);

	if (argc > optind + 1) {
		seed = atoi(*(argv + optind + 1));
		if (seed == 0)
			printf("c there might be an error in the command line or is your seed 0?");
	} else
		seed = time(0);
}

void handle_interrupt() {
	printf("\nc caught signal... exiting\n ");
	tryTime = elapsed_seconds();
	printf("\nc UNKNOWN best(%d) (%-15.5fsec)\n", bestNumFalse, tryTime);
	printEndStatistics();
	fflush(NULL);
	exit(-1);
}

void setupSignalHandler() {
	signal(SIGTERM, handle_interrupt);
	signal(SIGINT, handle_interrupt);
	signal(SIGQUIT, handle_interrupt);
	signal(SIGABRT, handle_interrupt);
	signal(SIGKILL, handle_interrupt);
}
//probSAT is very sensitive to the cb parameter!
//This parameter settings are only applicable to randomly generated problems,
//do not use them for cradted instances
void setupParametersComp() {
	if (maxClauseSize <=3){
		cb1 = 2.06;
		eps = 0.9;
		fct = 0;
		caching = 1;
		randomC = 1;
		xor = 1;
		pickAndFlipVar = pickAndFlipX; //cache the break values
	} else 	if (maxClauseSize <=4){
		//cb1 = 2.85; //old setting
		cb1 = 3.0;
		fct = 1;
		caching = 1;
		randomC = 1;
		xor = 1;
		pickAndFlipVar = pickAndFlipX; //cache the break values
	}else 	if (maxClauseSize <=5){
		//cb1 = 3.75; //old setting
		cb1 = 3.88;
		fct = 1;
		caching = 1;
		randomC = 1;
		xor = 1;
		pickAndFlipVar =  pickAndFlipX;
	}else 	if (maxClauseSize <=6){
		//cb1 = 5.1; //old setting
		cb1 = 4.6;
		fct = 1;
		caching = 1;
		randomC = 1;
		xor =1;
		pickAndFlipVar = pickAndFlipX; //cache the break values
	}else{
		//cb1 = 5.4; //old setting
		cb1 = 4.6;
		fct = 1;
		caching = 1;
		randomC = 1;
		xor = 0;
		pickAndFlipVar = pickAndFlipNX;
		}
	if (randomC)
		pickClauseIndex = pickClauseRandom;
	else
		pickClauseIndex = pickClauseF;

	if (fct)
		initLookUpTable = initExp;
	else
		initLookUpTable = initPoly;
	//do not use the break2 value
	if (fct==0)
		cb2=0;
	else
		cb2=1;
}




int main(int argc, char *argv[]) {
	ticks_per_second = sysconf(_SC_CLK_TCK);
	tryTime = 0.;

	parseParameters(argc, argv);
	parseFile();

	printFormulaProperties();
	setupParametersComp(); //call only after parsing file!!!
	initLookUpTable(); //Initialize the look up table
	setupSignalHandler();
	printSolverParameters();
	srand(seed);
	for (try = 0; try < maxTries; try++) {
		init();
		bestNumFalse = numClauses;
		for (flip = 0; flip < maxFlips; flip++) {
			if (numFalse == 0)
				break;
			pickAndFlipVar();
			//printStatsEndFlip(); //update bestNumFalse
		}
		totalFlips += flip;
		tryTime = elapsed_seconds();
		totalTime += tryTime;
		if (numFalse == 0) {
			if (!checkAssignment()) {
				fprintf(stderr, "c ERROR the assignment is not valid!");
				printf("c UNKNOWN");
				return 0;
			} else {
				printEndStatistics();
				printf("s SATISFIABLE\n");
				if (printSol == 1)
					printSolution();
				return 10;
			}
		} else
			printf("c UNKNOWN best(%4d) current(%4d) (%-15.5fsec)\n", bestNumFalse, numFalse, tryTime);
	}
	printEndStatistics();
	if (maxTries > 1)
		printf("c %-30s: %-8.3fsec\n", "Mean time per try", totalTime / (double) try);
	return 0;
}

