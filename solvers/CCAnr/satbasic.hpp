
#ifndef SAT_BASIC_HEADER
#define SAT_BASIC_HEADER

#include "sat_defines.hpp"

#include <sys/times.h>
#include <string>

enum type
{
    SAT3,
    SAT5,
    SAT7,
    strSAT
};

#ifdef USE_PREDICT
// a data structure for sat predicting
struct sat_cnf
{
    int num_vars, num_clauses, num_edges;
    int (*edges)[2];
    int *output;
};
extern struct sat_cnf cnf_predict;

extern std::string gpu_list;
extern std::string load_model;
#endif // USE_PREDICT

// Define a data structure for a literal in the SAT problem.
struct lit
{
    int clause_num; //clause num, begin with 0
    int var_num;    //variable num, begin with 1
    int sense;      //is 1 for true literals, 0 for false literals.
};

extern int tries;
extern long long int step;

// parameters of the instance
extern int num_vars;    //var index from 1 to num_vars
extern int num_clauses; //clause index from 0 to num_clauses-1
extern int max_clause_len;
extern int min_clause_len;
extern int formula_len;
extern double avg_clause_len;
extern double ratio;

/* literal arrays */
extern lit *var_lit[MAX_VARS];            //var_lit[i][j] means the j'th literal of var i.
extern int var_lit_count[MAX_VARS];       //amount of literals of each var
extern lit *clause_lit[MAX_CLAUSES];      //clause_lit[i][j] means the j'th literal of clause i.
extern int clause_lit_count[MAX_CLAUSES]; // amount of literals in each clause

extern lit *org_clause_lit[MAX_CLAUSES];      //clause_lit[i][j] means the j'th literal of clause i.
extern int org_clause_lit_count[MAX_CLAUSES]; // amount of literals in each clause
extern int simplify;

/* Information about the variables. */
extern int score[MAX_VARS];
extern long long int time_stamp[MAX_VARS];
extern int conf_change[MAX_VARS];
extern int *var_neighbor[MAX_VARS];
extern int var_neighbor_count[MAX_VARS];
extern int fix[MAX_VARS];

/* Information about the clauses */
extern int clause_weight[MAX_CLAUSES];
extern int sat_count[MAX_CLAUSES];
extern int sat_var[MAX_CLAUSES];

#ifdef USE_RESULT
/* information about result */
extern int result_vars[MAX_VARS];
#endif //USE_RESULT

//unsat clauses stack
extern int unsat_stack[MAX_CLAUSES]; //store the unsat clause number
extern int unsat_stack_fill_pointer;
extern int this_try_best_unsat_stack_fill_pointer; // best unsat clause number
extern int index_in_unsat_stack[MAX_CLAUSES];      //which position is a clause in the unsat_stack

//variables in unsat clauses
extern int unsatvar_stack[MAX_VARS];
extern int unsatvar_stack_fill_pointer;
extern int index_in_unsatvar_stack[MAX_VARS];
extern int unsat_app_count[MAX_VARS]; //a varible appears in how many unsat clauses

//configuration changed decreasing variables (score>0 and confchange=1)
extern int goodvar_stack[MAX_VARS];
extern int goodvar_stack_fill_pointer;
extern int already_in_goodvar_stack[MAX_VARS];

//unit clauses preprocess
extern lit unitclause_queue[MAX_VARS];
extern int unitclause_queue_beg_pointer;
extern int unitclause_queue_end_pointer;
extern int clause_delete[MAX_CLAUSES];

/* Information about solution */
extern int cur_soln[MAX_VARS]; //the current solution, with 1's for True variables, and 0's for False variables

extern int ave_weight;
extern int delta_total_weight;
extern int scale_ave; //scale_ave==ave_weight*q_scale
extern struct tms time_start, time_stop;

//////////////////////////////////////////////////
// settings

//cutoff
extern int max_tries;
extern int max_flips;

extern int threshold;
extern float p_scale; //w=w*p+ave_w*q
extern float q_scale;

extern std::string inst;
extern int seed;

extern long long ls_no_improv_times;

extern bool aspiration_active;

#ifdef USE_RESULT
extern int result_samerate;
extern std::string result_file;
#endif

#define pop(stack) stack[--stack##_fill_pointer]
#define push(item, stack) stack[stack##_fill_pointer++] = item

void initsigint(void);
void free_memory(void);
bool parse_arguments(int argc, char **argv);
bool load();
void local_search(long long no_improv_times);
void print_solution(void);
int verify_sol(void);
void print_information(void);
int pick_var(void);
void flip(int flipvar);
void unsat(int clause);
void sat(int clause);

#ifdef USE_PREDICT
bool run_predict(void);
#endif // USE_PREDICT

#ifdef USE_RESULT
int build_result(char *filename);
#endif // USE_RESULT

#ifdef USE_INIT_PREDICT
extern double tryrage;
extern int tryside;
extern double predict_time;
#endif

#ifdef USE_PREDICT
extern std::string predictfile;
#endif

#endif // SAT_BASIC_HEADER
