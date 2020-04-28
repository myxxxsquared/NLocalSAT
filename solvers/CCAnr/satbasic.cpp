
#include "satbasic.hpp"

enum type probtype;

#ifdef USE_PREDICT
struct sat_cnf cnf_predict;
std::string gpu_list;
std::string load_model;
#endif // USE_PREDICT

int tries = 0;
long long int step = 0;

// parameters of the instance
int num_vars = 0;    //var index from 1 to num_vars
int num_clauses = 0; //clause index from 0 to num_clauses-1
int max_clause_len = 0;
int min_clause_len = 0;
int formula_len = 0;
double avg_clause_len = 0;
double ratio = 0;

/* literal arrays */
lit *var_lit[MAX_VARS] = {0};            //var_lit[i][j] means the j'th literal of var i.
int var_lit_count[MAX_VARS] = {0};       //amount of literals of each var
lit *clause_lit[MAX_CLAUSES] = {0};      //clause_lit[i][j] means the j'th literal of clause i.
int clause_lit_count[MAX_CLAUSES] = {0}; // amount of literals in each clause

lit *org_clause_lit[MAX_CLAUSES] = {0};      //clause_lit[i][j] means the j'th literal of clause i.
int org_clause_lit_count[MAX_CLAUSES] = {0}; // amount of literals in each clause
int simplify = 0;

/* Information about the variables. */
int score[MAX_VARS] = {0};
long long int time_stamp[MAX_VARS] = {0};
int conf_change[MAX_VARS] = {0};
int *var_neighbor[MAX_VARS] = {0};
int var_neighbor_count[MAX_VARS] = {0};
int fix[MAX_VARS] = {0};

/* Information about the clauses */
int clause_weight[MAX_CLAUSES] = {0};
int sat_count[MAX_CLAUSES] = {0};
int sat_var[MAX_CLAUSES] = {0};

#ifdef USE_RESULT
/* information about result */
int result_vars[MAX_VARS] = {0};
#endif // USE_RESULT

//unsat clauses stack
int unsat_stack[MAX_CLAUSES] = {0}; //store the unsat clause number
int unsat_stack_fill_pointer = 0;
int this_try_best_unsat_stack_fill_pointer = 0; // best unsat clause number
int index_in_unsat_stack[MAX_CLAUSES] = {0};    //which position is a clause in the unsat_stack

//variables in unsat clauses
int unsatvar_stack[MAX_VARS] = {0};
int unsatvar_stack_fill_pointer = 0;
int index_in_unsatvar_stack[MAX_VARS] = {0};
int unsat_app_count[MAX_VARS] = {0}; //a varible appears in how many unsat clauses

//configuration changed decreasing variables (score>0 and confchange=1)
int goodvar_stack[MAX_VARS] = {0};
int goodvar_stack_fill_pointer = 0;
int already_in_goodvar_stack[MAX_VARS] = {0};

//unit clauses preprocess
lit unitclause_queue[MAX_VARS] = {0};
int unitclause_queue_beg_pointer = 0;
int unitclause_queue_end_pointer = 0;
int clause_delete[MAX_CLAUSES] = {0};

/* Information about solution */
int cur_soln[MAX_VARS] = {0}; //the current solution, with 1's for True variables, and 0's for False variables

int ave_weight;
int delta_total_weight;
int scale_ave; //scale_ave==ave_weight*q_scale

struct tms time_start, time_stop;

//////////////////////////////////////////////////
// settings

//cutoff
int max_tries;
int max_flips;

int threshold;
float p_scale; //w=w*p+ave_w*q
float q_scale;

std::string inst;
int seed;

long long ls_no_improv_times;

bool aspiration_active;

#ifdef USE_RESULT
int result_samerate = 0;
std::string result_file;
#endif

#ifdef USE_INIT_PREDICT
double tryrage = 1.5;
int tryside = 1;
double predict_time;
#endif

#ifdef USE_PREDICT
std::string predictfile;
#endif
