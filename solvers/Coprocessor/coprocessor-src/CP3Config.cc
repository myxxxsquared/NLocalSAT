/************************************************************************************[CP3Config.cc]

Copyright (c) 2012-2013, Norbert Manthey

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "coprocessor-src/CP3Config.h"

#include "mtl/Sort.h"

using namespace Coprocessor;

const char* _cat = "COPROCESSOR 3";
const char* _cat2 = "COPROCESSOR  TECHNIQUES";
const char* _cat_bve = "COPROCESSOR 3 - BVE";
const char* _cat_bva = "COPROCESSOR 3 - BVA";
const char* _cat_bce = "COPROCESSOR 3 - BCE";
const char* _cat_la = "COPROCESSOR 3 - LA";
const char* _cat_cce = "COPROCESSOR 3 - CCE";
const char* _cat_dense = "COPROCESSOR 3 - DENSE";
const char* _cat_entailed = "COPROCESSOR 3 - ENTAILED";
const char* _cat_ee = "COPROCESSOR 3 - EQUIVALENCE ELIMINATION";
const char* _cat_ee_hash = "COPROCESSOR 3 - EQUIVALENCE ELIMINATION - HASHING";
const char* _cat_fm = "COPROCESSOR 3 - FOURIERMOTZKIN";
const char* _cat_hte = "COPROCESSOR 3 - HTE";
const char* _cat_pr = "COPROCESSOR 3 - PROBING";
const char* _cat_up = "COPROCESSOR 3 - UP";
const char* _cat_res = "COPROCESSOR 3 - RES";
const char* _cat_rew = "COPROCESSOR 3 - REWRITE";
const char* _cat_shuffle = "COPROCESSOR 3 - SHUFFLE";
const char* _cat_sls = "COPROCESSOR 3 - SLS";
const char* _cat_sub = "COPROCESSOR 3 - SUBSUMPTION";
const char* _cat_sym = "COPROCESSOR 3 - SYMMETRY";
const char* _cat_twosat = "COPROCESSOR 3 - TWOSAT";
const char* _cat_uhd = "COPROCESSOR 3 - UNHIDE";
const char* _cat_xor = "COPROCESSOR 3 - XOR";
const char* _cat_rat = "COPROCESSOR 3 - RAT Elimination";

CP3Config::CP3Config(const std::string& presetOptions) // add new options here!
:
 Config( &configOptions, presetOptions ),
 
 //
 // all the options for the object
 //
  
 opt_cp3_vars  (_cat, "cp3_vars",   "variable limit to enable CP3", 5000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_cp3_cls   (_cat, "cp3_cls",    "clause limit to enable CP3",   30000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_cp3_lits  (_cat, "cp3_lits",   "total literal limit to enable CP3",   50000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_cp3_ipvars(_cat, "cp3_ipvars", "variable limit to enable CP3 inprocessing", 5000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_cp3_ipcls (_cat, "cp3_ipcls",  "clause limit to enable CP3 inprocessing", 30000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_cp3_iplits(_cat, "cp3_iplits", "total literal limit to enable CP3 inprocessing", 50000000, IntRange(0, INT32_MAX), optionListPtr ), 
  
  opt_unlimited   (_cat, "cp3_limited",    "Limits for preprocessing techniques", true, optionListPtr ),
  opt_randomized  (_cat, "cp3_randomized", "Steps withing preprocessing techniques are executed in random order", false, optionListPtr ),
  opt_inprocessInt(_cat, "cp3_inp_cons",   "Perform Inprocessing after at least X conflicts", 20000, IntRange(0, INT32_MAX), optionListPtr ),
  opt_simplifyRounds(_cat, "cp3_iters",    "simplification rounds in preprocessing", 1, IntRange(0, INT32_MAX), optionListPtr ),
  opt_enabled     (_cat, "enabled_cp3",    "Use CP3", false, optionListPtr ),
  opt_inprocess   (_cat, "inprocess",      "Use CP3 for inprocessing", false, optionListPtr ),
   opt_exit_pp     (_cat, "cp3-exit-pp",   "terminate after preprocessing (1=exit,2=print formula cerr+exit 3=cout+exit)", 0, IntRange(0, 3), optionListPtr ),
  opt_randInp     (_cat, "randInp",        "Randomize Inprocessing", true, optionListPtr ),
  opt_inc_inp     (_cat, "inc-inp",        "increase technique limits per inprocess step", false, optionListPtr ),

#if defined TOOLVERSION && TOOLVERSION < 400
        opt_printStats ( true ), // do not print stats, if restricted binary is produced
        opt_verbose ( 0),        // do not talk during computation!
#else
        opt_printStats  (_cat, "cp3_stats",      "Print Technique Statistics", false, optionListPtr ),
          opt_verbose     (_cat, "cp3_verbose",    "Verbosity of preprocessor", 0, IntRange(0, 5), optionListPtr ),
#endif

// techniques
  opt_up          (_cat2, "up",            "Use Unit Propagation during preprocessing", false, optionListPtr ),
  opt_subsimp     (_cat2, "subsimp",       "Use Subsumption during preprocessing", false, optionListPtr ),
  opt_hte         (_cat2, "hte",           "Use Hidden Tautology Elimination during preprocessing", false, optionListPtr ),
#if defined TOOLVERSION && TOOLVERSION < 355
  opt_bce ( false ),
#else
  opt_bce         (_cat2, "bce",           "Use Blocked Clause Elimination during preprocessing", false, optionListPtr ),
#endif
#if defined TOOLVERSION && TOOLVERSION < 360
  opt_ent ( false ),
#else
  opt_ent         (_cat2, "ent",           "Use checking for entailed redundancy during preprocessing", false, optionListPtr ),
#endif
  opt_la          (_cat2, "la",            "Use (covered/asymmetric) Literal Addition during preprocessing", false, optionListPtr ),
  opt_cce         (_cat2, "cce",           "Use (covered) Clause Elimination during preprocessing", false, optionListPtr ),
  opt_rate        (_cat2, "rate",          "Use resolution asymmetric tautologye limination during preprocessing", false, optionListPtr ),
  opt_ee          (_cat2, "ee",            "Use Equivalence Elimination during preprocessing", false, optionListPtr ),
  opt_bve         (_cat2, "bve",           "Use Bounded Variable Elimination during preprocessing", false, optionListPtr ),
  opt_bva         (_cat2, "bva",           "Use Bounded Variable Addition during preprocessing", false, optionListPtr ),
  opt_unhide      (_cat2, "unhide",        "Use Unhiding (UHTE, UHLE based on BIG sampling)", false, optionListPtr ),
  opt_probe       (_cat2, "probe",         "Use Probing/Clause Vivification", false, optionListPtr ),
  opt_ternResolve (_cat2, "3resolve",      "Use Ternary Clause Resolution", false, optionListPtr ),
  opt_addRedBins  (_cat2, "addRed2",       "Use Adding Redundant Binary Clauses", false, optionListPtr ),
  opt_dense       (_cat2, "dense",         "Remove gaps in variables of the formula", false, optionListPtr ),
  opt_shuffle     (_cat2, "shuffle",       "Shuffle the formula, before the preprocessor is initialized", false, optionListPtr ),
  opt_simplify    (_cat2, "simplify",      "Apply easy simplifications to the formula", true, optionListPtr ),
  opt_symm        (_cat2, "symm",          "Do local symmetry breaking", false, optionListPtr ),
  opt_FM          (_cat2, "fm",            "Use the Fourier Motzkin transformation", false, optionListPtr ),

  opt_ptechs (_cat2, "cp3_ptechs", "techniques for preprocessing",0, optionListPtr ),
  opt_itechs (_cat2, "cp3_itechs", "techniques for inprocessing",0, optionListPtr ),

// use 2sat and sls only for high versions!
#if defined TOOLVERSION && TOOLVERSION < 301
  opt_threads ( 0),
  opt_sls ( false),       
  opt_sls_phase ( false),    
  opt_sls_flips ( 8000000),
  opt_xor ( false),    
  opt_rew ( false),    
  opt_twosat ( false),
  opt_twosat_init(false),
   opt_ts_phase (false),    
#else
   opt_threads     (_cat, "cp3_threads",    "Number of extra threads that should be used for preprocessing", 0, IntRange(0, INT32_MAX), optionListPtr ),
  opt_sls         (_cat2, "sls",           "Use Simple Walksat algorithm to test whether formula is satisfiable quickly", false, optionListPtr ),
  opt_sls_phase   (_cat2, "sls-phase",     "Use current interpretation of SLS as phase", false, optionListPtr ),
   opt_sls_flips   (_cat2, "sls-flips",     "Perform given number of SLS flips", 8000000, IntRange(-1, INT32_MAX), optionListPtr ),
  opt_xor         (_cat2, "xor",           "Reason with XOR constraints", false, optionListPtr ),
  opt_rew         (_cat2, "rew",           "Rewrite AMO constraints", false, optionListPtr ),
  opt_twosat      (_cat2, "2sat",          "2SAT algorithm to check satisfiability of binary clauses", false, optionListPtr ),
  opt_twosat_init (_cat2, "2sat1",         "2SAT before all other algorithms to find units", false, optionListPtr ),
  opt_ts_phase    (_cat2, "2sat-phase",    "use 2SAT model as initial phase for SAT solver", false, optionListPtr ),
#endif

// 
// Var and Cls LIMTS
// 

 opt_subsimp_vars(_cat, "cp3_susi_vars",     "variable limit to enable subsimp", 5000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_subsimp_cls (_cat, "cp3_susi_cls",      "clause limit to enable subsimp",   5000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_subsimp_lits(_cat, "cp3_susi_lits",     "total literal limit to enable subsimp",   10000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_hte_vars    (_cat, "cp3_hte_vars",      "variable limit to enable HTE", 1000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_hte_cls     (_cat, "cp3_hte_cls",       "clause limit to enable HTE",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_hte_lits(_cat, "cp3_hte_lits",          "total literal limit to enable HTE",   20000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_bce_vars    (_cat, "cp3_bce_vars",      "variable limit to enable BCE,CLE,CLA", 3000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_bce_cls     (_cat, "cp3_bce_cls",       "clause limit to enable BCE,CLE,CLA",   10000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_bce_lits(_cat, "cp3_bce_lits",          "total literal limit to enable BCE,CLE,CLA",   30000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_ent_vars    (_cat, "cp3_ent_vars",      "variable limit to enable ENT", INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ),
 opt_ent_cls     (_cat, "cp3_ent_cls",       "clause limit to enable ENT",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ),
 opt_ent_lits(_cat, "cp3_ent_lits",          "total literal limit to enable ENT",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_la_vars     (_cat, "cp3_la_vars",       "clause limit to enable CLA",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_la_cls      (_cat, "cp3_la_cls",        "clause limit to enable CLA",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_la_lits(_cat, "cp3_la_lits",            "total literal limit to enable CLA",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_cce_vars    (_cat, "cp3_cce_vars",      "variable limit to enable CCE", 5000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_cce_cls     (_cat, "cp3_cce_cls",       "clause limit to enable CCE",   30000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_cce_lits(_cat, "cp3_cce_lits",          "total literal limit to enable CCE",   50000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_rate_vars   (_cat, "cp3_rate_vars",     "variable limit to enable RATE", 1000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_rate_cls    (_cat, "cp3_rate_cls",      "clause limit to enable RATE",   2000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_rate_lits(_cat, "cp3_rate_lits",        "total literal limit to enable RATE",   10000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_ee_vars     (_cat, "cp3_ee_vars",       "variable limit to enable EE", 5000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_ee_cls      (_cat, "cp3_ee_cls",        "clause limit to enable EE",   20000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_ee_lits(_cat, "cp3_ee_lits",            "total literal limit to enable EE",   40000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_bve_vars    (_cat, "cp3_bve_vars",      "variable limit to enable BVE", 5000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_bve_cls     (_cat, "cp3_bve_cls",       "clause limit to enable BVE",   20000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_bve_lits(_cat, "cp3_bve_lits",          "total literal limit to enable BVE",   50000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_bva_vars    (_cat, "cp3_bva_vars",      "variable limit to enable BVA", 3000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_bva_cls     (_cat, "cp3_bva_cls",       "clause limit to enable BVA",   20000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_bva_lits(_cat, "cp3_bva_lits",          "total literal limit to enable BVA",   40000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_Ibva_vars   (_cat, "cp3_Ibva_vars",     "variable limit to enable IBVA", 1000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_Ibva_cls    (_cat, "cp3_Ibva_cls",      "clause limit to enable IBVA",   10000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_Ibva_lits(_cat, "cp3_Ibva_lits",        "total literal limit to enable IBVA",   40000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_Xbva_vars   (_cat, "cp3_Xbva_vars",     "variable limit to enable XBVA", 1000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_Xbva_cls    (_cat, "cp3_Xbva_cls",      "clause limit to enable XBVA",   5000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_Xbva_lits(_cat, "cp3_Xbva_lits",        "total literal limit to enable XBVA",   10000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_unhide_vars (_cat, "cp3_unhide_vars",   "variable limit to enable UNHIDE", 3000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_unhide_cls  (_cat, "cp3_unhide_cls",    "clause limit to enable UNHIDE",   10000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_unhide_lits(_cat, "cp3_unhide_lits",    "total literal limit to enable UNHIDE",   7000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_probe_vars  (_cat, "cp3_probe_vars",    "variable limit to enable PROBING", 3000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_probe_cls   (_cat, "cp3_probe_cls",     "clause limit to enable PROBING",   3000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_probe_lits(_cat, "cp3_probe_lits",      "total literal limit to enable PROBING",   30000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_viv_vars    (_cat, "cp3_viv_vars",      "variable limit to enable VIVIFICATION", 5000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_viv_cls     (_cat, "cp3_viv_cls",       "clause limit to enable VIVIFICATION",   10000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_viv_lits(_cat, "cp3_viv_lits",          "total literal limit to enable VIVIFICATION",   15000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_ternResolve_vars(_cat, "cp3_tRes_vars", "variable limit to enable 3RES", 1000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_ternResolve_cls (_cat, "cp3_tRes_cls",  "clause limit to enable 3RES",   20000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_ternResolve_lits(_cat, "cp3_tRes_lits", "total literal limit to enable 3RES",   50000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_addRedBins_vars (_cat, "cp3_aBin_vars", "variable limit to enable ADD2", INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ),
 opt_addRedBins_cls  (_cat, "cp3_aBin_cls",  "clause limit to enable ADD2",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_addRedBins_lits  (_cat, "cp3_aBin_lits", "total literal limit to enable ADD2",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_symm_vars   (_cat, "cp3_symm_vars",     "variable limit to enable SYMM", 3000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_symm_cls    (_cat, "cp3_symm_cls",      "clause limit to enable SYMM",   20000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_symm_lits(_cat, "cp3_symm_lits",        "total literal limit to enable SYMM",   15000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_fm_vars     (_cat, "cp3_fm_vars",       "variable limit to enable FM", 2000000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_fm_cls      (_cat, "cp3_fm_cls",        "clause limit to enable FM",   10000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_fm_lits(_cat, "cp3_fm_lits",            "total literal limit to enable FM",   20000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_xor_vars    (_cat, "cp3_xor_vars",      "variable limit to enable XOR", 700000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_xor_cls     (_cat, "cp3_xor_cls",       "clause limit to enable XOR",   3000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_xor_lits(_cat, "cp3_xor_lits",          "total literal limit to enable XOR",   5000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_sls_vars    (_cat, "cp3_sls_vars",      "variable limit to enable SLS", 500000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_sls_cls     (_cat, "cp3_sls_cls",       "clause limit to enable SLS",   500000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_sls_lits(_cat, "cp3_sls_lits",          "total literal limit to enable SLS",   4000000, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_rew_vars    (_cat, "cp3_rew_vars",      "variable limit to enable REW", INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ),
 opt_rew_cls     (_cat, "cp3_rew_cls",       "clause limit to enable REW",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ), 
 opt_rew_lits(_cat, "cp3_rew_lits",          "total literal limit to enable REW",   INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ), 
 
 

#if defined TOOLVERSION // debug only, if no version is given!
  opt_debug ( false),       
  opt_check ( 0),
   opt_log (0),
  printAfter ( 0),
#else
  opt_debug       (_cat, "cp3-debug",   "do more debugging", false, optionListPtr ),
  opt_check       (_cat, "cp3-check",   "check solver state during simplification and before returning control to solver",  0, IntRange(0, 3), optionListPtr ),
   opt_log         (_cat,  "cp3-log",    "Output log messages until given level", 0, IntRange(0, 3), optionListPtr ),
  printAfter    (_cat,  "cp3-print",  "print intermediate formula after given technique", 0, optionListPtr ),
#endif
  
//
// parameters BVE
//

#if defined TOOLVERSION && TOOLVERSION < 302
 opt_par_bve(1),
 opt_bve_verbose(0),
#else
  opt_par_bve         (_cat_bve, "cp3_par_bve",    "Parallel BVE: 0 never, 1 heur., 2 always", 1,IntRange(0,2), optionListPtr ),
   opt_bve_verbose     (_cat_bve, "cp3_bve_verbose",    "Verbosity of preprocessor", 0, IntRange(0, 3), optionListPtr ),
#endif
 
   opt_bve_limit       (_cat_bve, "cp3_bve_limit", "perform at most this many clause derefferences", 25000000, IntRange(-1, INT32_MAX), optionListPtr ),
   opt_learnt_growth   (_cat_bve, "cp3_bve_learnt_growth", "Keep C (x) D, where C or D is learnt, if |C (x) D| <= max(|C|,|D|) + N", 0, IntRange(-1, INT32_MAX), optionListPtr ),
   opt_resolve_learnts (_cat_bve, "cp3_bve_resolve_learnts", "Resolve learnt clauses: 0: off, 1: original with learnts, 2: 1 and learnts with learnts", 0, IntRange(0,2), optionListPtr ),
  opt_unlimited_bve   (_cat_bve, "bve_unlimited",  "perform bve test for Var v, if there are more than 10 + 10 or 15 + 5 Clauses containing v", false, optionListPtr ),
  opt_bve_strength    (_cat_bve, "bve_strength",  "do strengthening during bve", true, optionListPtr ),
   opt_bve_reduce_lits(_cat_bve, "bve_red_lits",  "0=reduce number of literals, 1=reduce number of clauses,2=reduce any of the two,3 reduce both", 0, IntRange(0,3), optionListPtr ),
  opt_bve_findGate    (_cat_bve, "bve_gates",  "try to find variable AND gate definition before elimination", true, optionListPtr ),
  opt_force_gates     (_cat_bve, "bve_force_gates", "Force gate search (slower, but probably more eliminations and blockeds are found)", false, optionListPtr ),
 // pick order of eliminations
   opt_bve_heap        (_cat_bve, "cp3_bve_heap"   ,  "0: minimum heap, 1: maximum heap, 2: random, 3: ratio pos/neg smaller+less, 4: ratio pos/neg smaller+greater, 5: ratio pos/neg greater+less, 6: ratio pos/neg greater + greater, 7-10: same as 3-6, but inverse measure order", 0, IntRange(0,10), optionListPtr ),
 // increasing eliminations
   opt_bve_grow        (_cat_bve, "bve_cgrow"  , "number of additional clauses per elimination", 0, IntRange(-INT32_MAX,INT32_MAX), optionListPtr ),
   opt_bve_growTotal   (_cat_bve, "bve_cgrow_t", "total number of additional clauses", INT32_MAX, IntRange(0,INT32_MAX), optionListPtr ),
  opt_totalGrow       (_cat_bve, "bve_totalG" , "Keep track of total size of formula when allowing increasing eliminations", false, optionListPtr ),
  
  opt_bve_bc          (_cat_bve, "bve_BCElim",    "Eliminate Blocked Clauses", true, optionListPtr ),
  heap_updates         (_cat_bve, "bve_heap_updates",    "Always update variable heap if clauses / literals are added or removed, 2 add variables, if not in heap", 1, IntRange(0,2), optionListPtr ),
  opt_bce_only        (_cat_bve, "bce_only",    "Only remove blocked clauses but do not resolve variables.", false, optionListPtr ),
  opt_print_progress  (_cat_bve, "bve_progress", "Print bve progress stats.", false, optionListPtr ),
  opt_bveInpStepInc      (_cat_bve, "cp3_bve_inpInc","increase for steps per inprocess call", 5000000, IntRange(0, INT32_MAX), optionListPtr ),

#if defined TOOLVERSION && TOOLVERSION < 302
par_bve_threshold(0),
postpone_locked_neighbors (1),
opt_minimal_updates (false),
#else
par_bve_threshold (_cat_bve, "par_bve_th", "Threshold for use of BVE-Worker", 10000, IntRange(0,INT32_MAX), optionListPtr ),
postpone_locked_neighbors (_cat_bve, "postp_lockd_neighb", "Postpone Elimination-Check if more neighbors are locked", 3, IntRange(0,INT32_MAX), optionListPtr ),
opt_minimal_updates       (_cat_bve, "par_bve_min_upd", "Omit LitOcc and Heap updates to reduce locking", false, optionListPtr ),
#endif

//
// BVA
//
opt_bva_push             (_cat_bva, "cp3_bva_push",    "push variables back to queue (0=none,1=original,2=all)", 2, IntRange(0, 2), optionListPtr ),
opt_bva_VarLimit         (_cat_bva, "cp3_bva_Vlimit",  "use BVA only, if number of variables is below threshold", 3000000, IntRange(-1, INT32_MAX), optionListPtr ),
opt_bva_Alimit           (_cat_bva, "cp3_bva_limit",   "number of steps allowed for AND-BVA", 1200000, IntRange(0, INT32_MAX), optionListPtr ),
opt_Abva                 (_cat_bva, "cp3_Abva",        "perform AND-bva", true, optionListPtr ),
opt_bvaInpStepInc        (_cat_bva, "cp3_bva_incInp",  "increases of number of steps per inprocessing", 80000, IntRange(0, INT32_MAX), optionListPtr ),
opt_Abva_heap            (_cat_bva, "cp3_Abva_heap",   "0: minimum heap, 1: maximum heap, 2: random, 3: ratio pos/neg smaller+less, 4: ratio pos/neg smaller+greater, 5: ratio pos/neg greater+less, 6: ratio pos/neg greater + greater, 7-10: same as 3-6, but inverse measure order", 1, IntRange(0,10), optionListPtr ),

opt_bvaComplement        (_cat_bva, "cp3_bva_compl",   "treat complementary literals special", true, optionListPtr ),
opt_bvaRemoveDubplicates (_cat_bva, "cp3_bva_dupli",   "remove duplicate clauses", true, optionListPtr ),
opt_bvaSubstituteOr      (_cat_bva, "cp3_bva_subOr",   "try to also substitus disjunctions", false, optionListPtr ),

#if defined TOOLVERSION  
bva_debug (0),
#else
bva_debug (_cat_bva, "bva-debug",       "Debug Output of BVA", 0, IntRange(0, 4), optionListPtr ),
#endif

#if defined TOOLVERSION  && TOOLVERSION < 350
opt_bvaAnalysis (false),
opt_Xbva (false),
opt_Ibva (false),
opt_bvaAnalysisDebug (0),
opt_bva_Xlimit (100000000),
opt_bva_Ilimit (100000000),
opt_Xbva_heap (1),
opt_Ibva_heap (1),
#else
 #if defined TOOLVERSION
 opt_bvaAnalysisDebug (0),
#else
 opt_bvaAnalysisDebug     (_cat_bva, "cp3_bva_ad",      "experimental analysis", 0, IntRange(0, 4), optionListPtr ),
#endif
opt_bva_Xlimit           (_cat_bva, "cp3_bva_Xlimit",   "number of steps allowed for XOR-BVA", 100000000, IntRange(0, INT32_MAX), optionListPtr ),
opt_bva_Ilimit           (_cat_bva, "cp3_bva_Ilimit",   "number of steps allowed for ITE-BVA", 100000000, IntRange(0, INT32_MAX), optionListPtr ),
opt_Xbva_heap            (_cat_bva, "cp3_Xbva_heap",   "0: minimum heap, 1: maximum heap, 2: random, 3: ratio pos/neg smaller+less, 4: ratio pos/neg smaller+greater, 5: ratio pos/neg greater+less, 6: ratio pos/neg greater + greater, 7-10: same as 3-6, but inverse measure order", 1, IntRange(0,10), optionListPtr ),
opt_Ibva_heap            (_cat_bva, "cp3_Ibva_heap",   "0: minimum heap, 1: maximum heap, 2: random, 3: ratio pos/neg smaller+less, 4: ratio pos/neg smaller+greater, 5: ratio pos/neg greater+less, 6: ratio pos/neg greater + greater, 7-10: same as 3-6, but inverse measure order", 1, IntRange(0,10), optionListPtr ),
opt_Xbva                 (_cat_bva, "cp3_Xbva",       "perform XOR-bva (1=half gates,2=full gates)", 0, IntRange(0, 2), optionListPtr ),
opt_Ibva                 (_cat_bva, "cp3_Ibva",       "perform ITE-bva (1=half gates,2=full gates)", 0, IntRange(0, 2), optionListPtr ),
#endif  
//
// BCE
//
orderComplements (_cat_bce,"bce-compl", "test literals for BCE based on the number of occurrences of the complementary literal", true , optionListPtr ),
bceBinary (_cat_bce,"bce-bin", "allow to remove binary clauses during BCE", false , optionListPtr ),
bceLimit (_cat_bce,"bce-limit", "number of pairwise clause comparisons before interrupting BCE", 100000000, IntRange(0, INT32_MAX) , optionListPtr ),
opt_bce_bce(_cat_bce,"bce-bce", "actually perform BCE", true, optionListPtr ),
opt_bce_cle(_cat_bce,"bce-cle", "perform covered literal elimination (CLE)", false, optionListPtr ),
opt_bce_cla(_cat_bce,"bce-cla", "perform covered literal elimination (CLA)", false, optionListPtr ),
opt_bce_cle_conservative(_cat_bce,"bce-cle-cons", "conservative cle if taut. resolvents are present", false, optionListPtr ),
opt_bceInpStepInc (_cat_bce,"bce-incInp", "number of steps given to BCE for another inprocessign round", 10000, IntRange(0, INT32_MAX) , optionListPtr ),
#if defined TOOLVERSION
opt_bce_verbose (0),
opt_cle_debug(false),
#else
opt_bce_verbose (_cat_bce, "bce-verbose", "be verbose during BCE", 0, IntRange(0, 3), optionListPtr ),
opt_bce_debug (_cat_bce, "bce-debug", "output debug info during BCE", false, optionListPtr ),
#endif

//
// Literal Addition
//
opt_la_cla(_cat_la,"la-cla", "perform covered literal addition (CLA)", true, optionListPtr ),
opt_la_ala(_cat_la,"la-ala", "perform asymmetric literal addition (ALA)", false, optionListPtr ),
claLimit (_cat_la,"cla-limit", "number of pairwise clause comparisons before interrupting LA", 100000000, IntRange(0, INT32_MAX) , optionListPtr ),
claStepSize(_cat_la,"la-claStep", "number of extension literals per step so that literals are removed randomly", 4, IntRange(1, INT32_MAX) , optionListPtr ), 
claStepMax(_cat_la,"la-claMax", "number of extension literals per step so that literals are removed randomly", 2, IntRange(1, INT32_MAX) , optionListPtr ), 
claIterations(_cat_la,"la-claIter", "number of extension literals per step so that literals are removed randomly", 1, IntRange(1, INT32_MAX) , optionListPtr ), 

alaLimit(_cat_la,"ala-limit", "number of pairwise clause comparisons before interrupting LA", 100000000, IntRange(0, INT32_MAX) , optionListPtr ),
alaIterations(_cat_la,"la-alaIter", "number of extension literals per step so that literals are removed randomly", 1, IntRange(1, INT32_MAX) , optionListPtr ), 
ala_binary(_cat_la, "la-alaBin", "use binary clauses for ALA", false, optionListPtr ),
#if defined TOOLVERSION
opt_la_debug(false),
#else
opt_la_debug (_cat_la, "la-debug", "output debug info during LA", false, optionListPtr ),
#endif

//
// CCE
//
  opt_cceSteps         (_cat_cce, "cp3_cce_steps", "Number of steps that are allowed per iteration", 2000000, IntRange(-1, INT32_MAX), optionListPtr ),
  opt_ccelevel         (_cat_cce, "cp3_cce_level", "none, ALA+ATE, CLA+ATE, ALA+CLA+BCE", 3, IntRange(0, 3), optionListPtr ),
  opt_ccePercent    (_cat_cce, "cp3_cce_sizeP", "percent of max. clause size for clause elimination (excluding)", 40, IntRange(0,100), optionListPtr ),
#if defined TOOLVERSION  
 cce_debug_out (0),
#else
  cce_debug_out (_cat_cce, "cce-debug", "debug output for clause elimination",0, IntRange(0,4) , optionListPtr ),
#endif
   opt_cceInpStepInc      (_cat_cce, "cp3_cce_inpInc","increase for steps per inprocess call", 60000, IntRange(0, INT32_MAX), optionListPtr ),

//
// RAT Elimination
//
rate_orderComplements(_cat_rat, "rat-compl", "sort according to nr. of complements", true, optionListPtr ),
rate_Limit(_cat_rat,"rate-limit", "number of pairwise clause comparisons before interrupting RATE", 9000000000, Int64Range(0, INT64_MAX) , optionListPtr ),
opt_rate_debug (_cat_rat, "rate-debug", "debug output for RAT elimination",0, IntRange(0,4) , optionListPtr ),
rate_minSize(_cat_rat,"rate-min", "minimal clause size for RAT elimination", 3, IntRange(2, INT32_MAX) , optionListPtr ),

//
// Dense
//
#if defined TOOLVERSION  
dense_debug_out (0),
#else
dense_debug_out (_cat_dense, "cp3_dense_debug", "print debug output to screen",0, IntRange(0,2) , optionListPtr ),
#endif
opt_dense_fragmentation  (_cat_dense, "cp3_dense_frag", "Perform densing, if fragmentation is higher than (percent)", 0, IntRange(0, 100), optionListPtr ),
opt_dense_store_forward  (_cat_dense, "cp3_dense_forw", "store forward mapping",false, optionListPtr ),
opt_dense_keep_assigned  (_cat_dense, "cp3_keep_set",   "keep already assigned literals",false, optionListPtr ),
//
// Entailed
//
#if defined TOOLVERSION && TOOLVERSION < 360
opt_entailed_minClsSize (INT32_MAX),
#else
opt_entailed_minClsSize  (_cat_entailed, "ent-min",    "minimum clause size that is tested", 2, IntRange(2, INT32_MAX), optionListPtr ),
#endif
#if defined TOOLVERSION 
entailed_debug(0),
#else
entailed_debug(_cat_entailed, "ent-debug",       "Debug Output for ENT reasoning", 0, IntRange(0, 5), optionListPtr ),
#endif

//
// Equivalence
//
#if defined TOOLVERSION  && TOOLVERSION < 350
opt_ee_level            ( 0),
opt_ee_gate_limit       ( 0),
opt_ee_circuit_iters    ( 2),
opt_ee_eagerEquivalence (false),
opt_eeGateBigFirst   (false),
opt_ee_aagFile (0),
#else
opt_ee_level            (_cat_ee, "cp3_ee_level",    "EE on BIG, gate probing, structural hashing", 0, IntRange(0, 3), optionListPtr ),
opt_ee_gate_limit       (_cat_ee, "cp3_ee_glimit",   "step limit for structural hashing", INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ),
opt_ee_circuit_iters    (_cat_ee, "cp3_ee_cIter",    "max. EE iterations for circuit (-1 == inf)", 2, IntRange(-1, INT32_MAX), optionListPtr ),
opt_ee_eagerEquivalence (_cat_ee, "cp3_eagerGates",  "do handle gates eagerly", true, optionListPtr ),
opt_eeGateBigFirst   (_cat_ee, "cp3_BigThenGate", "detect binary equivalences before going for gates [should not be disabled!]", true, optionListPtr ),
opt_ee_aagFile            (_cat_ee, "ee_aag", "write final circuit to this file",0, optionListPtr ),
#endif
#if defined TOOLVERSION  
ee_debug_out (0),
#else
ee_debug_out            (_cat_ee, "ee_debug", "print debug output to screen", 0, IntRange(0, 3), optionListPtr ),
#endif
opt_eeSub            (_cat_ee, "ee_sub",          "do subsumption/strengthening during applying equivalent literals?", false, optionListPtr ),
opt_eeFullReset      (_cat_ee, "ee_reset",        "after Subs or Up, do full reset?", false, optionListPtr ),
opt_ee_limit         (_cat_ee, "cp3_ee_limit",    "step limit for detecting equivalent literals", 1000000, IntRange(0, INT32_MAX), optionListPtr ),
opt_ee_inpStepInc       (_cat_ee, "cp3_ee_inpInc",   "increase for steps per inprocess call", 200000, IntRange(0, INT32_MAX), optionListPtr ),
opt_ee_bigIters         (_cat_ee, "cp3_ee_bIter",    "max. iteration to perform EE search on BIG", 3, IntRange(0, INT32_MAX), optionListPtr ),
opt_ee_iterative        (_cat_ee, "cp3_ee_it",       "use the iterative BIG-EE algorithm", false, optionListPtr ),
opt_EE_checkNewSub   (_cat_ee, "cp3_ee_subNew",   "check for new subsumptions immediately when adding new clauses", false, optionListPtr ),
opt_ee_eager_frozen     (_cat_ee, "ee_freeze_eager", "exclude frozen variables eagerly from found equivalences", false, optionListPtr ),
//
// Structural hashing options
//
#if defined TOOLVERSION  && TOOLVERSION < 350
circ_AND        (false),
circ_ITE        (false),
circ_XOR        (false),
circ_ExO        (false),
circ_genAND     (false),
circ_FASUM      (false),
circ_BLOCKED    (false),
circ_AddBlocked (false),
circ_NegatedI   (false),
circ_Implied    (false),
#else
circ_AND        (_cat_ee_hash, "cp3_extAND",      "extract AND gates", true, optionListPtr),
circ_ITE        (_cat_ee_hash, "cp3_extITE",      "extract ITE gates", false, optionListPtr),
circ_XOR        (_cat_ee_hash, "cp3_extXOR",      "extract XOR gates", false, optionListPtr),
circ_ExO        (_cat_ee_hash, "cp3_extExO",      "extract ExO gates", false, optionListPtr),
circ_genAND     (_cat_ee_hash, "cp3_genAND",      "extract generic AND gates", false, optionListPtr),
circ_FASUM      (_cat_ee_hash, "cp3_extHASUM",    "extract full adder sum bit gates", false, optionListPtr),
circ_BLOCKED    (_cat_ee_hash, "cp3_extBlocked",  "extract gates, that can be found by blocked clause addition", false, optionListPtr),
circ_AddBlocked (_cat_ee_hash, "cp3_addBlocked",  "clauses that are used to extract blocked gates will be added eagerly (soundness)", false, optionListPtr),
circ_NegatedI   (_cat_ee_hash, "cp3_extNgtInput", "extract gates, where inputs come from the same variable", true, optionListPtr),
circ_Implied    (_cat_ee_hash, "cp3_extImplied",  "do search binary clause also in BIG with dfs", true, optionListPtr),
#endif
/// temporary Boolean flag to quickly enable debug output for the whole file
#if defined TOOLVERSION  
circ_debug_out (false),
#else
circ_debug_out      (_cat_ee_hash, "cp3_circ_debug",  "print debug output for circuitextraction", false, optionListPtr),
#endif

//
// Fourier Motzkin
//
opt_fm_max_constraints(_cat_fm, "cp3_fm_maxConstraints", "number of constraints that are allows", 200000, IntRange(0, INT32_MAX), optionListPtr ),
opt_fmLimit        (_cat_fm, "cp3_fm_limit"    ,"number of steps allowed for FM", 6000000, Int64Range(0, INT64_MAX), optionListPtr ),
opt_fmSearchLimit  (_cat_fm, "cp3_fm_Slimit"   ,"number of steps allowed for searching AMOs for FM", 12000000, Int64Range(0, INT64_MAX), optionListPtr ),
opt_fmMaxAMO       (_cat_fm, "cp3_fm_maxA"     ,"largest AMO that will be found during search", 200, IntRange(3, INT32_MAX), optionListPtr ),
opt_fmGrow         (_cat_fm, "cp3_fm_grow"     ,"max. grow of number of constraints per step", 40, IntRange(0, INT32_MAX), optionListPtr ),
opt_fmGrowT        (_cat_fm, "cp3_fm_growT"    ,"total grow of number of constraints", 100000, IntRange(0, INT32_MAX), optionListPtr ),
opt_atMostTwo      (_cat_fm, "cp3_fm_amt"      ,"extract at-most-two", true, optionListPtr ),
opt_fm_twoPr       (_cat_fm, "cp3_fm_twoPr"    ,"extract AMO using two product structures", true, optionListPtr ),
opt_fm_sem         (_cat_fm, "cp3_fm_sem"      ,"extract Card constraints using UP", true, optionListPtr ),
opt_findUnit       (_cat_fm, "cp3_fm_unit"     ,"check for units first", true, optionListPtr ),
opt_merge          (_cat_fm, "cp3_fm_merge"    ,"perform AMO merge", true, optionListPtr ),
opt_fm_avoid_duplicates(_cat_fm, "cp3_fm_dups" ,"avoid finding the same AMO multiple times", true, optionListPtr ),
opt_fm_multiVarAMO (_cat_fm, "cp3_fm_vMulAMO"  ,"try to find multiple AMOs per variable", true, optionListPtr ),
opt_multiVarAMT    (_cat_fm, "cp3_fm_vMulAMT"  ,"try to find multiple AMTs per variable", false, optionListPtr ),
opt_cutOff         (_cat_fm, "cp3_fm_cut"      ,"avoid eliminating too expensive variables (>10,10 or >5,15)", true, optionListPtr ),
opt_newAmo          (_cat_fm, "cp3_fm_newAmo"  ,"encode the newly produced AMOs (with pairwise encoding) 0=no,1=yes,2=try to avoid redundant clauses",  2, IntRange(0, 2), optionListPtr ),
opt_keepAllNew     (_cat_fm, "cp3_fm_keepM"    ,"keep all new AMOs (also rejected ones)", true, optionListPtr ),
opt_newAlo          (_cat_fm, "cp3_fm_newAlo"  ,"create clauses from deduced ALO constraints 0=no,1=from kept,2=keep all ",  2, IntRange(0, 2), optionListPtr ),
opt_newAlk          (_cat_fm, "cp3_fm_newAlk"  ,"create clauses from deduced ALK constraints 0=no,1=from kept,2=keep all (possibly redundant!)",  2, IntRange(0, 2), optionListPtr ),
opt_checkSub       (_cat_fm, "cp3_fm_newSub"   ,"check whether new ALO and ALK subsume other clauses (only if newALO or newALK)", true, optionListPtr ),
opt_rem_first      (_cat_fm, "cp3_fm_1st"      ,"extract first AMO candidate, or last AMO candidate", false, optionListPtr ),

opt_minCardClauseSize (_cat_fm, "card_minC"    ,"min clause size to find cards", 3, IntRange(2, INT32_MAX), optionListPtr),
opt_maxCardClauseSize (_cat_fm, "card_maxC"    ,"max clause size to find cards", 6, IntRange(2, INT32_MAX), optionListPtr),
opt_maxCardSize       (_cat_fm, "card_max"     ,"max card size that will be looked for", 12, IntRange(2, INT32_MAX), optionListPtr),
opt_semSearchLimit    (_cat_fm, "card_Elimit"  ,"number of steps allowed for searching AMOs semantically", 1200000, Int64Range(0, INT64_MAX), optionListPtr),
opt_semDebug          (_cat_fm, "card_debug"   ,"print info during running semantic card find", false, optionListPtr),
opt_noReduct          (_cat_fm, "card_noUnits" ,"assume there are no unit clauses inside the formula (otherwise, more expensive)", false, optionListPtr),

#if defined TOOLVERSION 
fm_debug_out (0),
#else
fm_debug_out (_cat_fm, "fm-debug",       "Debug Output of Fourier Motzkin", 0, IntRange(0, 4), optionListPtr ),
#endif

//
// Hidden Tautology Elimination
//
opt_hte_steps    (_cat_hte, "cp3_hte_steps",  "Number of steps that are allowed per iteration", INT32_MAX, IntRange(-1, INT32_MAX), optionListPtr ),
#if defined TOOLVERSION && TOOLVERSION < 302
opt_par_hte        (false),
#else
opt_par_hte         (_cat_hte, "cp3_par_hte",    "Forcing Parallel HTE", false, optionListPtr ),
#endif
#if defined TOOLVERSION  
hte_debug_out (0),
opt_hteTalk (false),
#else
hte_debug_out    (_cat_hte, "cp3_hte_debug",  "print debug output to screen", 0, IntRange(0, 4), optionListPtr ),
opt_hteTalk (_cat_hte, "cp3_hteTalk",    "talk about algorithm execution", false, optionListPtr ),
#endif
opt_hte_inpStepInc      (_cat_hte, "cp3_hte_inpInc","increase for steps per inprocess call", 60000, IntRange(0, INT32_MAX), optionListPtr ),

//
// Probing
//
pr_uip            (_cat_pr, "pr-uips",   "perform learning if a conflict occurs up to x-th UIP (-1 = all )", -1, IntRange(-1, INT32_MAX), optionListPtr ),
opt_pr_probeBinary(_cat_pr, "pr-bins",   "use binary clauses for probing",false, optionListPtr ),
pr_double         (_cat_pr, "pr-double", "perform double look-ahead",true, optionListPtr ),
pr_probe          (_cat_pr, "pr-probe",  "perform probing",true, optionListPtr ),
pr_rootsOnly      (_cat_pr, "pr-roots",  "probe only on root literals",true, optionListPtr ),
pr_repeat         (_cat_pr, "pr-repeat", "repeat probing if changes have been applied",false, optionListPtr ),
pr_clsSize        (_cat_pr, "pr-csize",  "size of clauses that are considered for probing/vivification (propagation)", INT32_MAX,  IntRange(0, INT32_MAX), optionListPtr ),
pr_LHBR           (_cat_pr, "pr-lhbr",   "perform lhbr during probing",false, optionListPtr ),
pr_prLimit        (_cat_pr, "pr-probeL", "step limit for probing", 5000000,  IntRange(0, INT32_MAX), optionListPtr ),
pr_EE             (_cat_pr, "pr-EE",     "run equivalent literal detection",true, optionListPtr ),
pr_vivi           (_cat_pr, "pr-vivi",   "perform clause vivification",true, optionListPtr ),
pr_keepLearnts    (_cat_pr, "pr-keepL",  "keep conflict clauses in solver (0=no,1=learnt,2=original)", 2, IntRange(0,2), optionListPtr ),
pr_keepImplied    (_cat_pr, "pr-keepI",  "keep clauses that imply on level 1 (0=no,1=learnt,2=original)", 2, IntRange(0,2), optionListPtr ),
pr_viviPercent    (_cat_pr, "pr-viviP",  "percent of max. clause size for clause vivification", 80, IntRange(0,100), optionListPtr ),
pr_viviLimit      (_cat_pr, "pr-viviL",  "step limit for clause vivification", 5000000,  IntRange(0, INT32_MAX), optionListPtr ),
pr_opt_inpStepInc1(_cat_pr, "cp3_pr_inpInc","increase for steps per inprocess call", 1000000, IntRange(0, INT32_MAX), optionListPtr ),
pr_opt_inpStepInc2(_cat_pr, "cp3_viv_inpInc","increase for steps per inprocess call", 1000000, IntRange(0, INT32_MAX), optionListPtr ),
pr_keepLHBRs      (_cat_pr, "pr-keepLHBR",  "keep clauses that have been created during LHBR during probing/vivification (0=no,1=learnt)", 0, IntRange(0,1), optionListPtr ),
pr_necBinaries      (_cat_pr, "pr-nce",    "generate L2 necessary assignments as binary clauses",true, optionListPtr ),
#if defined TOOLVERSION  
pr_debug_out (0),
#else
pr_debug_out        (_cat_pr, "pr-debug", "debug output for probing",0, IntRange(0,4) , optionListPtr ),
#endif

//
// Unit Propagation
//
#if defined TOOLVERSION  
up_debug_out (0),
#else
up_debug_out (_cat_up, "up-debug", "debug output for propagation",0, IntRange(0,4) , optionListPtr ),
#endif

//
// Resolution and Redundancy Addition
//
opt_res3_use_binaries  (_cat_res, "cp3_res_bin",      "resolve with binary clauses", false, optionListPtr ),
opt_res3_steps    (_cat_res, "cp3_res3_steps",   "Number of resolution-attempts that are allowed per iteration", 1000000, IntRange(0, INT32_MAX-1), optionListPtr ),
opt_res3_newCls   (_cat_res, "cp3_res3_ncls",    "Max. Number of newly created clauses", 100000, IntRange(0, INT32_MAX-1), optionListPtr ),
opt_res3_reAdd    (_cat_res, "cp3_res3_reAdd",   "Add variables of newly created resolvents back to working queues", false, optionListPtr ),
opt_res3_use_subs      (_cat_res, "cp3_res_eagerSub", "perform eager subsumption", true, optionListPtr ),
opt_add2_percent   (_cat_res, "cp3_res_percent",  "produce this percent many new clauses out of the total", 0.01, DoubleRange(0, true, 1, true), optionListPtr ),
opt_add2_red       (_cat_res, "cp3_res_add_red",  "add redundant binary clauses", false, optionListPtr ),
opt_add2_red_level     (_cat_res, "cp3_res_add_lev",  "calculate added percent based on level", true, optionListPtr ),
opt_add2_red_lea   (_cat_res, "cp3_res_add_lea",  "add redundants based on learneds as well?", false, optionListPtr ),
opt_add2_red_start (_cat_res, "cp3_res_ars",      "also before preprocessing?", false, optionListPtr ),
opt_res3_inpStepInc      (_cat_res, "cp3_res_inpInc","increase for steps per inprocess call", 200000, IntRange(0, INT32_MAX), optionListPtr ),
opt_add2_inpStepInc      (_cat_res, "cp3_add_inpInc","increase for steps per inprocess call", 60000, IntRange(0, INT32_MAX), optionListPtr ),
/// enable this parameter only during debug!
#if defined TOOLVERSION  
res3_debug_out (false),
#else
res3_debug_out         (_cat_res, "cp3_res_debug",   "print debug output to screen",false, optionListPtr ),
#endif


//
// Rewriter
//
opt_rew_min             (_cat_rew, "cp3_rew_min"  ,"min occurrence to be considered", 3, IntRange(0, INT32_MAX), optionListPtr ),
opt_rew_iter            (_cat_rew, "cp3_rew_iter" ,"number of iterations", 1, IntRange(0, INT32_MAX), optionListPtr ),
opt_rew_minAMO          (_cat_rew, "cp3_rew_minA" ,"min size of altered AMOs", 3, IntRange(0, INT32_MAX), optionListPtr ),
opt_rew_limit        (_cat_rew, "cp3_rew_limit","number of steps allowed for REW", 1200000, IntRange(0, INT32_MAX), optionListPtr ),
opt_rew_Varlimit        (_cat_rew, "cp3_rew_Vlimit","max number of variables to still perform REW", 1000000, IntRange(0, INT32_MAX), optionListPtr ),
opt_rew_Addlimit        (_cat_rew, "cp3_rew_Addlimit","number of new variables being allowed", 100000, IntRange(0, INT32_MAX), optionListPtr ),
opt_rew_amo        (_cat_rew, "cp3_rew_amo"   ,"rewrite amos", true, optionListPtr ),
opt_rew_imp        (_cat_rew, "cp3_rew_imp"   ,"rewrite implication chains", false, optionListPtr ),
opt_rew_scan_exo        (_cat_rew, "cp3_rew_exo"   ,"scan for encoded exactly once constraints first", true, optionListPtr ),
opt_rew_merge_amo       (_cat_rew, "cp3_rew_merge" ,"merge AMO constraints to create larger AMOs (fourier motzkin)", false, optionListPtr ),
opt_rew_rem_first       (_cat_rew, "cp3_rew_1st"   ,"how to find AMOs", false, optionListPtr ),
opt_rew_avg         (_cat_rew, "cp3_rew_avg"   ,"use AMOs above equal average only?", true, optionListPtr ),
opt_rew_ratio       (_cat_rew, "cp3_rew_ratio" ,"allow literals in AMO only, if their complement is not more frequent", true, optionListPtr ),
opt_rew_once        (_cat_rew, "cp3_rew_once"  ,"rewrite each variable at most once! (currently: yes only!)", true, optionListPtr ),
opt_rew_stat_only       (_cat_rew, "cp3_rew_stats" ,"analyze formula, but do not apply rewriting", false , optionListPtr ),
opt_rew_min_imp_size        (_cat_rew, "cp3_rewI_min"   ,"min size of an inplication chain to be rewritten", 4, IntRange(0, INT32_MAX), optionListPtr ),
opt_rew_impl_pref_small     (_cat_rew, "cp3_rewI_small" ,"prefer little imply variables", true, optionListPtr ),
opt_rew_inpStepInc      (_cat_rew, "cp3_rew_inpInc","increase for steps per inprocess call", 60000, IntRange(0, INT32_MAX), optionListPtr ),
#if defined TOOLVERSION 
rew_debug_out (0),
#else
rew_debug_out                 (_cat_rew, "rew-debug",       "Debug Output of Rewriter", 0, IntRange(0, 4), optionListPtr ),
#endif

//
// Shuffle
//
opt_shuffle_seed          (_cat_shuffle, "shuffle-seed",  "seed for shuffling",  0, IntRange(0, INT32_MAX), optionListPtr ),
opt_shuffle_order        (_cat_shuffle, "shuffle-order", "shuffle the order of the clauses", true, optionListPtr ),
#if defined TOOLVERSION  
shuffle_debug_out (0),
#else
shuffle_debug_out                 (_cat_shuffle, "shuffle-debug", "Debug Output of Shuffler", 0, IntRange(0, 4), optionListPtr ),
#endif

//
// Sls
//
#if defined TOOLVERSION 
opt_sls_debug (false),
#else
opt_sls_debug (_cat_sls, "sls-debug", "Print SLS debug output", false, optionListPtr ),
#endif
opt_sls_ksat_flips (_cat_sls, "sls-ksat-flips",   "how many flips should be performed, if k-sat is detected (-1 = infinite)", 20000000, IntRange(-1, INT32_MAX), optionListPtr ),
opt_sls_rand_walk  (_cat_sls, "sls-rnd-walk",     "probability of random walk (0-10000)", 2000, IntRange(0,10000), optionListPtr ),
opt_sls_adopt      (_cat_sls, "sls-adopt-cls",    "reduce nr of flips for large instances", false, optionListPtr ),

//
// Subsumption
//
opt_sub_naivStrength    (_cat_sub, "naive_strength",   "use naive strengthening", false, optionListPtr ),
opt_sub_allStrengthRes  (_cat_sub, "all_strength_res", "Create all self-subsuming resolvents of clauses less equal given size (prob. slow & blowup, only seq)", 0, IntRange(0,INT32_MAX), optionListPtr ), 
opt_sub_strength        (_cat_sub, "cp3_strength",     "Perform clause strengthening", true, optionListPtr ), 
opt_sub_preferLearned   (_cat_sub, "cp3_inpPrefL",    "During inprocessing, check learned clauses first!", true, optionListPtr ), 
opt_sub_subLimit        (_cat_sub, "cp3_sub_limit", "limit of subsumption steps",   300000000, IntRange(0,INT32_MAX), optionListPtr ), 
opt_sub_strLimit        (_cat_sub, "cp3_str_limit", "limit of strengthening steps", 300000000, IntRange(0,INT32_MAX), optionListPtr ), 
opt_sub_callIncrease    (_cat_sub, "cp3_call_inc",  "max. limit increase per process call (subsimp is frequently called from other techniques)", 200, IntRange(0,INT32_MAX), optionListPtr ), 
opt_sub_inpStepInc      (_cat_sub, "cp3_sub_inpInc","increase for steps per inprocess call", 40000000, IntRange(0, INT32_MAX), optionListPtr ),
#if defined TOOLVERSION && TOOLVERSION < 302
opt_sub_par_strength    (1),
opt_sub_lock_stats      (false),
opt_sub_par_subs        (1),
opt_sub_par_subs_counts (false),
opt_sub_chunk_size      (100000),
opt_sub_par_str_minCls  (250000),
#else
opt_sub_par_strength    (_cat_sub, "cp3_par_strength", "par strengthening: 0 never, 1 heuristic, 2 always", 1, IntRange(0,2), optionListPtr ),
opt_sub_lock_stats      (_cat_sub, "cp3_lock_stats", "measure time waiting in spin locks", false, optionListPtr ),
opt_sub_par_subs        (_cat_sub, "cp3_par_subs", "par subsumption: 0 never, 1 heuristic, 2 always", 1, IntRange(0,2), optionListPtr ),
opt_sub_par_subs_counts (_cat_sub, "par_subs_counts" ,  "Updates of counts in par-subs 0: compare_xchange, 1: CRef-vector", 1, IntRange(0,1), optionListPtr ),
opt_sub_chunk_size      (_cat_sub, "susi_chunk_size" ,  "Size of Par SuSi Chunks", 100000, IntRange(1,INT32_MAX), optionListPtr ),
opt_sub_par_str_minCls  (_cat_sub, "par_str_minCls"  ,  "number of clauses to start parallel strengthening", 250000, IntRange(1,INT32_MAX), optionListPtr ),
#endif
#if defined TOOLVERSION
opt_sub_debug (0),
#else
opt_sub_debug   (_cat_sub, "susi_debug" , "Debug Output for Subsumption", 0, IntRange(0,3), optionListPtr ),
#endif

//
// Symmetry Breaker
//
sym_opt_hsize             (_cat_sym, "sym-size",    "scale with the size of the clause", false, optionListPtr ),
sym_opt_hpol              (_cat_sym, "sym-pol",     "consider the polarity of the occurrences", false, optionListPtr ),
sym_opt_hpushUnit         (_cat_sym, "sym-unit",    "ignore unit clauses", false, optionListPtr ), // there should be a parameter delay-units already!
sym_opt_hmin              (_cat_sym, "sym-min",     "minimum symmtry to be exploited", 2, IntRange(1, INT32_MAX) , optionListPtr ),
sym_opt_hratio            (_cat_sym, "sym-ratio",   "only consider a variable if it appears close to the average of variable occurrences", 0.4, DoubleRange(0, true, HUGE_VAL, true), optionListPtr ),
sym_opt_iter              (_cat_sym, "sym-iter",    "number of symmetry approximation iterations", 3, IntRange(0, INT32_MAX) , optionListPtr ),
sym_opt_pairs             (_cat_sym, "sym-show",    "show symmetry pairs", false, optionListPtr ),
sym_opt_print             (_cat_sym, "sym-print",   "show the data for each variable", false, optionListPtr ),
sym_opt_exit              (_cat_sym, "sym-exit",    "exit after analysis", false, optionListPtr ),
sym_opt_hprop             (_cat_sym, "sym-prop",    "try to generate symmetry breaking clauses with propagation", false, optionListPtr ),
sym_opt_hpropF            (_cat_sym, "sym-propF",    "generate full clauses", false, optionListPtr ),
sym_opt_hpropA            (_cat_sym, "sym-propA",    "test all four casese instead of two", false, optionListPtr ),
sym_opt_cleanLearn        (_cat_sym, "sym-clLearn",  "clean the learned clauses that have been created during symmetry search", false, optionListPtr ),
sym_opt_conflicts         (_cat_sym, "sym-cons",     "number of conflicts for looking for being implied", 0, IntRange(0, INT32_MAX) , optionListPtr ),
sym_opt_total_conflicts   (_cat_sym, "sym-consT",    "number of total conflicts for looking for being implied", 10000, IntRange(0, INT32_MAX) , optionListPtr ),
#if defined TOOLVERSION  
sym_debug_out (0),
#else
sym_debug_out        (_cat_sym, "sym-debug", "debug output for probing",0, IntRange(0,4) , optionListPtr ),
#endif

//
// Twosat
//
#if defined TOOLVERSION 
twosat_debug_out (0),
twosat_useUnits (false),
twosat_clearQueue( true),
#else
twosat_debug_out                 (_cat_twosat, "2sat-debug",  "Debug Output of 2sat", 0, IntRange(0, 4), optionListPtr ),
twosat_useUnits                 (_cat_twosat, "2sat-units",  "If 2SAT finds units, use them!", false, optionListPtr ),
twosat_clearQueue               (_cat_twosat, "2sat-cq",     "do a decision after a unit has been found", true, optionListPtr ),
#endif

 
//
// Unhide
//
opt_uhd_Iters     (_cat_uhd, "cp3_uhdIters",     "Number of iterations for unhiding", 3, IntRange(0, INT32_MAX), optionListPtr ),
opt_uhd_Trans     (_cat_uhd, "cp3_uhdTrans",     "Use Transitive Graph Reduction (buggy)", false, optionListPtr ),
opt_uhd_UHLE      (_cat_uhd, "cp3_uhdUHLE",      "Use Unhiding+Hidden Literal Elimination",  3, IntRange(0, 3), optionListPtr ),
opt_uhd_UHTE      (_cat_uhd, "cp3_uhdUHTE",      "Use Unhiding+Hidden Tautology Elimination", true, optionListPtr ),
opt_uhd_NoShuffle (_cat_uhd, "cp3_uhdNoShuffle", "Do not perform randomized graph traversation", false, optionListPtr ),
opt_uhd_EE        (_cat_uhd, "cp3_uhdEE",        "Use equivalent literal elimination (buggy)", false, optionListPtr ),
opt_uhd_TestDbl   (_cat_uhd, "cp3_uhdTstDbl",    "Test for duplicate binary clauses", false, optionListPtr ),
opt_uhd_probe     (_cat_uhd, "cp3_uhdProbe",     "Approximate probing (bin cls) with stamp info (off,constant,linear,quadratic,exponential)", 0, IntRange(0, 4), optionListPtr ),
opt_uhd_fullProbe (_cat_uhd, "cp3_uhdPrSize",    "Enable unhide probing for larger clauses, size <= given parameter", 2, IntRange(2, INT32_MAX), optionListPtr ),
opt_uhd_probeEE   (_cat_uhd, "cp3_uhdPrEE",      "Find Equivalences during uhd probing (requ. uhdProbe > 1)", false, optionListPtr  ),
opt_uhd_fullBorder(_cat_uhd, "cp3_uhdPrSiBo",    "Check larger clauses only in first and last iteration", true, optionListPtr  ),
#if defined TOOLVERSION  
opt_uhd_Debug(0),
#else
opt_uhd_Debug     (_cat_uhd, "cp3_uhdDebug",     "Debug Level of Unhiding", 0, IntRange(0, 6), optionListPtr ),
#endif


//
// Xor
//
opt_xorMatchLimit (_cat_xor, "xorMaxSize",  "Maximum Clause Size for detecting XOrs (high number consume much memory!)", 12, IntRange(3, 63), optionListPtr ),
opt_xorFindLimit  (_cat_xor, "xorLimit",    "number of checks for finding xors", 1200000, IntRange(0, INT32_MAX), optionListPtr ),
opt_xor_selectX       (_cat_xor, "xorSelect",    "how to select next xor 0=first,1=smallest", 0, IntRange(0, 1), optionListPtr ),
opt_xor_keepUsed      (_cat_xor, "xorKeepUsed",  "continue to simplify kept xors", true, optionListPtr ),
opt_xor_findSubsumed  (_cat_xor, "xorFindSubs",  "try to recover XORs that are partially subsumed", true, optionListPtr ),
opt_xor_findResolved  (_cat_xor, "xorFindRes",   "try to recover XORs including resolution steps", false, optionListPtr ),
#if defined TOOLVERSION 
opt_xor_debug(0),
#else
opt_xor_debug             (_cat_xor, "xor-debug",       "Debug Output of XOR reasoning", 0, IntRange(0, 5), optionListPtr ),
#endif
 dummy (0)
{
  if( defaultPreset.size() != 0 ) setPreset( defaultPreset ); // set configuration options immediately
}
