/***********************************************************************************[CoreConfig.cc]

Copyright (c) 2012-2013, Norbert Manthey

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "core/CoreConfig.h"

#include "mtl/Sort.h"

using namespace Minisat;

static const char* _cat = "CORE";
static const char* _cr = "CORE -- RESTART";
static const char* _cred = "CORE -- REDUCE";
static const char* _cm = "CORE -- MINIMIZE";

CoreConfig::CoreConfig(const std::string & presetOptions) // add new options here!
:
 Config( &configOptions, presetOptions ),
 
 //
 // all the options for the object
 //
 opt_solve_stats (_cat, "solve_stats", "print stats about solving process", false, optionListPtr ),
 opt_fast_rem (_cat, "rmf", "use fast remove", false, optionListPtr ),
 
 
 ppOnly (_cat, "ppOnly", "interrupts search after preprocessing", false, optionListPtr ),
#if defined TOOLVERSION
 opt_learn_debug(false) ,
#else
 opt_learn_debug (_cat, "learn-debug", "print debug information during learning", false, optionListPtr ),
#endif
 

 opt_K (_cr, "K", "The constant used to force restart", 0.8, DoubleRange(0, false, 1, false), optionListPtr ), 
 opt_R (_cr, "R", "The constant used to block restart", 1.4, DoubleRange(1, false, 5, false), optionListPtr ), 
 opt_size_lbd_queue (_cr, "szLBDQueue", "The size of moving average for LBD (restarts)", 50, IntRange(10, INT32_MAX), optionListPtr ),
 opt_size_trail_queue (_cr, "szTrailQueue", "The size of moving average for trail (block restarts)", 5000, IntRange(10, INT32_MAX), optionListPtr ),

 opt_first_reduce_db (_cred, "firstReduceDB", "The number of conflicts before the first reduce DB", 4000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_inc_reduce_db (_cred, "incReduceDB", "Increment for reduce DB", 300, IntRange(0, INT32_MAX), optionListPtr ),
 opt_spec_inc_reduce_db (_cred, "specialIncReduceDB", "Special increment for reduce DB", 1000, IntRange(0, INT32_MAX), optionListPtr ),
 opt_lb_lbd_frozen_clause (_cred, "minLBDFrozenClause", "Protect clauses if their LBD decrease and is lower than (for one turn)", 30, IntRange(0, INT32_MAX), optionListPtr ),
 opt_lbd_ignore_l0 (_cred, "lbdIgnL0", "ignore top level literals for LBD calculation", false, optionListPtr ),
 opt_update_lbd (_cred, "lbdupd", "update LBD during (0=propagation,1=learning,2=never),",1, IntRange(0, 2), optionListPtr ),
 opt_lbd_inc(_cred,"incLBD","allow to increment lbd of clauses dynamically",false, optionListPtr ),
 opt_quick_reduce(_cred,"quickRed","check only first two literals for being satisfied",false, optionListPtr ),
 opt_keep_worst_ratio(_cred,"keepWorst","keep this (relative to all learned) number of worst learned clauses during removal", 0, DoubleRange(0, true, 1, true), optionListPtr ), 
 
 opt_biAsserting (_cm, "biAsserting", "Learn bi-asserting clauses, if possible (do not learn asserting clause!)", false, optionListPtr),
 opt_biAssiMaxEvery (_cm, "biAsFreq", "The min nr. of clauses between two learned bi-asserting clauses", 0, IntRange(0, INT32_MAX), optionListPtr ),
 opt_lb_size_minimzing_clause (_cm, "minSizeMinimizingClause", "The min size required to minimize clause", 30, IntRange(3, INT32_MAX), optionListPtr ),
 opt_lb_lbd_minimzing_clause (_cm, "minLBDMinimizingClause", "The min LBD required to minimize clause", 6, IntRange(3, INT32_MAX), optionListPtr ),

 opt_var_decay_start(_cat, "var-decay-b", "The variable activity decay factor start value", 0.95, DoubleRange(0, false, 1, false), optionListPtr ),
 opt_var_decay_stop(_cat, "var-decay-e", "The variable activity decay factor stop value", 0.95, DoubleRange(0, false, 1, false), optionListPtr ),
 opt_var_decay_inc(_cat, "var-decay-i",  "The variable activity decay factor increase ", 0.01, DoubleRange(0, false, 1, false), optionListPtr ),
 opt_var_decay_dist(_cat, "var-decay-d", "Nr. of conflicts for activity decay increase", 5000, IntRange(1, INT32_MAX), optionListPtr ),
 
 opt_agility_restart_reject("MODS", "agil-r", "reject restarts based on agility", false, optionListPtr ),
 opt_agility_rejectLimit("MODS", "agil-limit", "agility above this limit rejects restarts", 0.22, DoubleRange(0, true, 1, true), optionListPtr ),
 opt_agility_decay("MODS", "agil-decay", "search agility decay", 0.9999, DoubleRange(0, true, 1, true), optionListPtr ),
 opt_agility_init("MODS", "agil-init",   "initial agility", 0.11, DoubleRange(0, true, 1, true), optionListPtr ),
 opt_agility_limit_increase("MODS", "agil-add",   "number of conflicts until the next restart is allowed (for static schedules)", 128, IntRange(1, INT32_MAX), optionListPtr ),
 
 opt_clause_decay (_cat, "cla-decay", "The clause activity decay factor", 0.999, DoubleRange(0, false, 1, false), optionListPtr ),
 opt_random_var_freq (_cat, "rnd-freq", "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true), optionListPtr ),
 opt_random_seed (_cat, "rnd-seed", "Used by the random variable selection", 91648253, DoubleRange(0, false, HUGE_VAL, false), optionListPtr ),
 opt_ccmin_mode (_cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2), optionListPtr ),
 opt_phase_saving (_cat, "phase-saving","Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2), optionListPtr ),
 opt_rnd_init_act (_cat, "rnd-init", "Randomize the initial activity", false, optionListPtr ),
 opt_init_act ("INIT", "init-act", "initialize activities (0=none,1=inc-lin,2=inc-geo,3=dec-lin,4=dec-geo,5=rnd,6=abs(jw))", 0, IntRange(0, 6), optionListPtr ),
 opt_init_pol ("INIT", "init-pol", "initialize polarity (0=none,1=JW-pol,2=JW-neg,3=MOMS,4=MOMS-neg,5=rnd)", 0, IntRange(0, 5), optionListPtr ),

 opt_restart_level (_cat, "rlevel", "Choose to which level to jump to: 0=0, 1=ReusedTrail, 2=recursive reused trail", 0, IntRange(0, 2), optionListPtr ),
 opt_restarts_type (_cat, "rtype", "Choose type of restart (0=dynamic,1=luby,2=geometric)", 0, IntRange(0, 2), optionListPtr ),
 opt_restart_first (_cat, "rfirst", "The base restart interval", 100, IntRange(1, INT32_MAX), optionListPtr ),
 opt_restart_inc (_cat, "rinc", "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false), optionListPtr ),

 opt_garbage_frac (_cat, "gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered", 0.20, DoubleRange(0, false, HUGE_VAL, false), optionListPtr ),

 opt_allUipHack ("MODS", "alluiphack", "learn all unit UIPs at any level", 0, IntRange(0, 2) , optionListPtr ),
 opt_vsids_start ("MODS", "vsids-s", "interpolate between VSIDS and VMTF,start value", 1, DoubleRange(0, true, 1, true), optionListPtr ),
 opt_vsids_end("MODS", "vsids-e", "interpolate between VSIDS and VMTF, end value", 1, DoubleRange(0, true, 1, true), optionListPtr ),
 opt_vsids_inc("MODS", "vsids-i", "interpolate between VSIDS and VMTF, inc during update", 1, DoubleRange(0, true, 1, true), optionListPtr ),
 opt_vsids_distance("MODS", "vsids-d", "interpolate between VSIDS and VMTF, numer of conflits until next update", INT32_MAX, IntRange(1, INT32_MAX), optionListPtr ),
 opt_var_act_bump_mode("MODS", "varActB", "bump activity of a variable (0 as usual, 1 relativ to cls size, 2 relative to LBD)", 0, IntRange(0, 2), optionListPtr ),
 opt_cls_act_bump_mode("MODS", "clsActB", "bump activity of a clause (0 as usual, 1 relativ to cls size, 2 relative to LBD)", 0, IntRange(0, 2), optionListPtr ),
 
 opt_dontTrustPolarity("MODS", "dontTrust", "change decision literal polarity once in a while", false, optionListPtr ),
 
 opt_LHBR ("SEARCH - LHBR", "lhbr", "use lhbr (0=no,1=str,2=trans,str,3=new,4=trans,new)", 0, IntRange(0, 4), optionListPtr ),
 opt_LHBR_max ("SEARCH - LHBR", "lhbr-max", "max nr of newly created lhbr clauses", INT32_MAX, IntRange(0, INT32_MAX), optionListPtr ),
 opt_LHBR_sub ("SEARCH - LHBR", "lhbr-sub", "check whether new clause subsumes the old clause", false, optionListPtr ),
 opt_printLhbr ("SEARCH - LHBR", "lhbr-print", "print info about lhbr", false, optionListPtr ),

 opt_updateLearnAct ("MODS", "updLearnAct", "UPDATEVARACTIVITY trick (see glucose competition'09 companion paper)", true , optionListPtr ),

 opt_hack ("SEARCH - REASON", "hack", "use hack modifications", 0, IntRange(0, 3) , optionListPtr ),
 opt_hack_cost ("SEARCH - REASON", "hack-cost", "use size cost", true , optionListPtr ),
#if defined TOOLVERSION
 opt_dbg(false) ,
#else
 opt_dbg ("REASON", "dbg", "debug hack", false , optionListPtr ),
#endif

 

 opt_long_conflict ("REASON", "longConflict", "if a binary conflict is found, check for a longer one!", false, optionListPtr ),

// extra 
 opt_act ("INIT", "actIncMode", "how to inc 0=lin, 1=geo,2=reverse-lin,3=reverse-geo", 0, IntRange(0, 3) , optionListPtr ),
 opt_actStart ("INIT", "actStart", "highest value for first variable", 1024, DoubleRange(0, false, HUGE_VAL, false), optionListPtr ),
 pot_actDec ("INIT", "actDec", "decrease per element (sub, or divide)",1/0.95, DoubleRange(0, false, HUGE_VAL, true), optionListPtr ),
 actFile ("INIT", "actFile", "increase activities of those variables",0, optionListPtr ),
 opt_pol ("INIT", "polMode", "invert provided polarities", false , optionListPtr ),
 polFile ("INIT", "polFile", "use these polarities", 0, optionListPtr ),
 opt_printDecisions ("INIT", "printDec", "1=print decisions, 2=print all enqueues, 3=show clauses", 0, IntRange(0, 3)  , optionListPtr ),

 opt_rMax ("MODS", "rMax", "initial max. interval between two restarts (-1 = off)", -1, IntRange(-1, INT32_MAX) , optionListPtr ),
 opt_rMaxInc ("MODS", "rMaxInc", "increase of the max. restart interval per restart", 1.1, DoubleRange(1, true, HUGE_VAL, false), optionListPtr ),

 localLookaheadDebug ("SEARCH - LOCAL LOOK AHEAD", "laHackOutput","output info about LA", false, optionListPtr ),
 localLookAhead ("SEARCH - LOCAL LOOK AHEAD", "laHack", "enable lookahead on level 0", false, optionListPtr ),
 tb ("SEARCH - LOCAL LOOK AHEAD", "tabu", "do not perform LA, if all considered LA variables are as before", true, optionListPtr ),
 opt_laDyn ("SEARCH - LOCAL LOOK AHEAD", "dyn", "dynamically set the frequency based on success", false, optionListPtr ),
 opt_laEEl ("SEARCH - LOCAL LOOK AHEAD", "laEEl", "add EE clauses as learnt clauses", false, optionListPtr ),
 opt_laEEp ("SEARCH - LOCAL LOOK AHEAD", "laEEp", "add EE clauses, if less than p percent tests failed", 0, IntRange(0, 100), optionListPtr ),
 opt_laMaxEvery ("SEARCH - LOCAL LOOK AHEAD", "hlaMax", "maximum bound for frequency", 50, IntRange(0, INT32_MAX) , optionListPtr ),
#ifdef DONT_USE_128_BIT
 opt_laLevel ("SEARCH - LOCAL LOOK AHEAD", "hlaLevel", "level of look ahead", 5, IntRange(1, 5) , optionListPtr ),
#else
 opt_laLevel ("SEARCH - LOCAL LOOK AHEAD", "hlaLevel", "level of look ahead", 5, IntRange(1, 5) , optionListPtr ), 
#endif
 opt_laEvery ("SEARCH - LOCAL LOOK AHEAD", "hlaevery", "initial frequency of LA", 1, IntRange(0, INT32_MAX) , optionListPtr ),
 opt_laBound ("SEARCH - LOCAL LOOK AHEAD", "hlabound", "max. nr of LAs (-1 == inf)", 4096, IntRange(-1, INT32_MAX) , optionListPtr ),
 opt_laTopUnit ("SEARCH - LOCAL LOOK AHEAD", "hlaTop", "allow another LA after learning another nr of top level units (-1 = never)", -1, IntRange(-1, INT32_MAX), optionListPtr ),

 opt_hpushUnit ("MODS", "delay-units", "does not propagate unit clauses until solving is initialized", false, optionListPtr ),
 opt_simplifyInterval ("MODS", "sInterval", "how often to perform simplifications on level 0", 0, IntRange(0, INT32_MAX) , optionListPtr ),

 opt_otfss ("SEARCH - OTFSS", "otfss", "perform otfss during conflict analysis", false, optionListPtr ),
 opt_otfssL ("SEARCH - OTFSS", "otfssL", "otfss for learnt clauses", false, optionListPtr ),
 opt_otfssMaxLBD ("SEARCH - OTFSS", "otfssMLDB", "max. LBD of learnt clauses that are candidates for otfss", 30, IntRange(2, INT32_MAX) , optionListPtr ),
#if defined TOOLVERSION
 debug_otfss ( false , optionListPtr ),
#else
 debug_otfss ("SEARCH - OTFSS", "otfss-d", "print debug output", false, optionListPtr ),
#endif

 opt_learnDecPrecent ("SEARCH - DECISION CLAUSES", "learnDecP",   "if LBD of is > percent of decisionlevel, learn decision Clause (Knuth), -1 = off", -1, IntRange(-1, 100) , optionListPtr ),
 opt_learnDecMinSize ("SEARCH - DECISION CLAUSES", "learnDecMS",  "min size so that decision clauses are learned, -1 = off", 2, IntRange(2, INT32_MAX) , optionListPtr ),
 opt_learnDecRER     ("SEARCH - DECISION CLAUSES", "learnDecRER", "consider decision clauses for RER?",false , optionListPtr ),


 opt_extendedClauseLearning("EXTENDED RESOLUTION ECL", "ecl", "perform extended clause learning (along Huang 2010)", false, optionListPtr ), 
 opt_ecl_as_learned("EXTENDED RESOLUTION ECL", "ecl-l", "add ecl clauses as learned clauses", true, optionListPtr ),
 opt_ecl_as_replaceAll("EXTENDED RESOLUTION ECL", "ecl-r", "run through formula and replace all disjunctions in the ECL (only if not added as learned) 0=no,1=formula,2=formula+learned", 0, IntRange(0, 2), optionListPtr ),
 opt_ecl_rewriteNew("EXTENDED RESOLUTION ECL", "ecl-rn", "rewrite upcoming learned clauses as well (only, if not added as learned)", false, optionListPtr ),
 opt_ecl_full("EXTENDED RESOLUTION ECL", "ecl-f", "add full ecl extension?", true, optionListPtr ), 
 opt_ecl_minSize ("EXTENDED RESOLUTION ECL", "ecl-min-size", "minimum size of learned clause to perform ecl", 3, IntRange(3, INT32_MAX) , optionListPtr ),
 opt_ecl_maxLBD("EXTENDED RESOLUTION ECL", "ecl-maxLBD", "maximum LBD to perform ecl", 4, IntRange(2, INT32_MAX) , optionListPtr ), 
 opt_ecl_newAct("EXTENDED RESOLUTION ECL", "ecl-new-act", "how to set the new activity: 0=avg, 1=max, 2=min, 3=sum, 4=geo-mean", 0, IntRange(0, 4) , optionListPtr ),
#if defined TOOLVERSION
 opt_ecl_debug(false),
#else
 opt_ecl_debug("EXTENDED RESOLUTION ECL", "ecl-d", "debug output for ECL", false, optionListPtr ),
#endif
 opt_ecl_smallLevel("EXTENDED RESOLUTION ECL", "ecl-smL", "ecl only, if smallest lit level is below the given (negative=neg.ratio from bj. level,positive=absolute)", -1, DoubleRange(-1, true, HUGE_VAL, true) , optionListPtr ),
 opt_ecl_every("EXTENDED RESOLUTION ECL", "ecl-freq", "how often ecl compared to usual learning", 1, DoubleRange(0, true, 1, true) , optionListPtr ),
 
 opt_restrictedExtendedResolution("EXTENDED RESOLUTION RER", "rer", "perform restricted extended resolution (along Audemard ea 2010)", false, optionListPtr ), 
 opt_rer_as_learned("EXTENDED RESOLUTION RER", "rer-l", "store extensions as learned clauses", true, optionListPtr ), 
 opt_rer_as_replaceAll("EXTENDED RESOLUTION RER", "rer-r", "replace all disjunctions of the RER extension (only, if not added as learned, and if full - RER adds a conjunction, optionListPtr ), 0=no,1=formula,2=formula+learned", 0, IntRange(0, 2), optionListPtr ), 
 opt_rer_rewriteNew("EXTENDED RESOLUTION RER", "rer-rn", "rewrite new learned clauses, only if full and not added as learned", false, optionListPtr ), 
 opt_rer_full("EXTENDED RESOLUTION RER", "rer-f", "add full rer extension?", true, optionListPtr ), 
 opt_rer_minSize ("EXTENDED RESOLUTION RER", "rer-min-size", "minimum size of learned clause to perform rer", 2, IntRange(2, INT32_MAX) , optionListPtr ),
 opt_rer_maxSize("EXTENDED RESOLUTION RER", "rer-max-size", "maximum size of learned clause to perform rer", INT32_MAX, IntRange(2, INT32_MAX) , optionListPtr ),
 opt_rer_minLBD("EXTENDED RESOLUTION RER", "rer-minLBD", "minimum LBD to perform rer", 1, IntRange(1, INT32_MAX) , optionListPtr ), 
 opt_rer_maxLBD("EXTENDED RESOLUTION RER", "rer-maxLBD", "maximum LBD to perform rer", INT32_MAX, IntRange(1, INT32_MAX) , optionListPtr ), 
 opt_rer_windowSize("EXTENDED RESOLUTION RER", "rer-window", "number of clauses to collect before fuse", 2, IntRange(2, INT32_MAX) , optionListPtr ), 
 opt_rer_newAct("EXTENDED RESOLUTION RER", "rer-new-act", "how to set the new activity: 0=avg, 1=max, 2=min, 3=sum, 4=geo-mean", 0, IntRange(0, 4) , optionListPtr ),
 opt_rer_ite("EXTENDED RESOLUTION RER", "rer-ite", "check for ITE pattern, if AND is not found?", false , optionListPtr ),
#if defined TOOLVERSION
 opt_ecl_debug(false),
#else
 opt_rer_debug("EXTENDED RESOLUTION RER", "rer-d", "debug output for RER", false, optionListPtr ),
#endif
 opt_rer_every("EXTENDED RESOLUTION RER", "rer-freq", "how often rer compared to usual learning", 1, DoubleRange(0, true, 1, true) , optionListPtr ),
 
 erRewrite_size("EXTENDED RESOLUTION", "er-size", "rewrite new learned clauses with ER, if size is small enough", 30, IntRange(0, INT32_MAX), optionListPtr ),
 erRewrite_lbd( "EXTENDED RESOLUTION", "er-lbd" , "rewrite new learned clauses with ER, if lbd is small enough",  6,  IntRange(0, INT32_MAX), optionListPtr ),
 
 opt_interleavedClauseStrengthening("INTERLEAVED CLAUSE STRENGTHENING", "ics", "perform interleaved clause strengthening (along Wieringa ea 2013)", false, optionListPtr ), 
 opt_ics_interval("INTERLEAVED CLAUSE STRENGTHENING", "ics_window" ,"run ICS after another N conflicts", 5000, IntRange(0, INT32_MAX) , optionListPtr ),
 opt_ics_processLast("INTERLEAVED CLAUSE STRENGTHENING", "ics_processLast" ,"process this number of learned clauses (analyse, reject if quality too bad!)", 5050, IntRange(0, INT32_MAX) , optionListPtr ),
 opt_ics_keepLearnts("INTERLEAVED CLAUSE STRENGTHENING", "ics_keepNew" ,"keep the learned clauses that have been produced during the ICS", false , optionListPtr ),
 opt_ics_dynUpdate("INTERLEAVED CLAUSE STRENGTHENING", "ics_dyn" ,"update variable/clause activities during ICS", false , optionListPtr ),
 opt_ics_shrinkNew("INTERLEAVED CLAUSE STRENGTHENING", "ics_shrinkNew" ,"shrink the kept learned clauses in the very same run?! (makes only sense if the other clauses are kept!)", false , optionListPtr ),
 opt_ics_LBDpercent("INTERLEAVED CLAUSE STRENGTHENING", "ics_relLBD" ,"only look at a clause if its LBD is less than this percent of the average of the clauses that are looked at, 1=100%",1, DoubleRange(0, true, HUGE_VAL, true) , optionListPtr ), 
 opt_ics_SIZEpercent("INTERLEAVED CLAUSE STRENGTHENING", "ics_relSIZE" ,"only look at a clause if its size is less than this percent of the average size of the clauses that are looked at, 1=100%",1, DoubleRange(0, true, HUGE_VAL, true) , optionListPtr ),
#if defined TOOLVERSION
 opt_ics_debug(false),
#else
 opt_ics_debug("INTERLEAVED CLAUSE STRENGTHENING", "ics-debug","debug output for ICS",false, optionListPtr ),
#endif
 
 // USING BIG information during search
 opt_uhdProbe     (       "SEARCH UNHIDE PROBING", "sUhdProbe", "perform probing based on learned clauses (off,linear,quadratic,larger)", 0, IntRange(0,3), optionListPtr ),
 opt_uhdCleanRebuild     ("SEARCH UNHIDE PROBING", "sUhdPrRb",  "rebuild BIG before cleaning the formula" ,true, optionListPtr ),
 opt_uhdRestartReshuffle ("SEARCH UNHIDE PROBING", "sUhdPrSh",  "travers the BIG again during every i-th restart 0=off" ,0, IntRange(0,INT32_MAX), optionListPtr ),
 uhle_minimizing_size    ("SEARCH UNHIDE PROBING", "sUHLEsize", "maximal clause size for UHLE for learnt clauses (0=off)" ,0, IntRange(0,INT32_MAX), optionListPtr ),
 uhle_minimizing_lbd     ("SEARCH UNHIDE PROBING", "sUHLElbd",  "maximal LBD for UHLE for learnt clauses (0=off)", 6, IntRange(0,INT32_MAX), optionListPtr ),
 
 // CEGAR
 opt_maxSDcalls("SUBSTITUTE DISJUNCTIONS", "sdCalls", "number of calls of assumptions, before solving original formula" ,0, IntRange(0,INT32_MAX), optionListPtr ),
 opt_sdLimit("SUBSTITUTE DISJUNCTIONS",    "sdSteps", "number of steps for subsitute disjunctions" ,250000, IntRange(0,INT32_MAX), optionListPtr ),
 
 opt_maxCBcalls("CEGAR BVA", "cbCalls", "number of calls to cegar bva iterations" ,        0, IntRange(0,INT32_MAX), optionListPtr ),
 opt_cbLimit("CEGAR BVA",    "cbSteps", "number of steps for subsitute disjunctions" ,2500000, IntRange(0,INT32_MAX), optionListPtr ),
 opt_cbLeast("CEGAR BVA",    "cbLeast", "use least frequent lit for matching (otherwise, most freq.) " ,true ),
 opt_cbStrict("CEGAR BVA",  "cbStrict", "only use cegar BVA for patterns that always lead to reduction" ,true ),
 
 
 // DRUP
 opt_verboseProof     ("PROOF", "verb-proof", "also print comments into the proof, 2=print proof also to stderr", 1, IntRange(0, 2) , optionListPtr ),
 opt_rupProofOnly     ("PROOF", "rup-only", "do not print delete lines into proof", false, optionListPtr ), 
 opt_checkProofOnline ("PROOF", "proof-oft-check", "check proof construction during execution (1=on, higher => more verbose checking)", 0, IntRange(0,10), optionListPtr ), 

 opt_verb ("CORE", "solververb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2), optionListPtr ),
 
 opt_usePPpp ("CORE", "usePP", "use preprocessor for preprocessing", true, optionListPtr ),
 opt_usePPip ("CORE", "useIP", "use preprocessor for inprocessing", true, optionListPtr ),
//
// for incremental solving
//
 resetActEvery        ("INCREMENTAL", "incResAct", "when incrementally called, reset activity every X calls (0=off)", 0, IntRange(0, INT32_MAX) , optionListPtr ),
 resetPolEvery        ("INCREMENTAL", "incResPol", "when incrementally called, reset polarities every X calls (0=off)", 0, IntRange(0, INT32_MAX) , optionListPtr ),
 intenseCleaningEvery ("INCREMENTAL", "incClean",  "when incrementally called, extra clean learnt data base every X calls (0=off)", 0, IntRange(0, INT32_MAX) , optionListPtr ),
 incKeepSize          ("INCREMENTAL", "incClSize", "keep size for extra cleaning (any higher is dropped)", 5, IntRange(1, INT32_MAX) , optionListPtr ),
 incKeepLBD           ("INCREMENTAL", "incClLBD",  "keep lbd for extra cleaning (any higher is dropped)", 10, IntRange(1, INT32_MAX) , optionListPtr ),
 opt_reset_counters   ("INCREMENTAL", "incResCnt", "reset solving counters every X start (0=off)", 100000, IntRange(0, INT32_MAX) , optionListPtr )
{
  if( defaultPreset.size() != 0 ) setPreset( defaultPreset ); // set configuration options immediately
}

