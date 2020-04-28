/**************************************************************************************[CPConfig.h]

Copyright (c) 2013, Norbert Manthey, All rights reserved.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef CPConfig_h
#define CPConfig_h

#include "utils/Config.h"
#include "utils/Options.h"

using namespace Minisat;

namespace Coprocessor {

/** This class should contain all options that can be specified for the solver, and its tools.
 * Furthermore, constraints/assertions on parameters can be specified, and checked.
 */
class CP3Config : public Config {
 
  /** pointer to all options in this object - used for parsing and printing the help! */
  vec<Option*> configOptions;
  
public:
 /** default constructor, which sets up all options in their standard format */
 CP3Config (const std::string & presetOptions = "");
 
 /** 
 * List of all used options, public members, can be changed and read directly
 */
 
// options
 IntOption opt_cp3_vars; 	// variable limit to enable CP3
 IntOption opt_cp3_cls;  	// clause limit to enable CP3
 IntOption opt_cp3_lits;
 IntOption opt_cp3_ipvars;  	// variable limit to enable CP3 inprocessing
 IntOption opt_cp3_ipcls;  	// clause limit to enable CP3 inprocessing
 IntOption opt_cp3_iplits;
 BoolOption opt_unlimited  ;
 BoolOption opt_randomized  ;
 IntOption  opt_inprocessInt;
 IntOption  opt_simplifyRounds;
 BoolOption opt_enabled     ;
 BoolOption opt_inprocess   ;
 IntOption  opt_exit_pp     ;
 BoolOption opt_randInp     ;
 BoolOption opt_inc_inp     ;

#if defined TOOLVERSION && TOOLVERSION < 400
       const bool opt_printStats; // do not print stats, if restricted binary is produced
       const  int opt_verbose;        // do not talk during computation!
#else
       BoolOption opt_printStats;
       IntOption  opt_verbose;
#endif

// techniques
 BoolOption opt_up          ;
 BoolOption opt_subsimp     ;
 BoolOption opt_hte         ;
#if defined TOOLVERSION && TOOLVERSION < 355
 const bool opt_bce;
#else
 BoolOption opt_bce         ;
#endif
#if defined TOOLVERSION && TOOLVERSION < 360
  const bool opt_ent;
#else
  BoolOption opt_ent        ;
#endif
 BoolOption opt_la          ;
 BoolOption opt_cce         ;
 BoolOption opt_rate        ;
 BoolOption opt_ee          ;
 BoolOption opt_bve         ;
 BoolOption opt_bva         ;
 BoolOption opt_unhide      ;
 BoolOption opt_probe       ;
 BoolOption opt_ternResolve ;
 BoolOption opt_addRedBins  ;
 BoolOption opt_dense       ;
 BoolOption opt_shuffle     ;
 BoolOption opt_simplify    ;
 BoolOption opt_symm        ;
 BoolOption opt_FM          ;

 
 StringOption opt_ptechs ;
 StringOption opt_itechs ;

// use 2sat and sls only for high versions!
#if defined TOOLVERSION && TOOLVERSION < 301
 const int opt_threads;
 const bool opt_sls;
 const bool opt_sls_phase;
 const int opt_sls_flips;
 const bool opt_xor;
 const bool opt_rew;    
 const bool opt_twosat;
 const bool opt_twosat_init;
 const bool  opt_ts_phase;
#else
 IntOption  opt_threads     ;
 BoolOption opt_sls         ;
 BoolOption opt_sls_phase   ;
 IntOption  opt_sls_flips   ;
 BoolOption opt_xor         ;
 BoolOption opt_rew         ;
 BoolOption opt_twosat      ;
 BoolOption opt_twosat_init ;
 BoolOption opt_ts_phase    ;
#endif

 

 IntOption opt_subsimp_vars; 	// variable limit to enable 
 IntOption opt_subsimp_cls;  	// clause limit to enable 
 IntOption opt_subsimp_lits;	// total literals limit to enable 
 IntOption opt_hte_vars; 	// variable limit to enable 
 IntOption opt_hte_cls;  	// clause limit to enable 
 IntOption opt_hte_lits;	// total literals limit to enable 
 IntOption opt_bce_vars; 	// variable limit to enable 
 IntOption opt_bce_cls;  	// clause limit to enable 
 IntOption opt_bce_lits;	// total literals limit to enable 
 IntOption opt_ent_vars; 	// variable limit to enable 
 IntOption opt_ent_cls;  	// clause limit to enable 
 IntOption opt_ent_lits;	// total literals limit to enable 
 IntOption opt_la_vars; 	// variable limit to enable 
 IntOption opt_la_cls;  	// clause limit to enable 
 IntOption opt_la_lits;	// total literals limit to enable 
 IntOption opt_cce_vars; 	// variable limit to enable 
 IntOption opt_cce_cls;  	// clause limit to enable 
 IntOption opt_cce_lits;	// total literals limit to enable 
 IntOption opt_rate_vars; 	// variable limit to enable 
 IntOption opt_rate_cls;  	// clause limit to enable 
 IntOption opt_rate_lits;	// total literals limit to enable 
 IntOption opt_ee_vars; 	// variable limit to enable 
 IntOption opt_ee_cls;  	// clause limit to enable 
 IntOption opt_ee_lits;	// total literals limit to enable 
 IntOption opt_bve_vars; 	// variable limit to enable 
 IntOption opt_bve_cls;  	// clause limit to enable 
 IntOption opt_bve_lits;	// total literals limit to enable 
 IntOption opt_bva_vars; 	// variable limit to enable 
 IntOption opt_bva_cls;  	// clause limit to enable 
 IntOption opt_bva_lits;	// total literals limit to enable 
 IntOption opt_Ibva_vars; 	// variable limit to enable 
 IntOption opt_Ibva_cls;  	// clause limit to enable 
 IntOption opt_Ibva_lits;	// total literals limit to enable 
 IntOption opt_Xbva_vars; 	// variable limit to enable 
 IntOption opt_Xbva_cls;  	// clause limit to enable 
 IntOption opt_Xbva_lits;	// total literals limit to enable 
 IntOption opt_unhide_vars; 	// variable limit to enable 
 IntOption opt_unhide_cls;  	// clause limit to enable 
 IntOption opt_unhide_lits;	// total literals limit to enable 
 IntOption opt_probe_vars; 	// variable limit to enable 
 IntOption opt_probe_cls;  	// clause limit to enable 
 IntOption opt_probe_lits;	// total literals limit to enable 
 IntOption opt_viv_vars; 	// variable limit to enable 
 IntOption opt_viv_cls;  	// clause limit to enable 
 IntOption opt_viv_lits;	// total literals limit to enable 
 IntOption opt_ternResolve_vars; 	// variable limit to enable 
 IntOption opt_ternResolve_cls;  	// clause limit to enable 
 IntOption opt_ternResolve_lits;	// total literals limit to enable 
 IntOption opt_addRedBins_vars; 	// variable limit to enable 
 IntOption opt_addRedBins_cls;  	// clause limit to enable 
 IntOption opt_addRedBins_lits;	// total literals limit to enable 
 IntOption opt_symm_vars; 	// variable limit to enable 
 IntOption opt_symm_cls;  	// clause limit to enable 
 IntOption opt_symm_lits;	// total literals limit to enable 
 IntOption opt_fm_vars; 	// variable limit to enable 
 IntOption opt_fm_cls;  	// clause limit to enable  
 IntOption opt_fm_lits;	// total literals limit to enable 
 
 IntOption opt_xor_vars; 	// variable limit to enable 
 IntOption opt_xor_cls;  	// clause limit to enable  
 IntOption opt_xor_lits;	// total literals limit to enable 
 IntOption opt_sls_vars; 	// variable limit to enable 
 IntOption opt_sls_cls;  	// clause limit to enable  
 IntOption opt_sls_lits;	// total literals limit to enable 
 IntOption opt_rew_vars; 	// variable limit to enable 
 IntOption opt_rew_cls;  	// clause limit to enable  
 IntOption opt_rew_lits;	// total literals limit to enable 
 
#if defined TOOLVERSION // debug only, if no version is given!
 const bool opt_debug;       
 const int opt_check;
 const int  opt_log;
 const char* printAfter;
#else
 BoolOption opt_debug    ;
 IntOption opt_check    ;
 IntOption  opt_log      ;
 StringOption printAfter ;
#endif
 
//
// BVE
//

#if defined TOOLVERSION && TOOLVERSION < 302
  const int opt_par_bve    ;
  const int  opt_bve_verbose;
#else
 IntOption opt_par_bve         ;
 IntOption  opt_bve_verbose     ;
#endif
 
 IntOption  opt_bve_limit       ;
 IntOption  opt_learnt_growth   ;
 IntOption  opt_resolve_learnts ;
 BoolOption opt_unlimited_bve   ;
 BoolOption opt_bve_strength    ;
 IntOption  opt_bve_reduce_lits ;
 BoolOption opt_bve_findGate    ;
 BoolOption opt_force_gates     ;
 // pick order of eliminations
 IntOption  opt_bve_heap        ;
 // increasing eliminations
 IntOption  opt_bve_grow        ;
 IntOption  opt_bve_growTotal   ;
 BoolOption opt_totalGrow       ;
  
 BoolOption opt_bve_bc          ;
 IntOption heap_updates         ;
 BoolOption opt_bce_only        ;
 BoolOption opt_print_progress  ;
 IntOption  opt_bveInpStepInc   ;

#if defined TOOLVERSION && TOOLVERSION < 302
const int par_bve_threshold ;
const int postpone_locked_neighbors ;
const bool opt_minimal_updates ;
#else
IntOption  par_bve_threshold; 
IntOption  postpone_locked_neighbors;
BoolOption opt_minimal_updates;
#endif

//
// BVA
//
 IntOption  opt_bva_push             ;
 IntOption  opt_bva_VarLimit         ;
 IntOption  opt_bva_Alimit           ;
 BoolOption opt_Abva                 ;
 IntOption  opt_bvaInpStepInc        ;
 IntOption  opt_Abva_heap            ;
 BoolOption opt_bvaComplement        ;
 BoolOption opt_bvaRemoveDubplicates ;
 BoolOption opt_bvaSubstituteOr      ;
#if defined TOOLVERSION  
 const int bva_debug;
#else
 IntOption  bva_debug                ;
#endif

#if defined TOOLVERSION  && TOOLVERSION < 350
 const bool opt_bvaAnalysis ;
 const bool opt_Xbva ;
 const bool opt_Ibva ;
 const int opt_bvaAnalysisDebug ;
 const int opt_bva_Xlimit ;
 const int opt_bva_Ilimit ;
 const int opt_Xbva_heap ;
 const int opt_Ibva_heap ;
#else
 #if defined TOOLVERSION
 const int opt_bvaAnalysisDebug;
#else
 IntOption  opt_bvaAnalysisDebug     ;
#endif
 IntOption  opt_bva_Xlimit           ;
 IntOption  opt_bva_Ilimit           ;
 IntOption  opt_Xbva_heap            ;
 IntOption  opt_Ibva_heap            ;
 IntOption  opt_Xbva                 ;
 IntOption  opt_Ibva                 ;
#endif

//
// BCE
//
BoolOption orderComplements; // sort the heap based on the occurrence of complementary literals
BoolOption bceBinary; // remove binary clauses during BCE
IntOption bceLimit;
BoolOption opt_bce_bce; // actually remove blocked clauses
BoolOption opt_bce_cle; // perform covered literal elimination
BoolOption opt_bce_cla; // perform covered literal addition
BoolOption opt_bce_cle_conservative; // perform CLE conservative and cheap, if tautological resolvents occur
IntOption opt_bceInpStepInc; // add to limit for inprocessing
#if defined TOOLVERSION  
const int opt_bce_verbose;
const bool opt_cle_debug; 
#else
IntOption opt_bce_verbose; // output operation steps
BoolOption opt_bce_debug; // debug output
#endif

//
// LiteralAddition
//
BoolOption opt_la_cla; // perform covered literal addition
BoolOption opt_la_ala; // perform asymmetric literal addition

IntOption claLimit; // number of steps before aborting LA
IntOption claStepSize; // number of extension literals so that literals are removed randomly
IntOption claStepMax; // number of first extension literals that are considered (should be smaller then size!)
IntOption claIterations; // number of iterations to do for CLA

IntOption alaLimit; // number of steps for limits
IntOption alaIterations; // number of iterations to do for ALA
BoolOption ala_binary; // perform ALA with binary clauses
#if defined TOOLVERSION  
const bool opt_la_debug; 
#else
BoolOption opt_la_debug; // debug output
#endif

 
//
// CCE
//
IntOption opt_cceSteps;
IntOption opt_ccelevel;
IntOption opt_ccePercent;
#if defined TOOLVERSION  
const int cce_debug_out;
#else
IntOption cce_debug_out;
#endif
IntOption  opt_cceInpStepInc;

//
// Options for rat elimination
//
BoolOption rate_orderComplements;
Int64Option rate_Limit;
IntOption opt_rate_debug;
IntOption rate_minSize;
 
//
// Dense
//
#if defined TOOLVERSION  
const int dense_debug_out;
#else
IntOption dense_debug_out;
#endif
IntOption  opt_dense_fragmentation;
BoolOption opt_dense_store_forward;
BoolOption opt_dense_keep_assigned;

//
// Entailed
//
#if defined TOOLVERSION && TOOLVERSION < 360
const int opt_entailed_minClsSize;
#else
IntOption opt_entailed_minClsSize;
#endif

#if defined TOOLVERSION 
const int entailed_debug;
#else
IntOption  entailed_debug;
#endif


//
// Equivalence
//
#if defined TOOLVERSION  && TOOLVERSION < 350
const int opt_ee_level            ;
const int opt_ee_gate_limit       ;
const int opt_ee_circuit_iters    ;
const bool opt_ee_eagerEquivalence;
const bool opt_eeGateBigFirst     ;
const char* opt_ee_aagFile        ;
#else
IntOption  opt_ee_level           ;
IntOption  opt_ee_gate_limit      ;
IntOption  opt_ee_circuit_iters   ;
BoolOption opt_ee_eagerEquivalence;
BoolOption opt_eeGateBigFirst     ;
StringOption opt_ee_aagFile       ;
#endif
#if defined TOOLVERSION  
const int ee_debug_out;
#else
IntOption  ee_debug_out           ;
#endif
BoolOption opt_eeSub            ;
BoolOption opt_eeFullReset      ;
IntOption  opt_ee_limit         ;
IntOption  opt_ee_inpStepInc    ;
IntOption  opt_ee_bigIters      ;
BoolOption opt_ee_iterative     ;
BoolOption opt_EE_checkNewSub   ;
BoolOption opt_ee_eager_frozen  ;
//
// Structural hashing options
//
#if defined TOOLVERSION  && TOOLVERSION < 350
const bool circ_AND       ;
const bool circ_ITE       ;
const bool circ_XOR       ;
const bool circ_ExO       ;
const bool circ_genAND    ;
const bool circ_FASUM     ;
const bool circ_BLOCKED   ;
const bool circ_AddBlocked;
const bool circ_NegatedI  ;
const bool circ_Implied   ;
#else
BoolOption circ_AND;
BoolOption circ_ITE;
BoolOption circ_XOR;
BoolOption circ_ExO;
BoolOption circ_genAND;
BoolOption circ_FASUM;

BoolOption circ_BLOCKED;
BoolOption circ_AddBlocked;
BoolOption circ_NegatedI;
BoolOption circ_Implied;
#endif
/// temporary Boolean flag to quickly enable debug output for the whole file
#if defined TOOLVERSION  
  const bool circ_debug_out;
#else
  BoolOption circ_debug_out;
#endif


//
// Fourier Motzkin
//
IntOption  opt_fm_max_constraints;
Int64Option opt_fmLimit    ;
Int64Option opt_fmSearchLimit    ;
IntOption  opt_fmMaxAMO   ;
IntOption  opt_fmGrow     ;
IntOption  opt_fmGrowT    ;
BoolOption opt_atMostTwo  ;
BoolOption opt_fm_twoPr   ;
BoolOption opt_fm_sem     ;
BoolOption opt_findUnit   ;
BoolOption opt_merge      ;
BoolOption opt_fm_avoid_duplicates ;
BoolOption opt_fm_multiVarAMO ;
BoolOption opt_multiVarAMT;
BoolOption opt_cutOff     ;
IntOption opt_newAmo      ;
BoolOption opt_keepAllNew ;
IntOption opt_newAlo      ;
IntOption opt_newAlk      ;
BoolOption opt_checkSub   ;
BoolOption opt_rem_first  ;
IntOption opt_minCardClauseSize;
IntOption opt_maxCardClauseSize; 
IntOption opt_maxCardSize      ;
Int64Option opt_semSearchLimit ;
BoolOption opt_semDebug        ;
BoolOption opt_noReduct        ;

#if defined TOOLVERSION 
const int fm_debug_out;
#else
IntOption fm_debug_out       ;
#endif

//
// Hidden Tautology Elimination
//
IntOption opt_hte_steps;
#if defined TOOLVERSION && TOOLVERSION < 302
const bool opt_par_hte;
#else
BoolOption opt_par_hte;
#endif
#if defined TOOLVERSION  
const int hte_debug_out;
const bool opt_hteTalk;
#else
IntOption hte_debug_out;
BoolOption opt_hteTalk ;
#endif
IntOption  opt_hte_inpStepInc;

//
// Probing
//
IntOption pr_uip;
BoolOption opt_pr_probeBinary;
BoolOption pr_double     ;
BoolOption pr_probe      ;
BoolOption pr_rootsOnly  ;
BoolOption pr_repeat     ;
IntOption pr_clsSize     ;
BoolOption pr_LHBR       ; // LHBR during probing
IntOption pr_prLimit     ;
BoolOption pr_EE         ;
BoolOption pr_vivi       ;
IntOption pr_keepLearnts ;
IntOption pr_keepImplied ;
IntOption pr_viviPercent ;
IntOption pr_viviLimit   ;
IntOption  pr_opt_inpStepInc1      ;
IntOption  pr_opt_inpStepInc2      ;
IntOption  pr_keepLHBRs  ;
BoolOption pr_necBinaries  ;
#if defined TOOLVERSION  
const int pr_debug_out;
#else
IntOption pr_debug_out;
#endif

//
// Unit Propagation
//
#if defined TOOLVERSION  
const int up_debug_out;
#else
IntOption up_debug_out;
#endif

//
// Resolution and Redundancy Addition
//
BoolOption   opt_res3_use_binaries ;
IntOption    opt_res3_steps    ;
IntOption    opt_res3_newCls   ;
BoolOption   opt_res3_reAdd    ;
BoolOption   opt_res3_use_subs ;
DoubleOption opt_add2_percent  ;
BoolOption   opt_add2_red      ;
BoolOption   opt_add2_red_level;
BoolOption   opt_add2_red_lea  ;
BoolOption   opt_add2_red_start;
IntOption  opt_res3_inpStepInc ;
IntOption  opt_add2_inpStepInc ;
/// enable this parameter only during debug!
#if defined TOOLVERSION  
const bool res3_debug_out;
#else
BoolOption res3_debug_out      ;
#endif

//
// Rewriter
//
 IntOption  opt_rew_min   ;   
 IntOption  opt_rew_iter   ;  
 IntOption  opt_rew_minAMO ;  
 IntOption  opt_rew_limit  ;  
 IntOption  opt_rew_Varlimit ;
 IntOption  opt_rew_Addlimit ;
 BoolOption opt_rew_amo    ;  
 BoolOption opt_rew_imp    ;  
 BoolOption opt_rew_scan_exo ;
 BoolOption opt_rew_merge_amo;
 BoolOption opt_rew_rem_first;
 BoolOption opt_rew_avg     ; 
 BoolOption opt_rew_ratio  ;  
 BoolOption opt_rew_once     ;
 BoolOption opt_rew_stat_only;
 IntOption  opt_rew_min_imp_size     ;   
 BoolOption opt_rew_impl_pref_small   ;  
 IntOption  opt_rew_inpStepInc     ;
#if defined TOOLVERSION 
 const int rew_debug_out;
#else
 IntOption rew_debug_out;           
#endif
 
//
// Shuffle
//
IntOption opt_shuffle_seed;
BoolOption opt_shuffle_order;
#if defined TOOLVERSION  
const int shuffle_debug_out;
#else
IntOption shuffle_debug_out;
#endif

//
// Sls
//
#if defined TOOLVERSION 
const bool opt_sls_debug;
#else
BoolOption opt_sls_debug ;
#endif
IntOption  opt_sls_ksat_flips ;
IntOption  opt_sls_rand_walk  ;
BoolOption opt_sls_adopt      ;

//
// Subsumption
//
 BoolOption  opt_sub_naivStrength;
 IntOption   opt_sub_allStrengthRes; 
 BoolOption  opt_sub_strength     ;
 BoolOption  opt_sub_preferLearned; 
 IntOption   opt_sub_subLimit     ; 
 IntOption   opt_sub_strLimit     ; 
 IntOption   opt_sub_callIncrease ; 
 IntOption  opt_sub_inpStepInc    ;
#if defined TOOLVERSION && TOOLVERSION < 302
 const int   opt_sub_par_strength ;
 const bool  opt_sub_lock_stats   ;
 const int   opt_sub_par_subs     ;
 const int   opt_sub_par_subs_counts;
 const int   opt_sub_chunk_size     ;
 const int   opt_sub_par_str_minCls ;
#else
 IntOption   opt_sub_par_strength   ;
 BoolOption  opt_sub_lock_stats     ;
 IntOption   opt_sub_par_subs       ;
 IntOption   opt_sub_par_subs_counts;
 IntOption   opt_sub_chunk_size     ;
 IntOption   opt_sub_par_str_minCls ;
#endif
#if defined TOOLVERSION
 const int opt_sub_debug;
#else
 IntOption   opt_sub_debug  ;
#endif

//
// Symmetry Breaker
//
 BoolOption    sym_opt_hsize          ;
 BoolOption    sym_opt_hpol           ;
 BoolOption    sym_opt_hpushUnit      ; // there should be a parameter delay-units already!
 IntOption     sym_opt_hmin           ;
 DoubleOption  sym_opt_hratio         ;
 IntOption     sym_opt_iter           ;
 BoolOption    sym_opt_pairs          ;
 BoolOption    sym_opt_print          ;
 BoolOption    sym_opt_exit           ;
 BoolOption    sym_opt_hprop          ;
 BoolOption    sym_opt_hpropF         ;
 BoolOption    sym_opt_hpropA         ;
 BoolOption    sym_opt_cleanLearn     ;
 IntOption     sym_opt_conflicts      ;
 IntOption     sym_opt_total_conflicts;
#if defined TOOLVERSION  
 const int sym_debug_out;
#else
 IntOption sym_debug_out;
#endif
 
//
// Twosat
//
#if defined TOOLVERSION 
 const int twosat_debug_out;
 const bool twosat_useUnits;
 const bool twosat_clearQueue;
#else
 IntOption twosat_debug_out  ;
 BoolOption twosat_useUnits  ;
 BoolOption twosat_clearQueue;
#endif
 
//
// Unhide
//
 IntOption  opt_uhd_Iters     ;
 BoolOption opt_uhd_Trans     ;
 IntOption  opt_uhd_UHLE      ;
 BoolOption opt_uhd_UHTE      ;
 BoolOption opt_uhd_NoShuffle ;
 BoolOption opt_uhd_EE        ;
 BoolOption opt_uhd_TestDbl   ;
 IntOption  opt_uhd_probe     ;
 IntOption  opt_uhd_fullProbe ;
 BoolOption opt_uhd_probeEE   ;
 BoolOption opt_uhd_fullBorder;
#if defined TOOLVERSION  
 const int opt_uhd_Debug;
#else
 IntOption  opt_uhd_Debug;
#endif
 
//
// Xor
//
 IntOption  opt_xorMatchLimit ;
 IntOption  opt_xorFindLimit  ;
 IntOption  opt_xor_selectX     ;
 BoolOption opt_xor_keepUsed    ;
 BoolOption opt_xor_findSubsumed;
 BoolOption opt_xor_findResolved;
 
#if defined TOOLVERSION
 const int opt_xor_debug;
#else
 IntOption  opt_xor_debug;
#endif
private:
 int dummy;
};
 
}

#endif