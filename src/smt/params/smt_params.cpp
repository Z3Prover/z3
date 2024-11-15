/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#include "smt/params/smt_params.h"
#include "smt/params/smt_params_helper.hpp"
#include "util/gparams.h"
#include "params/solver_params.hpp"

void smt_params::updt_local_params(params_ref const & _p) {
    smt_params_helper p(_p);
    m_auto_config = p.auto_config() && gparams::get_value("auto_config") == "true"; // auto-config is not scoped by smt in gparams.
    m_random_seed = p.random_seed();
    m_relevancy_lvl = p.relevancy();
    m_ematching   = p.ematching();
    m_induction   = p.induction();
    m_clause_proof = p.clause_proof();
    m_phase_selection = static_cast<phase_selection>(p.phase_selection());
    if (m_phase_selection > PS_THEORY) throw default_exception("illegal phase selection numeral");
    m_phase_caching_on = p.phase_caching_on();
    m_phase_caching_off = p.phase_caching_off();
    m_restart_strategy = static_cast<restart_strategy>(p.restart_strategy());
    if (m_restart_strategy > RS_ARITHMETIC) throw default_exception("illegal restart strategy numeral");
    m_restart_factor = p.restart_factor();
    m_case_split_strategy = static_cast<case_split_strategy>(p.case_split());
    m_theory_case_split = p.theory_case_split();
    m_theory_aware_branching = p.theory_aware_branching();
    m_delay_units = p.delay_units();
    m_delay_units_threshold = p.delay_units_threshold();
    m_preprocess = _p.get_bool("preprocess", true); // hidden parameter
    m_max_conflicts = p.max_conflicts();
    m_restart_max   = p.restart_max();
    m_cube_depth    = p.cube_depth();
    m_threads       = p.threads();
    m_threads_max_conflicts  = p.threads_max_conflicts();
    m_threads_cube_frequency = p.threads_cube_frequency();
    m_core_validate = p.core_validate();
    m_sls_enable = p.sls_enable();
    m_sls_parallel = p.sls_parallel();
    m_logic = _p.get_sym("logic", m_logic);
    m_string_solver = p.string_solver();
    m_up_persist_clauses = p.up_persist_clauses();
    validate_string_solver(m_string_solver);
    if (_p.get_bool("arith.greatest_error_pivot", false))
        m_arith_pivot_strategy = arith_pivot_strategy::ARITH_PIVOT_GREATEST_ERROR;
    else if (_p.get_bool("arith.least_error_pivot", false))
        m_arith_pivot_strategy = arith_pivot_strategy::ARITH_PIVOT_LEAST_ERROR;
    theory_array_params::updt_params(_p);
    m_dump_benchmarks = false;
    m_dump_min_time = 0.5;
    m_dump_recheck = false;
    solver_params sp(_p);
    m_axioms2files = sp.axioms2files();
    m_lemmas2console = sp.lemmas2console();
    m_instantiations2console = sp.instantiations2console();
    m_proof_log = sp.proof_log();
    
}

void smt_params::updt_params(params_ref const & p) {
    preprocessor_params::updt_params(p);
    dyn_ack_params::updt_params(p);
    qi_params::updt_params(p);
    theory_arith_params::updt_params(p);
    theory_bv_params::updt_params(p);
    theory_pb_params::updt_params(p);
    // theory_array_params::updt_params(p);
    theory_datatype_params::updt_params(p);
    theory_str_params::updt_params(p);
    updt_local_params(p);
}

void smt_params::updt_params(context_params const & p) {
    m_auto_config    = p.m_auto_config;
    m_model          = p.m_model;
}

#define DISPLAY_PARAM(X) out << #X"=" << X << '\n';

void smt_params::display(std::ostream & out) const {
    preprocessor_params::display(out);
    dyn_ack_params::display(out);
    qi_params::display(out);
    theory_arith_params::display(out);
    theory_array_params::display(out);
    theory_bv_params::display(out);
    theory_pb_params::display(out);
    theory_datatype_params::display(out);
    theory_str_params::display(out);

    DISPLAY_PARAM(m_display_proof);
    DISPLAY_PARAM(m_display_dot_proof);
    DISPLAY_PARAM(m_display_unsat_core);
    DISPLAY_PARAM(m_check_proof);
    DISPLAY_PARAM(m_eq_propagation);
    DISPLAY_PARAM(m_binary_clause_opt);
    DISPLAY_PARAM(m_relevancy_lvl);
    DISPLAY_PARAM(m_relevancy_lemma);
    DISPLAY_PARAM(m_random_seed);
    DISPLAY_PARAM(m_random_var_freq);
    DISPLAY_PARAM(m_inv_decay);
    DISPLAY_PARAM(m_clause_decay);
    DISPLAY_PARAM(m_random_initial_activity);
    DISPLAY_PARAM(m_phase_selection);
    DISPLAY_PARAM(m_phase_caching_on);
    DISPLAY_PARAM(m_phase_caching_off);
    DISPLAY_PARAM(m_minimize_lemmas);
    DISPLAY_PARAM(m_max_conflicts);
    DISPLAY_PARAM(m_cube_depth);
    DISPLAY_PARAM(m_threads);
    DISPLAY_PARAM(m_threads_max_conflicts);
    DISPLAY_PARAM(m_threads_cube_frequency);
    DISPLAY_PARAM(m_simplify_clauses);
    DISPLAY_PARAM(m_tick);
    DISPLAY_PARAM(m_display_features);
    DISPLAY_PARAM(m_new_core2th_eq);
    DISPLAY_PARAM(m_ematching);
    DISPLAY_PARAM(m_induction);
    DISPLAY_PARAM(m_clause_proof);
    DISPLAY_PARAM(m_proof_log);

    DISPLAY_PARAM(m_case_split_strategy);
    DISPLAY_PARAM(m_rel_case_split_order);
    DISPLAY_PARAM(m_lookahead_diseq);

    DISPLAY_PARAM(m_delay_units);
    DISPLAY_PARAM(m_delay_units_threshold);

    DISPLAY_PARAM(m_theory_resolve);

    DISPLAY_PARAM(m_restart_strategy);
    DISPLAY_PARAM(m_restart_initial);
    DISPLAY_PARAM(m_restart_factor);
    DISPLAY_PARAM(m_restart_adaptive);
    DISPLAY_PARAM(m_agility_factor);
    DISPLAY_PARAM(m_restart_agility_threshold);

    DISPLAY_PARAM(m_up_persist_clauses);
    DISPLAY_PARAM(m_lemma_gc_strategy);
    DISPLAY_PARAM(m_lemma_gc_half);
    DISPLAY_PARAM(m_recent_lemmas_size);
    DISPLAY_PARAM(m_lemma_gc_initial);
    DISPLAY_PARAM(m_lemma_gc_factor);
    DISPLAY_PARAM(m_new_old_ratio);
    DISPLAY_PARAM(m_new_clause_activity);
    DISPLAY_PARAM(m_old_clause_activity);
    DISPLAY_PARAM(m_new_clause_relevancy);
    DISPLAY_PARAM(m_old_clause_relevancy);
    DISPLAY_PARAM(m_inv_clause_decay);

    DISPLAY_PARAM(m_axioms2files);
    DISPLAY_PARAM(m_lemmas2console);
    DISPLAY_PARAM(m_logic);
    DISPLAY_PARAM(m_string_solver);

    DISPLAY_PARAM(m_profile_res_sub);
    DISPLAY_PARAM(m_display_bool_var2expr);
    DISPLAY_PARAM(m_display_ll_bool_var2expr);

    DISPLAY_PARAM(m_model);
    DISPLAY_PARAM(m_model_on_timeout);
    DISPLAY_PARAM(m_model_on_final_check);

    DISPLAY_PARAM(m_progress_sampling_freq);

    DISPLAY_PARAM(m_core_validate);

    DISPLAY_PARAM(m_preprocess);
    DISPLAY_PARAM(m_user_theory_preprocess_axioms);
    DISPLAY_PARAM(m_user_theory_persist_axioms);
    DISPLAY_PARAM(m_at_labels_cex);
    DISPLAY_PARAM(m_check_at_labels);
    DISPLAY_PARAM(m_dump_goal_as_smt);
    DISPLAY_PARAM(m_auto_config);
}

void smt_params::validate_string_solver(symbol const& s) const {
    if (s == "z3str3" || s == "seq" || s == "empty" || s == "auto" || s == "none")
        return;
    throw default_exception("Invalid string solver value. Legal values are z3str3, seq, empty, auto, none");
}

void smt_params::setup_QF_UF() {
    m_relevancy_lvl           = 0;
    m_nnf_cnf                 = false;
    m_restart_strategy        = RS_LUBY;
    m_phase_selection         = PS_CACHING_CONSERVATIVE2;
    m_random_initial_activity = IA_RANDOM;
}

void smt_params::setup_QF_RDL() {
    m_relevancy_lvl       = 0;
    m_arith_eq2ineq       = true;
    m_arith_reflect       = false;
    m_arith_propagate_eqs = false;
    m_nnf_cnf             = false;
}

void smt_params::setup_QF_RDL(static_features & st) {

}

void smt_params::setup_QF_IDL() {
    m_relevancy_lvl       = 0;
    m_arith_eq2ineq       = true;
    m_arith_reflect       = false;
    m_arith_propagate_eqs = false;
    m_arith_small_lemma_size = 30;
    m_nnf_cnf             = false;
}

void smt_params::setup_QF_IDL(static_features & st) {

}

void smt_params::setup_QF_LRA() {
    m_relevancy_lvl       = 0;
    m_arith_eq2ineq       = true;
    m_arith_reflect       = false;
    m_arith_propagate_eqs = false;
    m_eliminate_term_ite  = true;
    m_nnf_cnf             = false;
    m_phase_selection     = PS_THEORY;
}

void smt_params::setup_QF_LRA(static_features const& st) {
    m_relevancy_lvl       = 0;
    m_arith_eq2ineq       = true;
    m_arith_reflect       = false;
    m_arith_propagate_eqs = false;
    m_eliminate_term_ite  = true;
    m_nnf_cnf             = false;
    if (numerator(st.m_arith_k_sum) > rational(2000000) && denominator(st.m_arith_k_sum) > rational(500)) {
        m_relevancy_lvl       = 2;
        m_relevancy_lemma     = false;
    }
    m_phase_selection       = PS_THEORY;
    if (!st.m_cnf) {
        m_restart_strategy      = RS_GEOMETRIC;
        m_arith_stronger_lemmas = false;
        m_restart_adaptive      = false;
    }
    m_arith_small_lemma_size = 32;
}

void smt_params::setup_QF_LIA() {
    m_relevancy_lvl       = 0;
    m_arith_eq2ineq       = true;
    m_arith_reflect       = false; 
    m_arith_propagate_eqs = false; 
    m_nnf_cnf             = false;            
}

void smt_params::setup_QF_LIA(static_features const& st) {
    m_relevancy_lvl       = 0;
    m_arith_eq2ineq       = true;
    m_arith_reflect       = false; 
    m_arith_propagate_eqs = false;
    m_nnf_cnf             = false;
    if (st.m_max_ite_tree_depth > 50) {
        m_arith_eq2ineq        = false;
        m_pull_cheap_ite       = true;
        m_arith_propagate_eqs  = true;
        m_relevancy_lvl        = 2; 
        m_relevancy_lemma      = false;
    }
    else if (st.m_num_clauses == st.m_num_units) {
        m_arith_gcd_test         = false;
        m_arith_branch_cut_ratio = 4;
        m_relevancy_lvl          = 2; 
        m_arith_eq2ineq          = true;
        m_eliminate_term_ite     = true;
    } 
    else {
        m_eliminate_term_ite   = true;
        m_restart_adaptive     = false;
        m_restart_strategy     = RS_GEOMETRIC;
        m_restart_factor       = 1.5;
    }
    if (st.m_num_bin_clauses + st.m_num_units == st.m_num_clauses && st.m_cnf && st.m_arith_k_sum > rational(100000)) {
        m_arith_bound_prop      = bound_prop_mode::BP_NONE;
        m_arith_stronger_lemmas = false;
    }
}

void smt_params::setup_QF_UFIDL() {
    m_relevancy_lvl = 0;
    m_arith_reflect = false;
    m_nnf_cnf = false;
    m_arith_eq_bounds = true;
    m_arith_eq2ineq = true;
    // m_params.m_phase_selection  = PS_THEORY;
    m_restart_strategy = RS_GEOMETRIC;
    m_restart_factor = 1.5;
    m_restart_adaptive = false;
}

void smt_params::setup_QF_UFLIA() {
    m_relevancy_lvl       = 0;
    m_arith_reflect       = false; 
    m_nnf_cnf             = false;
    m_arith_propagation_threshold = 1000;
}


void smt_params::setup_QF_UFLRA() {
    m_relevancy_lvl       = 0;
    m_arith_reflect       = false; 
    m_nnf_cnf             = false;
}

void smt_params::setup_QF_BV() {
    m_relevancy_lvl       = 0;
    m_arith_reflect       = false; 
    m_bv_cc               = false;
    m_bb_ext_gates        = true;
    m_nnf_cnf             = false;
}

void smt_params::setup_QF_AUFBV() {
    m_array_mode          = AR_FULL;
    m_relevancy_lvl       = 0;
    m_bv_cc               = false;
    m_bb_ext_gates        = true;
    m_nnf_cnf             = false;
}

void smt_params::setup_QF_AX() {
    m_array_mode          = AR_SIMPLE;
    m_nnf_cnf             = false;
}

void smt_params::setup_QF_AX(static_features const& st) {
    m_array_mode          = st.m_has_ext_arrays ? AR_FULL : AR_SIMPLE;
    m_nnf_cnf             = false;
    if (st.m_num_clauses == st.m_num_units) {
        m_relevancy_lvl       = 0;
        m_phase_selection     = PS_ALWAYS_FALSE;
    }
    else 
        m_relevancy_lvl       = 2;
}

void smt_params::setup_QF_AUFLIA() {
    m_array_mode          = AR_SIMPLE;
    m_nnf_cnf             = false;
    m_relevancy_lvl       = 2;
    m_restart_strategy    = RS_GEOMETRIC;
    m_restart_factor      = 1.5;
    m_phase_selection     = PS_CACHING_CONSERVATIVE2;
}

void smt_params::setup_QF_AUFLIA(static_features const& st) {
    m_array_mode          = st.m_has_ext_arrays ? AR_FULL : AR_SIMPLE;
    if (st.m_has_real)
        throw default_exception("Benchmark has real variables but it is marked as QF_AUFLIA (arrays, uninterpreted functions and linear integer arithmetic).");
    m_nnf_cnf             = false;
    if (st.m_num_clauses == st.m_num_units) {
        TRACE("QF_AUFLIA", tout << "using relevancy: 0\n";);
        m_relevancy_lvl       = 0;
        m_phase_selection     = PS_ALWAYS_FALSE;
    }
    else {
        m_relevancy_lvl           = 0; // it was 2, for some reason 2 doesn't work anymore TODO: investigate
        m_restart_strategy        = RS_GEOMETRIC;
        m_restart_factor          = 1.5;
        m_phase_selection         = PS_CACHING_CONSERVATIVE2;
        m_random_initial_activity = IA_ZERO;
    }    
}

void smt_params::setup_AUFLIA(bool simple_array) {
    m_array_mode              = simple_array ? AR_SIMPLE : AR_FULL;
    m_pi_use_database         = true;
    m_phase_selection         = PS_ALWAYS_FALSE;
    m_restart_strategy        = RS_GEOMETRIC;
    m_restart_factor          = 1.5;
    m_eliminate_bounds        = true;
    m_qi_quick_checker        = MC_UNSAT;
    m_qi_lazy_threshold       = 20;
    m_mbqi                    = true; // enabling MBQI and MACRO_FINDER by default :-)
    
    // MACRO_FINDER is a horrible for AUFLIA and UFNIA benchmarks (boogie benchmarks in general)
    // It destroys the existing patterns.
    // m_macro_finder            = true; 
    
    if (m_ng_lift_ite == lift_ite_kind::LI_NONE)
        m_ng_lift_ite = lift_ite_kind::LI_CONSERVATIVE;
}

void smt_params::setup_AUFLIA(static_features const & st) {
    m_qi_eager_threshold      = st.m_num_quantifiers_with_patterns == 0 ? 5 : 7;
}

void smt_params::setup_AUFLIRA(bool simple_array) {
    m_array_mode              = simple_array ? AR_SIMPLE : AR_FULL;
    m_phase_selection         = PS_ALWAYS_FALSE;
    m_eliminate_bounds        = true;
    m_qi_quick_checker        = MC_UNSAT;
    m_qi_eager_threshold      = 5;
    // Added for MBQI release
    m_qi_lazy_threshold       = 20;
    // 
    m_macro_finder            = true;
    if (m_ng_lift_ite == lift_ite_kind::LI_NONE)
        m_ng_lift_ite         = lift_ite_kind::LI_CONSERVATIVE;
    m_pi_max_multi_patterns   = 10; //<< it was used for SMT-COMP
    m_array_lazy_ieq          = true;
    m_array_lazy_ieq_delay    = 4;
    //
    m_mbqi                    = true; // enabling MBQI by default :-)
    // 
}

void smt_params::setup_LRA() {
    m_relevancy_lvl       = 0;
    m_arith_reflect       = false;
    m_arith_propagate_eqs = false;
    m_eliminate_term_ite  = true;
}

