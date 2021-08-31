/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    gparams.cpp

Abstract:

    Global parameter management.

Author:

    Leonardo (leonardo) 2012-11-29

Notes:

--*/
#include "util/gparams.h"
#include "util/str_hashtable.h"
#include "util/trace.h"
#include "util/mutex.h"
#include "util/region.h"
#include "util/map.h"

static DECLARE_MUTEX(gparams_mux);

extern void gparams_register_modules();

static char const * g_old_params_names[] = {
    "arith_adaptive","arith_adaptive_assertion_threshold","arith_adaptive_gcd","arith_adaptive_propagation_threshold","arith_add_binary_bounds","arith_blands_rule_threshold","arith_branch_cut_ratio","arith_dump_lemmas","arith_eager_eq_axioms","arith_eager_gcd","arith_eq_bounds","arith_euclidean_solver","arith_expand_eqs","arith_force_simplex","arith_gcd_test","arith_ignore_int","arith_lazy_adapter","arith_lazy_pivoting","arith_max_lemma_size","arith_process_all_eqs","arith_propagate_eqs","arith_propagation_mode","arith_propagation_threshold","arith_prop_strategy","arith_random_initial_value","arith_random_lower","arith_random_seed","arith_random_upper","arith_reflect","arith_skip_big_coeffs","arith_small_lemma_size","arith_solver","arith_stronger_lemmas","array_always_prop_upward","array_canonize","array_cg","array_delay_exp_axiom","array_extensional","array_laziness","array_lazy_ieq","array_lazy_ieq_delay","array_solver","array_weak","async_commands","at_labels_cex","auto_config","bb_eager","bb_ext_gates","bb_quantifiers","bin_clauses","bit2int","bv2int_distribute","bv_blast_max_size","bv_cc","bv_enable_int2bv_propagation","bv_lazy_le","bv_max_sharing","bv_reflect","bv_solver","case_split","check_at_labels","check_proof","cnf_factor","cnf_mode","context_simplifier","dack","dack_eq","dack_factor","dack_gc","dack_gc_inv_decay","dack_threshold","default_qid","default_table","default_table_checked","delay_units","delay_units_threshold","der","display_config","display_dot_proof","display_error_for_visual_studio","display_features","display_proof","display_unsat_core","distribute_forall","dt_lazy_splits","dump_goal_as_smt","elim_and","elim_bounds","elim_nlarith_quantifiers","elim_quantifiers","elim_term_ite","ematching","engine","eq_propagation","hi_div0","ignore_bad_patterns","ignore_setparameter","instruction_max","inst_gen","interactive","internalizer_nnf","lemma_gc_factor","lemma_gc_half","lemma_gc_initial","lemma_gc_new_clause_activity","lemma_gc_new_clause_relevancy","lemma_gc_new_old_ratio","lemma_gc_old_clause_activity","lemma_gc_old_clause_relevancy","lemma_gc_strategy","lift_ite","lookahead_diseq","macro_finder","max_conflicts","max_counterexamples","mbqi","mbqi_force_template","mbqi_max_cexs","mbqi_max_cexs_incr","mbqi_max_iterations","mbqi_trace","minimize_lemmas","model","model_compact","model_completion","model_display_arg_sort","model_hide_unused_partitions","model_on_final_check","model_on_timeout","model_partial","model_v1","model_v2","model_validate","new_core2th_eq","ng_lift_ite","nl_arith","nl_arith_branching","nl_arith_gb","nl_arith_gb_eqs","nl_arith_gb_perturbate","nl_arith_gb_threshold","nl_arith_max_degree","nl_arith_rounds","nnf_factor","nnf_ignore_labels","nnf_mode","nnf_sk_hack","order","order_var_weight","order_weights","phase_selection","pi_arith","pi_arith_weight","pi_avoid_skolems","pi_block_looop_patterns","pi_max_multi_patterns","pi_non_nested_arith_weight","pi_nopat_weight","pi_pull_quantifiers","pi_use_database","pi_warnings","pp_bounded","pp_bv_literals","pp_bv_neg","pp_decimal","pp_decimal_precision","pp_fixed_indent","pp_flat_assoc","pp_max_depth","pp_max_indent","pp_max_num_lines","pp_max_ribbon","pp_max_width","pp_min_alias_size","pp_simplify_implies","pp_single_line","precedence","precedence_gen","pre_demodulator","pre_simplifier","pre_simplify_expr","profile_res_sub","progress_sampling_freq","proof_mode","propagate_booleans","propagate_values","pull_cheap_ite_trees","pull_nested_quantifiers","qi_conservative_final_check","qi_cost","qi_eager_threshold","qi_lazy_instantiation","qi_lazy_quick_checker","qi_lazy_threshold","qi_max_eager_multi_patterns","qi_max_instances","qi_max_lazy_multi_pattern_matching","qi_new_gen","qi_profile","qi_profile_freq","qi_promote_unsat","qi_quick_checker","quasi_macros","random_case_split_freq","random_initial_activity","random_seed","recent_lemma_threshold","reduce_args","refine_inj_axiom","relevancy","relevancy_lemma","rel_case_split_order","restart_adaptive","restart_agility_threshold","restart_factor","restart_initial","restart_strategy","restricted_quasi_macros","simplify_clauses","smtlib2_compliant","smtlib_category","smtlib_dump_lemmas","smtlib_logic","smtlib_source_info","smtlib_trace_path","soft_timeout","solver","spc_bs","spc_es","spc_factor_subsumption_index_opt","spc_initial_subsumption_index_opt","spc_max_subsumption_index_features","spc_min_func_freq_subsumption_index","spc_num_iterations","spc_trace","statistics","strong_context_simplifier","tick","trace","trace_file_name","type_check","user_theory_persist_axioms","user_theory_preprocess_axioms","verbose","warning","well_sorted_check","z3_solver_ll_pp","z3_solver_smt_pp", nullptr };

static bool is_old_param_name(std::string const & name) {
    char const * const * it = g_old_params_names;
    while (*it) {
        if (name == *it)
            return true;
        it++;
    }
    return false;
}

static char const * g_params_renames[] = {
    "proof_mode", "proof",
    "soft_timeout", "timeout",
    "mbqi", "smt.mbqi",
    "relevancy", "smt.relevancy",
    "ematching", "smt.ematching",
    "macro_finder", "smt.macro_finder",
    "delay_units", "smt.delay_units",
    "case_split", "smt.case_split",
    "phase_selection", "smt.phase_selection",
    "restart_strategy", "smt.restart_strategy",
    "restart_factor", "smt.restart_factor",
    "arith_random_initial_value", "smt.arith.random_initial_value",
    "bv_reflect", "smt.bv.reflect",
    "bv_enable_int2bv_propagation", "smt.bv.enable_int2bv",
    "qi_cost", "smt.qi.cost",
    "qi_eager_threshold", "smt.qi.eager_threshold",
    "nl_arith", "smt.arith.nl",
    "pull_nested_quantifiers", "smt.pull_nested_quantifiers",
    "nnf_sk_hack", "nnf.sk_hack",
    "model_v2", "model.v2",
    "pi_non_nested_arith_weight", "pi.non_nested_arith_weight",
    "pi_warnings", "pi.warnings",
    "pp_decimal", "pp.decimal",
    "pp_decimal", "pp.decimal_precision",
    "pp_bv_literals", "pp.bv_literals",
    "pp_bv_neg", "pp.bv_neg",
    "pp_max_depth", "pp.max_depth",
    "pp_min_alias_size", "pp.min_alias_size",
    nullptr };

static char const * get_new_param_name(std::string const & p) {
    char const * const * it = g_params_renames;
    while (*it) {
        if (p == *it) {
            it++;
            return *it;
        }
        it += 2;
    }
    return nullptr;
}

template <typename T>
class smap : public map<char const*, T, str_hash_proc, str_eq_proc> {};

typedef std::function<param_descrs*(void)> lazy_descrs_t;

class lazy_param_descrs {
    param_descrs*      m_descrs;
    ptr_vector<lazy_descrs_t>      m_mk;

    void apply(lazy_descrs_t& f) {
        param_descrs* d = f();
        if (m_descrs) {
            m_descrs->copy(*d);
            dealloc(d);            
        }
        else {
            m_descrs = d;
        }
    }
    
    void reset_mk() {
        for (auto* f : m_mk) dealloc(f);
        m_mk.reset();
    }

public:
    lazy_param_descrs(lazy_descrs_t& f): m_descrs(nullptr) {
        append(f);
    }

    ~lazy_param_descrs() { 
        dealloc(m_descrs);  
        reset_mk();
    }

    param_descrs* deref() {
        for (auto* f : m_mk) apply(*f);
        reset_mk();        
        return m_descrs;
    }

    void append(lazy_descrs_t& f) {
        m_mk.push_back(alloc(lazy_descrs_t, f));        
    }
};

struct gparams::imp {
    bool                 m_modules_registered;
    smap<lazy_param_descrs*> m_module_param_descrs;
    smap<char const *>   m_module_descrs;
    param_descrs         m_param_descrs;
    smap<params_ref* >   m_module_params;
    params_ref           m_params;
    region               m_region;
    std::string          m_buffer;

    void check_registered() {
        if (m_modules_registered)
            return;
        m_modules_registered = true;
        gparams_register_modules();
    }

    smap<lazy_param_descrs*> & get_module_param_descrs() { 
        check_registered(); return m_module_param_descrs; 
    }

    smap<char const *> & get_module_descrs() { check_registered(); return m_module_descrs; }
    param_descrs & get_param_descrs() { check_registered(); return m_param_descrs; }

    char * cpy(char const* s) {
        char * r = new (m_region) char[strlen(s)+1];
        memcpy(r, s, strlen(s)+1);
        return r;
    }

    bool get_module_param_descr(std::string const& m, param_descrs*& d) {
        return get_module_param_descr(m.c_str(), d);
    }

    bool get_module_param_descr(char const* m, param_descrs*& d) {
        check_registered(); 
        lazy_param_descrs* ld;
        return m_module_param_descrs.find(m, ld) && (d = ld->deref(), true);
    }

public:
    imp():
        m_modules_registered(false) {
    }

    ~imp() {
        reset();
        for (auto & kv : m_module_param_descrs) {
            dealloc(kv.m_value);
        }
    }

    void reset() {
        lock_guard lock(*gparams_mux);
        m_params.reset();
        for (auto & kv : m_module_params) {
            dealloc(kv.m_value);
        }
        m_module_params.reset();        
        m_region.reset();
    }

    // -----------------------------------------------
    //
    // Module registration routines.
    // They are invoked when descriptions are initialized
    //
    // -----------------------------------------------

    void register_global(param_descrs & d) {
        // Don't need synchronization here, this method
        // is invoked from check_registered that is already protected.
        m_param_descrs.copy(d);
    }

    void register_module(char const * module_name, lazy_descrs_t& f) {
        // Don't need synchronization here, this method
        // is invoked from check_registered that is already protected.
        
        lazy_param_descrs * ld;
        if (m_module_param_descrs.find(module_name, ld)) {
            ld->append(f);
        }
        else {
            ld = alloc(lazy_param_descrs, f);
            m_module_param_descrs.insert(cpy(module_name), ld);
        }
    }

    void register_module_descr(char const * module_name, char const * descr) {
        // Don't need synchronization here, this method
        // is invoked from check_registered that is already protected.
        if (!m_module_descrs.contains(module_name)) {
            m_module_descrs.insert(cpy(module_name), descr);
        }
    }

    // -----------------------------------------------
    //
    // Parameter setting & retrieval
    //
    // -----------------------------------------------

    void normalize(char const * name, /* out */ std::string & mod_name, /* out */ std::string & param_name) {
        if (*name == ':')
            name++;
        std::string tmp = name;
        unsigned n = static_cast<unsigned>(tmp.size());
        for (unsigned i = 0; i < n; i++) {
            if (tmp[i] >= 'A' && tmp[i] <= 'Z')
                tmp[i] = tmp[i] - 'A' + 'a';
            else if (tmp[i] == '-')
                tmp[i] = '_';
        }
        for (unsigned i = 0; i < n; i++) {
            if (tmp[i] == '.') {
                param_name = tmp.c_str() + i + 1;
                tmp.resize(i);
                mod_name   = tmp;
                return;
            }
        }
        param_name = tmp;
        mod_name   = "";
    }

    params_ref & get_params(std::string const& mod_name) {
        if (!mod_name[0]) {
            return m_params;
        }
        else {
            params_ref * p = nullptr;
            if (!m_module_params.find(mod_name.c_str(), p)) {
                p = alloc(params_ref);
                m_module_params.insert(cpy(mod_name.c_str()), p);                
            }
            SASSERT(p);
            return *p;
        }
    }

    void throw_unknown_parameter(std::string const& param_name, param_descrs const& d, std::string const& mod_name) {
        if (!mod_name[0]) {
            char const * new_name = get_new_param_name(param_name);
            if (new_name) {
                std::stringstream strm;
                strm << "the parameter '" << param_name
                     << "', invoke 'z3 -p' to obtain the new parameter list, and 'z3 -pp:" << new_name
                     << "' for the full description of the parameter";
                throw exception(strm.str());
            }
            else if (is_old_param_name(param_name)) {
                std::stringstream strm;
                strm << "unknown parameter '" << param_name 
                     << "', this is an old parameter name, invoke 'z3 -p' to obtain the new parameter list";
                throw default_exception(strm.str());
            }
            else {
                std::stringstream strm;
                strm << "unknown parameter '" << param_name << "'\n";    
                strm << "Legal parameters are:\n";
                d.display(strm, 2, false, false);
                throw default_exception(strm.str());
            }
        }
        else {
            std::stringstream strm;
            strm << "unknown parameter '" << param_name << "' ";
            strm << "at module '" << mod_name << "'\n";
            strm << "Legal parameters are:\n";
            d.display(strm, 2, false, false);
            throw default_exception(strm.str());
        }
    }

    void validate_type(std::string& name, char const* value, param_descrs const& d) {
        param_kind k = d.get_kind(name.c_str());
        std::stringstream strm;
        char const* _value = value;
        switch (k) {
        case CPK_UINT:
            for (; *value; ++value) {
                if (!('0' <= *value && *value <= '9')) {
                    strm << "Expected values for parameter " << name 
                         << " is an unsigned integer. It was given argument '" << _value << "'";
                    throw default_exception(strm.str());                    
                }
            }
            break;
        case CPK_DOUBLE:
            for (; *value; ++value) {
                if (!('0' <= *value && *value <= '9') && *value != '.' && *value != '-' && *value != '/') {
                    strm << "Expected values for parameter " << name 
                         << " is a double. It was given argument '" << _value << "'";
                    throw default_exception(strm.str());                                        
                }
            }
            break;

        case CPK_BOOL:
            if (strcmp(value, "true") != 0 && strcmp(value, "false") != 0) {
                strm << "Expected values for parameter " << name 
                     << " are 'true' or 'false'. It was given argument '" << value << "'";
                throw default_exception(strm.str());
            }
            break;
        default:
            break;
        }
    }


    void set(param_descrs const & d, std::string const & _param_name, char const * value, std::string const & mod_name) {
        char const* param_name = _param_name.c_str();
        param_kind k = d.get_kind(param_name);
        params_ref & ps = get_params(mod_name);
        if (k == CPK_INVALID) {
            throw_unknown_parameter(_param_name, d, mod_name);
        }
        else if (k == CPK_UINT) {
            long val = strtol(value, nullptr, 10);
            ps.set_uint(param_name, static_cast<unsigned>(val));
        }
        else if (k == CPK_DOUBLE) {
            char * aux;
            double val = strtod(value, &aux);
            ps.set_double(param_name, val);
        }
        else if (k == CPK_BOOL) {
            if (strcmp(value, "true") == 0) {
                ps.set_bool(param_name, true);
            }
            else if (strcmp(value, "false") == 0) {
                ps.set_bool(param_name, false);
            }
            else {
                std::stringstream strm;
                strm << "invalid value '" << value << "' for Boolean parameter '" << param_name << "'";                
                if (mod_name[0]) {
                    strm << " at module '" << mod_name << "'";
                }
                throw default_exception(strm.str());
            }
        }
        else if (k == CPK_SYMBOL) {
            ps.set_sym(param_name, symbol(value));
        }
        else if (k == CPK_STRING) {
            // There is no guarantee that (external) callers will not delete value after invoking gparams::set.
            // the value is copied to internal region.
            ps.set_str(param_name, cpy(value));
        }
        else {
            std::stringstream strm;
            strm << "unsupported parameter type '" << param_name << "'";            
            if (mod_name[0]) {
                strm << " at module '" << mod_name << "'";            
            }
            throw exception(strm.str());
        }
    }

    void set(char const * name, char const * value) {
        std::string m, p;
        normalize(name, m, p);
        lock_guard lock(*gparams_mux);
        if (!m[0]) {
            validate_type(p, value, get_param_descrs());
            set(get_param_descrs(), p, value, m);
        }
        else {
            param_descrs * d;
            if (get_module_param_descr(m, d)) {
                validate_type(p, value, *d);
                set(*d, p, value, m);
            }
            else {
                std::stringstream strm;
                strm << "invalid parameter, unknown module '" << m << "'";
                throw exception(strm.str());
            }
        }
    }

    std::string get_value(params_ref const & ps, std::string const & p) {
        symbol sp(p.c_str());
        std::ostringstream buffer;
        ps.display(buffer, sp);
        return buffer.str();
    }

    std::string get_default(param_descrs const & d, std::string const & p, std::string const & m) {
        symbol sp(p.c_str());
        if (!d.contains(sp)) {
            throw_unknown_parameter(p, d, m);
        }
        char const * r = d.get_default(sp);
        if (r == nullptr)
            return "default";
        return r;
    }

    std::string get_value(char const * name) {
        std::string m, p;
        normalize(name, m, p);
        lock_guard lock(*gparams_mux);
        symbol sp(p.c_str());
        if (!m[0]) {
            if (m_params.contains(sp)) {
                return get_value(m_params, p);
            }
            else {
                return get_default(get_param_descrs(), p, m);
            }
        }
        else {
            params_ref * ps = nullptr;
            if (m_module_params.find(m.c_str(), ps) && ps->contains(sp)) {
                return get_value(*ps, p);
            }
            else {
                param_descrs * d;
                if (get_module_param_descr(m, d)) {
                    return get_default(*d, p, m);
                }
            }
        }
        std::stringstream strm;
        strm << "unknown module '" << m << "'";
        throw exception(strm.str());
    }

    // unfortunately, params_ref is not thread safe
    // so better create a local copy of the parameters.
    params_ref get_module(char const* module_name) {
        params_ref result;
        params_ref * ps = nullptr;
        {
            lock_guard lock(*gparams_mux);
            if (m_module_params.find(module_name, ps)) {
                result.copy(*ps);
            }
        }
        return result;
    }
    
    params_ref const& get_ref() { 
        return m_params;
    }

    // -----------------------------------------------
    //
    // Pretty printing
    //
    // -----------------------------------------------

    void display(std::ostream & out, unsigned indent, bool smt2_style, bool include_descr) {
        lock_guard lock(*gparams_mux);
        out << "Global parameters\n";
        get_param_descrs().display(out, indent + 4, smt2_style, include_descr);
        out << "\n";
        if (!smt2_style) {
            out << "To set a module parameter, use <module-name>.<parameter-name>=value\n";
            out << "Example:  pp.decimal=true\n";
            out << "\n";
        }
        for (auto & kv : get_module_param_descrs()) {
            out << "[module] " << kv.m_key;
            char const * descr = nullptr;
            if (get_module_descrs().find(kv.m_key, descr)) {
                out << ", description: " << descr;
            }
            out << "\n";
            auto* d = kv.m_value->deref();
            d->display(out, indent + 4, smt2_style, include_descr);
        }
    }

    void display_modules(std::ostream & out) {
        lock_guard lock(*gparams_mux);
        for (auto & kv : get_module_param_descrs()) {
            out << "[module] " << kv.m_key;
            char const * descr = nullptr;
            if (get_module_descrs().find(kv.m_key, descr)) {
                out << ", description: " << descr;
            }
            out << "\n";
        }
    }

    void display_module(std::ostream & out, char const* module_name) {
        lock_guard lock(*gparams_mux);
        param_descrs * d = nullptr;
        if (!get_module_param_descr(module_name, d)) {
            std::stringstream strm;
            strm << "unknown module '" << module_name << "'";                    
            throw exception(strm.str());
        }
        out << "[module] " << module_name;
        char const * descr = nullptr;
        if (get_module_descrs().find(module_name, descr)) {
            out << ", description: " << descr;
        }
        out << "\n";
        d->display(out, 4, false);
    }

    void display_parameter(std::ostream & out, char const * name) {        
        std::string m, p;
        normalize(name, m, p);
        symbol sp(p.c_str());
        lock_guard lock(*gparams_mux);
        out << name << " " << m << " " << p << "\n";
        param_descrs * d;
        if (!m[0]) {
            d = &get_param_descrs();
        }
        else {
            if (!get_module_param_descr(m, d)) {
                std::stringstream strm;
                strm << "unknown module '" << m << "'";                    
                throw exception(strm.str());
            }
        }
        if (!d->contains(sp))
            throw_unknown_parameter(p, *d, m);
        out << "  name:           " << p << "\n";
        if (m[0]) {
            out << "  module:         " << m << "\n";
            out << "  qualified name: " << m << "." << p << "\n";
        }
        out << "  type:           " << d->get_kind(sp) << "\n";
        out << "  description:    " << d->get_descr(sp) << "\n";
        out << "  default value:  " << d->get_default(sp) << "\n";
    }
};

gparams::imp * gparams::g_imp = nullptr;

void gparams::reset() {
    SASSERT(g_imp);
    g_imp->reset();
}

void gparams::set(char const * name, char const * value) {
    TRACE("gparams", tout << "setting [" << name << "] <- '" << value << "'\n";);
    SASSERT(g_imp);
    g_imp->set(name, value);
}

void gparams::set(symbol const & name, char const * value) {
    SASSERT(g_imp);
    g_imp->set(name.bare_str(), value);
}

std::string gparams::get_value(char const * name) {
    SASSERT(g_imp);
    return g_imp->get_value(name);
}

std::string gparams::get_value(symbol const & name) {
    SASSERT(g_imp);
    return g_imp->get_value(name.bare_str());
}

void gparams::register_global(param_descrs & d) {
    SASSERT(g_imp);
    g_imp->register_global(d);
}

void gparams::register_module(char const * module_name, lazy_descrs_t& f) {
    SASSERT(g_imp);
    g_imp->register_module(module_name, f);
}

void gparams::register_module_descr(char const * module_name, char const * descr) {
    SASSERT(g_imp);
    g_imp->register_module_descr(module_name, descr);
}

params_ref gparams::get_module(char const * module_name) {
    SASSERT(g_imp);
    return g_imp->get_module(module_name);
}


params_ref const& gparams::get_ref() {
    TRACE("gparams", tout << "gparams::get_ref()\n";);
    SASSERT(g_imp);
    return g_imp->get_ref();
}

void gparams::display(std::ostream & out, unsigned indent, bool smt2_style, bool include_descr) {
    SASSERT(g_imp);
    g_imp->display(out, indent, smt2_style, include_descr);
}

void gparams::display_modules(std::ostream & out) {
    SASSERT(g_imp);
    g_imp->display_modules(out);
}

void gparams::display_module(std::ostream & out, char const * module_name) {
    SASSERT(g_imp);
    g_imp->display_module(out, module_name);
}

void gparams::display_parameter(std::ostream & out, char const * name) {
    SASSERT(g_imp);
    g_imp->display_parameter(out, name);
}

void gparams::init() {
    TRACE("gparams", tout << "gparams::init()\n";);
    ALLOC_MUTEX(gparams_mux);
    g_imp = alloc(imp);
}

void gparams::finalize() {
    TRACE("gparams", tout << "gparams::finalize()\n";);
    dealloc(g_imp);
    DEALLOC_MUTEX(gparams_mux);
}

std::string& gparams::g_buffer() {
    SASSERT(g_imp);
    return g_imp->m_buffer;
}
