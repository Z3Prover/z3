/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cmd_context.cpp

Abstract:
    Command context.

Author:

    Leonardo (leonardo) 2011-03-01

Notes:

--*/
#include<signal.h>
#include"tptr.h"
#include"cmd_context.h"
#include"func_decl_dependencies.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"array_decl_plugin.h"
#include"datatype_decl_plugin.h"
#include"seq_decl_plugin.h"
#include"pb_decl_plugin.h"
#include"fpa_decl_plugin.h"
#include"ast_pp.h"
#include"var_subst.h"
#include"pp.h"
#include"ast_smt2_pp.h"
#include"basic_cmds.h"
#include"cancel_eh.h"
#include"scoped_ctrl_c.h"
#include"dec_ref_util.h"
#include"decl_collector.h"
#include"well_sorted.h"
#include"model_evaluator.h"
#include"for_each_expr.h"
#include"scoped_timer.h"
#include"interpolant_cmds.h"
#include"model_smt2_pp.h"

func_decls::func_decls(ast_manager & m, func_decl * f):
    m_decls(TAG(func_decl*, f, 0)) {
    m.inc_ref(f);
}

void func_decls::finalize(ast_manager & m) {
    TRACE("cmd_context_detail", tout << "finalizing func_decls...\n";);
    if (GET_TAG(m_decls) == 0) {
        m.dec_ref(UNTAG(func_decl *, m_decls));
    }
    else {
        TRACE("func_decls", tout << "finalize...\n";);
        func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
        func_decl_set::iterator it  = fs->begin();
        func_decl_set::iterator end = fs->end();
        for (; it != end; ++it) {
            TRACE("func_decls", tout << "dec_ref of " << (*it)->get_name() << " ref_count: " << (*it)->get_ref_count() << "\n";);
            m.dec_ref(*it);
        }
        dealloc(fs);
    }
    m_decls = 0;
}

bool func_decls::contains(func_decl * f) const {
    if (GET_TAG(m_decls) == 0) {
        return UNTAG(func_decl*, m_decls) == f;
    }
    else {
        func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
        return fs->contains(f);
    }
}

bool func_decls::insert(ast_manager & m, func_decl * f) {
    if (contains(f))
        return false;
    m.inc_ref(f);
    if (m_decls == 0) {
        m_decls = TAG(func_decl*, f, 0);
    }
    else if (GET_TAG(m_decls) == 0) {
        func_decl_set * new_fs = alloc(func_decl_set);
        new_fs->insert(UNTAG(func_decl*, m_decls));
        new_fs->insert(f);
        m_decls = TAG(func_decl*, new_fs, 1);
    }
    else {
        func_decl_set * fs = UNTAG(func_decl_set*, m_decls);
        fs->insert(f);
    }
    return true;
}

void func_decls::erase(ast_manager & m, func_decl * f) {
    if (!contains(f))
        return;
    if (GET_TAG(m_decls) == 0) {
        m.dec_ref(f);
        m_decls = 0;
    }
    else {
        func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
        fs->erase(f);
        m.dec_ref(f);
        if (fs->empty()) {
            dealloc(fs);
            m_decls = 0;
        }
    }
}

/**
   \brief Return true if func_decls contains a declaration different from f, but with the same domain.
*/
bool func_decls::clash(func_decl * f) const {
    if (m_decls == 0)
        return false;
    if (GET_TAG(m_decls) == 0)
        return false;
    func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
    func_decl_set::iterator it  = fs->begin();
    func_decl_set::iterator end = fs->end();
    for (; it != end; ++it) {
        func_decl * g = *it;
        if (g == f)
            continue;
        if (g->get_arity() != f->get_arity()) 
            continue;
        unsigned num = g->get_arity();
        unsigned i;
        for (i = 0; i < num; i++) 
            if (g->get_domain(i) != f->get_domain(i))
                break;
        if (i == num)
            return true;
    }
    return false;
}

bool func_decls::more_than_one() const {
    if (m_decls == 0 || GET_TAG(m_decls) == 0)
        return false;
    func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
    return fs->size() > 1;
}

func_decl * func_decls::first() const {
    if (m_decls == 0)
        return 0;
    if (GET_TAG(m_decls) == 0)
        return UNTAG(func_decl*, m_decls);
    func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
    SASSERT(!fs->empty());
    return *(fs->begin());
}

func_decl * func_decls::find(unsigned arity, sort * const * domain, sort * range) const {
    if (!more_than_one())
        return first();
    func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
    func_decl_set::iterator it  = fs->begin();
    func_decl_set::iterator end = fs->end();
    for (; it != end; it++) {
        func_decl * f = *it;
        if (range != 0 && f->get_range() != range)
            continue;
        if (f->get_arity() != arity)
            continue;
        unsigned i = 0;
        for (i = 0; i < arity; i++) {
            if (f->get_domain(i) != domain[i])
                break;
        }
        if (i == arity)
            return f;
    }
    return 0;
}

func_decl * func_decls::find(ast_manager & m, unsigned num_args, expr * const * args, sort * range) const {
    if (!more_than_one())
        first();
    ptr_buffer<sort> sorts;
    for (unsigned i = 0; i < num_args; i++)
        sorts.push_back(m.get_sort(args[i]));
    return find(num_args, sorts.c_ptr(), range);
}

ast_object_ref::ast_object_ref(cmd_context & ctx, ast * a):m_ast(a) {
    ctx.m().inc_ref(a);
}

void ast_object_ref::finalize(cmd_context & ctx) {
    ctx.m().dec_ref(m_ast);
}

void stream_ref::set(char const * name) {
    if (!name) {
        throw cmd_exception("invalid stream name");
    }
    reset();
    SASSERT(!m_owner);
    if (strcmp(name, "stdout") == 0) {
        m_name   = "stdout";
        m_stream = &std::cout;
    }
    else if (strcmp(name, "stderr") == 0) {
        m_name   = "stderr";
        m_stream = &std::cerr;
    }
    else {
        m_stream = alloc(std::ofstream, name, std::ios_base::app);
        m_name   = name;
        m_owner = true;
        if (m_stream->bad() || m_stream->fail()) {
            reset();
            std::string msg = "failed to set output stream '";
            msg += name;
            msg += "'";
            throw cmd_exception(msg);
        }
        SASSERT(m_stream);
    }
}

void stream_ref::reset() {
    if (m_owner)
        dealloc(m_stream);
    m_name   = m_default_name;
    m_stream = &m_default;
    m_owner  = false;
}

class cmd_context::pp_env : public smt2_pp_environment {
protected:
    cmd_context & m_owner;
    arith_util    m_autil;
    bv_util       m_bvutil;
    array_util    m_arutil;
    fpa_util      m_futil;
    datalog::dl_decl_util m_dlutil;

    format_ns::format * pp_fdecl_name(symbol const & s, func_decls const & fs, func_decl * f, unsigned & len) {
        format_ns::format * f_name = smt2_pp_environment::pp_fdecl_name(s, len);
        if (!fs.more_than_one())
            return f_name;
        if (!fs.clash(f))
            return f_name;
        return pp_as(f_name, f->get_range());
    }

    format_ns::format * pp_fdecl_ref_core(symbol const & s, func_decls const & fs, func_decl * f) {
        unsigned len;
        format_ns::format * f_name = smt2_pp_environment::pp_fdecl_name(s, len);
        if (!fs.more_than_one())
            return f_name;
        return pp_signature(f_name, f);
    }

public:
    pp_env(cmd_context & o):m_owner(o), m_autil(o.m()), m_bvutil(o.m()), m_arutil(o.m()), m_futil(o.m()), m_dlutil(o.m()) {}
    virtual ~pp_env() {}
    virtual ast_manager & get_manager() const { return m_owner.m(); }
    virtual arith_util & get_autil() { return m_autil; }
    virtual bv_util & get_bvutil() { return m_bvutil; }
    virtual array_util & get_arutil() { return m_arutil; }
    virtual fpa_util & get_futil() { return m_futil; }
    virtual datalog::dl_decl_util& get_dlutil() { return m_dlutil; }
    virtual bool uses(symbol const & s) const { 
        return 
            m_owner.m_builtin_decls.contains(s) ||
            m_owner.m_func_decls.contains(s);
    }
    virtual format_ns::format * pp_sort(sort * s) { 
        return m_owner.pp(s);
    }
    virtual format_ns::format * pp_fdecl(func_decl * f, unsigned & len) {
        symbol s = f->get_name();
        func_decls fs;
        if (m_owner.m_func_decls.find(s, fs) && fs.contains(f)) {
            return pp_fdecl_name(s, fs, f, len);
        }
        if (m_owner.m_func_decl2alias.find(f, s) && m_owner.m_func_decls.find(s, fs) && fs.contains(f)) {
            return pp_fdecl_name(s, fs, f, len);
        }
        return smt2_pp_environment::pp_fdecl(f, len);
    }
    virtual format_ns::format * pp_fdecl_ref(func_decl * f) {
        symbol s = f->get_name();
        func_decls fs;
        if (m_owner.m_func_decls.find(s, fs) && fs.contains(f)) {
            return pp_fdecl_ref_core(s, fs, f);
        }
        if (m_owner.m_func_decl2alias.find(f, s) && m_owner.m_func_decls.find(s, fs) && fs.contains(f)) {
            return pp_fdecl_ref_core(s, fs, f);
        }
        return smt2_pp_environment::pp_fdecl_ref(f);
    }
};

cmd_context::cmd_context(bool main_ctx, ast_manager * m, symbol const & l):
    m_main_ctx(main_ctx),
    m_logic(l),
    m_interactive_mode(false),
    m_global_decls(false),  
    m_print_success(m_params.m_smtlib2_compliant),
    m_random_seed(0),
    m_produce_unsat_cores(false),
    m_produce_assignments(false),
    m_status(UNKNOWN),
    m_numeral_as_real(false),
    m_ignore_check(false),
    m_exit_on_error(false),
    m_manager(m),   
    m_own_manager(m == 0),
    m_manager_initialized(false),
    m_pmanager(0),
    m_sexpr_manager(0),
    m_regular("stdout", std::cout),
    m_diagnostic("stderr", std::cerr) {
    SASSERT(m != 0 || !has_manager());
    install_basic_cmds(*this);
    install_ext_basic_cmds(*this);
    install_core_tactic_cmds(*this);
    install_interpolant_cmds(*this);
    SASSERT(m != 0 || !has_manager());
    if (m_main_ctx) { 
        set_verbose_stream(diagnostic_stream());
    }
}

cmd_context::~cmd_context() {
    if (m_main_ctx) {
        set_verbose_stream(std::cerr);
    }
    finalize_cmds();
    finalize_tactic_cmds();
    finalize_probes();
    reset(true); 
    m_solver = 0;
    m_check_sat_result = 0;
}

void cmd_context::set_cancel(bool f) {
    if (m_solver) {
        if (f) {
            m_solver->cancel(); 
        }
        else {
            m_solver->reset_cancel();
        }
    }
    if (has_manager())
        m().set_cancel(f);
}

opt_wrapper* cmd_context::get_opt() {
    return m_opt.get();
}

void cmd_context::set_opt(opt_wrapper* opt) {
    m_opt = opt;
    for (unsigned i = 0; i < m_scopes.size(); ++i) {
        m_opt->push();
    }
    m_opt->set_logic(m_logic);
}

void cmd_context::global_params_updated() {
    m_params.updt_params();
    if (m_params.m_smtlib2_compliant)
        m_print_success = true;
    if (m_solver) {
        params_ref p;
        if (!m_params.m_auto_config)
            p.set_bool("auto_config", false);
        m_solver->updt_params(p);
    }
}

void cmd_context::set_produce_models(bool f) {
    if (m_solver)
        m_solver->set_produce_models(f);
    m_params.m_model = f;
}

void cmd_context::set_produce_unsat_cores(bool f) {
    // can only be set before initialization
    SASSERT(!has_manager());
    m_params.m_unsat_core = f;
}

void cmd_context::set_produce_proofs(bool f) {
    // can only be set before initialization
    SASSERT(!has_manager());
    m_params.m_proof = f;
}

void cmd_context::set_produce_interpolants(bool f) {
    // can only be set before initialization
    // FIXME currently synonym for produce_proofs
    // also sets the default solver to be simple smt
    SASSERT(!has_manager());
    m_params.m_proof = f;
    // set_solver_factory(mk_smt_solver_factory());
}

bool cmd_context::produce_models() const { 
    return m_params.m_model;
}

bool cmd_context::produce_proofs() const { 
    return m_params.m_proof;
}

bool cmd_context::produce_interpolants() const { 
    // FIXME currently synonym for produce_proofs
    return m_params.m_proof;
}

bool cmd_context::produce_unsat_cores() const { 
    return m_params.m_unsat_core;
}

bool cmd_context::well_sorted_check_enabled() const {
    return m_params.m_well_sorted_check;
}

bool cmd_context::validate_model_enabled() const {
    return m_params.m_model_validate;
}

cmd_context::check_sat_state cmd_context::cs_state() const {
    if (m_check_sat_result.get() == 0)
        return css_clear;
    switch (m_check_sat_result->status()) {
    case l_true:  return css_sat;
    case l_false: return css_unsat;
    default: return css_unknown;
    }
}

void cmd_context::register_builtin_sorts(decl_plugin * p) {
    svector<builtin_name> names;
    p->get_sort_names(names, m_logic);
    family_id fid = p->get_family_id();
    svector<builtin_name>::const_iterator it  = names.begin();
    svector<builtin_name>::const_iterator end = names.end();
    for (; it != end; ++it) {
        psort_decl * d = pm().mk_psort_builtin_decl((*it).m_name, fid, (*it).m_kind);
        insert(d);
    }
}

void cmd_context::register_builtin_ops(decl_plugin * p) {
    svector<builtin_name> names;
    p->get_op_names(names, m_logic);
    family_id fid = p->get_family_id();
    svector<builtin_name>::const_iterator it  = names.begin();
    svector<builtin_name>::const_iterator end = names.end();
    for (; it != end; ++it) {
        if (m_builtin_decls.contains((*it).m_name)) {
            builtin_decl & d = m_builtin_decls.find((*it).m_name);
            builtin_decl * new_d = alloc(builtin_decl, fid, (*it).m_kind, d.m_next);
            d.m_next = new_d;
            m_extra_builtin_decls.push_back(new_d);
        }
        else {
            m_builtin_decls.insert((*it).m_name, builtin_decl(fid, (*it).m_kind));
        }
    }
}

void cmd_context::register_plugin(symbol const & name, decl_plugin * p, bool install_names) {
    m_manager->register_plugin(name, p);
    if (install_names) {
        register_builtin_sorts(p);
        register_builtin_ops(p);
    }
}

void cmd_context::load_plugin(symbol const & name, bool install, svector<family_id>& fids) {
    family_id id = m_manager->get_family_id(name);
    decl_plugin* p = m_manager->get_plugin(id);
    if (install && p && fids.contains(id)) {
        register_builtin_sorts(p);
        register_builtin_ops(p);
    }
    fids.erase(id);
}

bool cmd_context::logic_has_arith_core(symbol const & s) const {
    return 
        s == "QF_LRA" ||
        s == "QF_LIA" ||
        s == "QF_RDL" ||
        s == "QF_IDL" ||
        s == "QF_AUFLIA" ||
        s == "QF_ALIA" ||
        s == "QF_AUFLIRA" ||
        s == "QF_AUFNIA" ||
        s == "QF_AUFNIRA" ||
        s == "QF_UFLIA" ||
        s == "QF_UFLRA" ||
        s == "QF_UFIDL" ||
        s == "QF_UFRDL" ||
        s == "QF_NIA" ||
        s == "QF_NRA" ||
        s == "QF_NIRA" ||
        s == "QF_UFNRA" ||
        s == "QF_UFNIA" ||
        s == "QF_UFNIRA" ||
        s == "QF_BVRE" ||
        s == "AUFLIA" ||
        s == "AUFLIRA" ||
        s == "AUFNIA" ||
        s == "AUFNIRA" ||
        s == "UFLIA" ||
        s == "UFLRA" ||
        s == "UFNRA" ||
        s == "UFNIRA" ||
        s == "UFNIA" ||
        s == "LIA" ||        
        s == "LRA" || 
        s == "QF_FP" ||
        s == "QF_FPBV" ||
        s == "QF_BVFP" ||
        s == "HORN";
}

bool cmd_context::logic_has_arith() const {
    return !has_logic() || logic_has_arith_core(m_logic);
}

bool cmd_context::logic_has_bv_core(symbol const & s) const {
    return
        s == "UFBV" ||
        s == "AUFBV" ||
        s == "ABV" ||
        s == "BV" ||
        s == "QF_BV" ||
        s == "QF_UFBV" ||
        s == "QF_ABV" ||
        s == "QF_AUFBV" ||
        s == "QF_BVRE" ||
        s == "QF_FPBV" ||
        s == "QF_BVFP" ||
        s == "HORN";
}

bool cmd_context::logic_has_horn(symbol const& s) const {
    return s == "HORN";
}

bool cmd_context::logic_has_bv() const {
    return !has_logic() || logic_has_bv_core(m_logic);
}

bool cmd_context::logic_has_seq_core(symbol const& s) const {
    return s == "QF_BVRE";
}

bool cmd_context::logic_has_seq() const {
    return !has_logic() || logic_has_seq_core(m_logic);        
}

bool cmd_context::logic_has_fpa_core(symbol const& s) const {
    return s == "QF_FP" || s == "QF_FPBV" || s == "QF_BVFP";
}

bool cmd_context::logic_has_fpa() const {
    return !has_logic() || logic_has_fpa_core(m_logic);
}

bool cmd_context::logic_has_array_core(symbol const & s) const {
    return 
        s == "QF_AX" ||
        s == "QF_AUFLIA" ||
        s == "QF_ALIA" ||
        s == "QF_AUFLIRA" ||
        s == "QF_AUFNIA" ||
        s == "QF_AUFNIRA" ||
        s == "AUFLIA" ||
        s == "AUFLIRA" ||
        s == "AUFNIA" ||
        s == "AUFNIRA" ||
        s == "AUFBV" || 
        s == "ABV" || 
        s == "QF_ABV" ||
        s == "QF_AUFBV" ||
        s == "HORN";
}

bool cmd_context::logic_has_array() const {
    return !has_logic() || logic_has_array_core(m_logic);
}

bool cmd_context::logic_has_datatype() const {
    return !has_logic();
}

void cmd_context::init_manager_core(bool new_manager) {
    SASSERT(m_manager != 0);
    SASSERT(m_pmanager != 0);
    m_dt_eh    = alloc(dt_eh, *this);
    m_pmanager->set_new_datatype_eh(m_dt_eh.get());
    if (new_manager) {
        decl_plugin * basic = m_manager->get_plugin(m_manager->get_basic_family_id());
        register_builtin_sorts(basic);
        register_builtin_ops(basic);
        // the manager was created by the command context.
        register_plugin(symbol("arith"),    alloc(arith_decl_plugin), logic_has_arith());
        register_plugin(symbol("bv"),       alloc(bv_decl_plugin), logic_has_bv());
        register_plugin(symbol("array"),    alloc(array_decl_plugin), logic_has_array());
        register_plugin(symbol("datatype"), alloc(datatype_decl_plugin), logic_has_datatype());
        register_plugin(symbol("seq"),      alloc(seq_decl_plugin), logic_has_seq());
        register_plugin(symbol("pb"),     alloc(pb_decl_plugin), !has_logic());
        register_plugin(symbol("fpa"),      alloc(fpa_decl_plugin), logic_has_fpa());
        register_plugin(symbol("datalog_relation"), alloc(datalog::dl_decl_plugin), !has_logic());
    }
    else {
        // the manager was created by an external module
        // we register all plugins available in the manager.
        // unless the logic specifies otherwise.
        svector<family_id> fids;
        m_manager->get_range(fids);
        load_plugin(symbol("arith"),    logic_has_arith(), fids);
        load_plugin(symbol("bv"),       logic_has_bv(), fids);
        load_plugin(symbol("array"),    logic_has_array(), fids);
        load_plugin(symbol("datatype"), logic_has_datatype(), fids);
        load_plugin(symbol("seq"),      logic_has_seq(), fids);
        load_plugin(symbol("fpa"),      logic_has_fpa(), fids);
        
        svector<family_id>::iterator it  = fids.begin();
        svector<family_id>::iterator end = fids.end();
        for (; it != end; ++it) {
            decl_plugin * p = m_manager->get_plugin(*it);
            if (p) {
                register_builtin_sorts(p);
                register_builtin_ops(p);
            }
        }
    }
    if (!has_logic()) {
        // add list type only if the logic is not specified.
        // it prevents clashes with builtin types.
        insert(pm().mk_plist_decl());
    }
    if (m_solver_factory) {
        mk_solver();
    }
    m_check_logic.set_logic(m(), m_logic);
}

void cmd_context::init_manager() {
    if (m_manager_initialized) {
        // no-op
    }
    else if (m_manager) {
        m_manager_initialized = true;
        SASSERT(!m_own_manager);
        init_external_manager();
    }
    else {
        m_manager_initialized = true;
        SASSERT(m_pmanager == 0);
        m_check_sat_result = 0;
        m_manager  = m_params.mk_ast_manager();
        m_pmanager = alloc(pdecl_manager, *m_manager);
        init_manager_core(true);
    }
}

void cmd_context::init_external_manager() {
    SASSERT(m_manager != 0);
    SASSERT(m_pmanager == 0);
    m_pmanager = alloc(pdecl_manager, *m_manager);
    init_manager_core(false);
}

bool cmd_context::supported_logic(symbol const & s) const {
    return s == "QF_UF" || s == "UF" || 
        logic_has_arith_core(s) || logic_has_bv_core(s) || 
        logic_has_array_core(s) || logic_has_seq_core(s) ||
        logic_has_horn(s) || logic_has_fpa_core(s);
}

bool cmd_context::set_logic(symbol const & s) {
    if (has_logic())
        throw cmd_exception("the logic has already been set");
    if (has_manager() && m_main_ctx) 
        throw cmd_exception("logic must be set before initialization");    
    if (!supported_logic(s)) {
        if (m_params.m_smtlib2_compliant) {
            return false; 
        }
        else {
            warning_msg("unknown logic, ignoring set-logic command");
            return true;
        }
    }
    m_logic = s;
    if (is_logic("QF_RDL") ||
        is_logic("QF_LRA") ||
        is_logic("UFLRA") ||
        is_logic("LRA") ||
        is_logic("RDL") ||
        is_logic("QF_NRA") ||
        is_logic("QF_UFNRA") ||
        is_logic("QF_UFLRA"))
        m_numeral_as_real = true;
    return true;
}

std::string cmd_context::reason_unknown() const { 
    if (m_check_sat_result.get() == 0)
        throw cmd_exception("state of the most recent check-sat command is not unknown");
    return m_check_sat_result->reason_unknown(); 
}

bool cmd_context::is_func_decl(symbol const & s) const {
    return m_builtin_decls.contains(s) || m_func_decls.contains(s);
}

void cmd_context::insert(symbol const & s, func_decl * f) {
    m_check_sat_result = 0;
    if (!m_check_logic(f)) {
        throw cmd_exception(m_check_logic.get_last_error());
    }
    if (m_macros.contains(s)) {
        throw cmd_exception("invalid declaration, named expression already defined with this name ", s);
    }
    if (m_builtin_decls.contains(s)) {
        throw cmd_exception("invalid declaration, builtin symbol ", s);
    }
    dictionary<func_decls>::entry * e = m_func_decls.insert_if_not_there2(s, func_decls());
    func_decls & fs = e->get_data().m_value;
    if (!fs.insert(m(), f)) {
        std::string msg = "invalid declaration, ";
        msg += f->get_arity() == 0 ? "constant" : "function";
        msg += " '";
        msg += s.str();
        msg += "' (with the given signature) already declared";
        throw cmd_exception(msg.c_str());
    }
    if (s != f->get_name()) {
        TRACE("func_decl_alias", tout << "adding alias for: " << f->get_name() << ", alias: " << s << "\n";);
        m_func_decl2alias.insert(f, s);
    }
    if (!m_global_decls) {
        m_func_decls_stack.push_back(sf_pair(s, f));
    }
    TRACE("cmd_context", tout << "new function decl\n" << mk_pp(f, m()) << "\n";);
}

void cmd_context::insert(symbol const & s, psort_decl * p) {
    m_check_sat_result = 0;
    if (m_psort_decls.contains(s)) {
        throw cmd_exception("sort already defined ", s);
    }
    pm().inc_ref(p);
    m_psort_decls.insert(s, p);
    if (!m_global_decls) {
        m_psort_decls_stack.push_back(s);
    }
    TRACE("cmd_context", tout << "new sort decl\n"; p->display(tout); tout << "\n";);
}

void cmd_context::insert(symbol const & s, unsigned arity, expr * t) {
    m_check_sat_result = 0;
    if (m_builtin_decls.contains(s)) {
        throw cmd_exception("invalid macro/named expression, builtin symbol ", s);
    }
    if (m_macros.contains(s)) {
        throw cmd_exception("named expression already defined");
    }
    if (m_func_decls.contains(s)) {
        throw cmd_exception("invalid named expression, declaration already defined with this name ", s);
    }
    m().inc_ref(t);
    TRACE("insert_macro", tout << "new macro " << arity << "\n" << mk_pp(t, m()) << "\n";);
    m_macros.insert(s, macro(arity, t));
    if (!m_global_decls) {
        m_macros_stack.push_back(s);
    }
}

void cmd_context::insert(cmd * c) {
    symbol const & s = c->get_name();
    cmd * old_c;
    if (m_cmds.find(s, old_c) && c != old_c) {
        old_c->finalize(*this);
        dealloc(old_c);
    }
    m_cmds.insert(s, c);
}

void cmd_context::insert_user_tactic(symbol const & s, sexpr * d) {
    sm().inc_ref(d);
    sexpr * old_d;
    if (m_user_tactic_decls.find(s, old_d)) {
        sm().dec_ref(old_d);
    }
    m_user_tactic_decls.insert(s, d);
}

void cmd_context::insert(symbol const & s, object_ref * r) {
    r->inc_ref(*this);
    object_ref * old_r = 0;
    if (m_object_refs.find(s, old_r)) {
        old_r->dec_ref(*this);
    }
    m_object_refs.insert(s, r);
}


func_decl * cmd_context::find_func_decl(symbol const & s) const {
    builtin_decl d;
    if (m_builtin_decls.find(s, d)) {
        try {
            // Remark: ignoring m_next of d. We do not allow two different theories to define the same constant name.
            func_decl * f;
            f = m().mk_func_decl(d.m_fid, d.m_decl, 0, 0, 0, static_cast<sort*const*>(0), 0);
            if (f != 0)
                return f;
        }
        catch (ast_exception &) {
        }
        throw cmd_exception("invalid function declaration reference, must provide signature for builtin symbol ", s);
    }
    if (m_macros.contains(s))
        throw cmd_exception("invalid function declaration reference, named expressions (aka macros) cannot be referenced ", s);
    func_decls fs;
    if (m_func_decls.find(s, fs)) {
        if (fs.more_than_one())
            throw cmd_exception("ambiguous function declaration reference, provide full signature to disumbiguate (<symbol> (<sort>*) <sort>) ", s);
        return fs.first();
    }
    throw cmd_exception("invalid function declaration reference, unknown function ", s);
    return 0;
}

/**
   \brief Select a builtin_decl from the list starting at first.
   We select the decl d s.t. d->m_fid == target_id
   If there is none that satisfies this condition, we return first.

   This is a HACK for supporting arithmetic and floating-point arithmetic.
   These are two different theories in Z3, but they share builtin symbol names: +, -, *, /, <, <=, >, >=
*/
static builtin_decl const & peek_builtin_decl(builtin_decl const & first, family_id target_id) {
    builtin_decl const * curr = &first;
    while (curr != 0) {
        if (curr->m_fid == target_id)
            return *curr;
        curr = curr->m_next;
    }
    return first;
}

func_decl * cmd_context::find_func_decl(symbol const & s, unsigned num_indices, unsigned const * indices, 
                                        unsigned arity, sort * const * domain, sort * range) const {
    builtin_decl d;
    if (m_builtin_decls.find(s, d)) {
        family_id fid = d.m_fid;
        decl_kind k   = d.m_decl;
        // Hack: if d.m_next != 0, we use domain[0] (if available) to decide which plugin we use.
        if (d.m_decl != 0 && arity > 0) {
            builtin_decl const & d2 = peek_builtin_decl(d, domain[0]->get_family_id());
            fid = d2.m_fid;
            k   = d2.m_decl;
        }
        func_decl * f;
        if (num_indices == 0) {
            f = m().mk_func_decl(fid, k, 0, 0, arity, domain, range);
        }
        else {
            buffer<parameter> ps;
            for (unsigned i = 0; i < num_indices; i++)
                ps.push_back(parameter(indices[i]));
            f = m().mk_func_decl(fid, k, num_indices, ps.c_ptr(), arity, domain, range);
        }
        if (f == 0)
            throw cmd_exception("invalid function declaration reference, invalid builtin reference ", s);
        return f;
    }
    
    if (m_macros.contains(s))
        throw cmd_exception("invalid function declaration reference, named expressions (aka macros) cannot be referenced ", s);

    if (num_indices > 0)
        throw cmd_exception("invalid indexed function declaration reference, unknown builtin function ", s);

    func_decl * f = 0;
    func_decls fs;
    if (m_func_decls.find(s, fs)) {
        f = fs.find(arity, domain, range);
    }
    if (f == 0)
        throw cmd_exception("invalid function declaration reference, unknown function ", s);
    return f;
}
 
psort_decl * cmd_context::find_psort_decl(symbol const & s) const {
    psort_decl * p = 0;
    m_psort_decls.find(s, p);
    return p;
}

cmd_context::macro cmd_context::find_macro(symbol const & s) const {
    macro m;
    m_macros.find(s, m);
    return m;
}

cmd * cmd_context::find_cmd(symbol const & s) const {
    cmd * c = 0;
    m_cmds.find(s, c);
    return c;
}

sexpr * cmd_context::find_user_tactic(symbol const & s) const {
    sexpr * n = 0;
    m_user_tactic_decls.find(s, n);
    return n;
}

object_ref * cmd_context::find_object_ref(symbol const & s) const {
    object_ref * r = 0;
    m_object_refs.find(s, r);
    if (r == 0) throw cmd_exception("unknown global variable ", s);
    return r;
}

#define CHECK_SORT(T) if (well_sorted_check_enabled()) m().check_sorts_core(T)

void cmd_context::mk_const(symbol const & s, expr_ref & result) const {
    mk_app(s, 0, 0, 0, 0, 0, result);
}

void cmd_context::mk_app(symbol const & s, unsigned num_args, expr * const * args, unsigned num_indices, parameter const * indices, sort * range,
                         expr_ref & result) const {
    builtin_decl d;
    if (m_builtin_decls.find(s, d)) {
        family_id fid = d.m_fid;
        decl_kind k   = d.m_decl;
        // Hack: if d.m_next != 0, we use the sort of args[0] (if available) to decide which plugin we use.
        if (d.m_decl != 0 && num_args > 0) {
            builtin_decl const & d2 = peek_builtin_decl(d, m().get_sort(args[0])->get_family_id());
            fid = d2.m_fid;
            k   = d2.m_decl;
        }
        if (num_indices == 0) {
            result = m().mk_app(fid, k, 0, 0, num_args, args, range);
        }
        else {
            result = m().mk_app(fid, k, num_indices, indices, num_args, args, range);
        }
        if (result.get() == 0)
            throw cmd_exception("invalid builtin application ", s);
        CHECK_SORT(result.get());
        return;
    }
    if (num_indices > 0)
        throw cmd_exception("invalid use of indexed indentifier, unknown builtin function ", s);
    macro _m;
    if (m_macros.find(s, _m)) {
        if (num_args != _m.first)
            throw cmd_exception("invalid defined function application, incorrect number of arguments ", s);
        if (num_args == 0) {
            result = _m.second;
            return;
        }
        SASSERT(num_args > 0);
        TRACE("macro_bug", tout << "well_sorted_check_enabled(): " << well_sorted_check_enabled() << "\n";
              tout << "s: " << s << "\n";
              tout << "body:\n" << mk_ismt2_pp(_m.second, m()) << "\n";
              tout << "args:\n"; for (unsigned i = 0; i < num_args; i++) tout << mk_ismt2_pp(args[i], m()) << "\n" << mk_pp(m().get_sort(args[i]), m()) << "\n";);
        var_subst subst(m());
        subst(_m.second, num_args, args, result);
        if (well_sorted_check_enabled() && !is_well_sorted(m(), result))
            throw cmd_exception("invalid macro application, sort mismatch ", s);
        return;
    }

    func_decls fs;
    if (!m_func_decls.find(s, fs)) {
        if (num_args == 0) {
            throw cmd_exception("unknown constant ", s);
        }
        else
            throw cmd_exception("unknown function/constant ", s);
    }

    if (num_args == 0 && range == 0) {
        if (fs.more_than_one())
            throw cmd_exception("ambiguous constant reference, more than one constant with the same sort, use a qualified expression (as <symbol> <sort>) to disumbiguate ", s);
        func_decl * f = fs.first();
        if (f == 0)
            throw cmd_exception("unknown constant ", s);
        if (f->get_arity() != 0)
            throw cmd_exception("invalid function application, missing arguments ", s);
        result = m().mk_const(f);
        return;
    }
    else {
        func_decl * f = fs.find(m(), num_args, args, range);
        if (f == 0)
            throw cmd_exception("unknown constant ", s);
        if (well_sorted_check_enabled())
            m().check_sort(f, num_args, args);
        result = m().mk_app(f, num_args, args);
        return;
    }
}

void cmd_context::erase_func_decl(symbol const & s) {
    if (!global_decls()) {
        throw cmd_exception("function declarations can only be erased when global declarations (instead of scoped) are used");
    }
    func_decls fs;
    m_func_decls.find(s, fs);
    while (!fs.empty()) {
        func_decl * f = fs.first();
        if (s != f->get_name()) {
            SASSERT(m_func_decl2alias.contains(f));
            m_func_decl2alias.erase(f);
        }
        fs.erase(m(), f);
    }
    fs.finalize(m());
    m_func_decls.erase(s);
}

void cmd_context::erase_func_decl_core(symbol const & s, func_decl * f) {
    func_decls fs;
    m_func_decls.find(s, fs);
    if (fs.contains(f)) {
        if (s != f->get_name()) {
            SASSERT(m_func_decl2alias.contains(f));
            m_func_decl2alias.erase(f);
        }
        fs.erase(m(), f);
        if (fs.empty())
            m_func_decls.erase(s);
    }
}

void cmd_context::erase_func_decl(symbol const & s, func_decl * f) {
    if (!global_decls()) {
        throw cmd_exception("function declarations can only be erased when global (instead of scoped) declarations are used");
    }
    erase_func_decl_core(s, f);
}

void cmd_context::erase_psort_decl_core(symbol const & s) {
    psort_decl * p;
    if (m_psort_decls.find(s, p)) {
        pm().dec_ref(p);
        m_psort_decls.erase(s);
    }
}

void cmd_context::erase_psort_decl(symbol const & s) {
    if (!global_decls()) {
        throw cmd_exception("sort declarations can only be erased when global (instead of scoped) declarations are used");
    }
    erase_psort_decl_core(s);
}

void cmd_context::erase_macro_core(symbol const & s) {
    macro _m;
    if (m_macros.find(s, _m)) {
        m().dec_ref(_m.second);
        m_macros.erase(s);
    }
}

void cmd_context::erase_macro(symbol const & s) {
    if (!global_decls()) {
        throw cmd_exception("macros (aka named expressions) can only be erased when global (instead of scoped) declarations are used");
    }
    erase_macro_core(s);
}

void cmd_context::erase_cmd(symbol const & s) {
    cmd * c;
    if (m_cmds.find(s, c)) {
        c->finalize(*this);
        m_cmds.erase(s);
        dealloc(c);
    }
}

void cmd_context::erase_user_tactic(symbol const & s) {
    sexpr * d;
    if (m_user_tactic_decls.find(s, d)) {
        m_user_tactic_decls.erase(s);
        sm().dec_ref(d);
    }
}

void cmd_context::erase_object_ref(symbol const & s) {
    object_ref * r = 0;
    if (m_object_refs.find(s, r)) {
        r->dec_ref(*this);
        m_object_refs.erase(s);
    }
}

void cmd_context::reset_func_decls() {
    dictionary<func_decls>::iterator  it  = m_func_decls.begin();
    dictionary<func_decls>::iterator  end = m_func_decls.end();
    for (; it != end; ++it) {
        func_decls fs = (*it).m_value;
        fs.finalize(m());
    }
    m_func_decls.reset();
    m_func_decls_stack.reset();
    m_func_decl2alias.reset();
}

void cmd_context::reset_psort_decls() {
    dictionary<psort_decl*>::iterator  it  = m_psort_decls.begin();
    dictionary<psort_decl*>::iterator  end = m_psort_decls.end();
    for (; it != end; ++it) {
        psort_decl * p = (*it).m_value;
        pm().dec_ref(p);
    }
    m_psort_decls.reset();
    m_psort_decls_stack.reset();
}

void cmd_context::reset_macros() {
    dictionary<macro>::iterator  it  = m_macros.begin();
    dictionary<macro>::iterator  end = m_macros.end();
    for (; it != end; ++it) {
        expr * t = (*it).m_value.second;
        m().dec_ref(t);
    }
    m_macros.reset();
    m_macros_stack.reset();
}

void cmd_context::reset_cmds() {
    dictionary<cmd*>::iterator  it  = m_cmds.begin();
    dictionary<cmd*>::iterator  end = m_cmds.end();
    for (; it != end; ++it) {
        cmd * c = (*it).m_value;
        c->reset(*this);
    }
}

void cmd_context::finalize_cmds() {
    dictionary<cmd*>::iterator  it  = m_cmds.begin();
    dictionary<cmd*>::iterator  end = m_cmds.end();
    for (; it != end; ++it) {
        cmd * c = (*it).m_value;
        c->finalize(*this);
        dealloc(c);
    }
    m_cmds.reset();
}

void cmd_context::reset_user_tactics() {
    dec_ref_values(sm(), m_user_tactic_decls);
    m_user_tactic_decls.reset();
}

void cmd_context::reset_object_refs() {
    dictionary<object_ref*>::iterator it  = m_object_refs.begin();
    dictionary<object_ref*>::iterator end = m_object_refs.end();
    for (; it != end; ++it) {
        object_ref * r = (*it).m_value;
        r->dec_ref(*this);
    }
    m_object_refs.reset();
}

void cmd_context::insert_aux_pdecl(pdecl * p) {
    pm().inc_ref(p);
    m_aux_pdecls.push_back(p);
}

void cmd_context::reset(bool finalize) {
    m_logic = symbol::null;
    m_check_sat_result = 0;
    m_numeral_as_real = false;
    m_builtin_decls.reset();
    m_extra_builtin_decls.reset();
    m_check_logic.reset();
    reset_object_refs();
    reset_cmds();
    reset_psort_decls();
    restore_aux_pdecls(0);
    reset_macros();
    reset_func_decls();
    restore_assertions(0);
    if (m_solver)
        m_solver = 0;
    m_scopes.reset();
    m_opt = 0;
    m_pp_env = 0;
    m_dt_eh  = 0;
    if (m_manager) {
        dealloc(m_pmanager);
        m_pmanager = 0;
        if (m_own_manager) {
            dealloc(m_manager);
            m_manager = 0;
            m_manager_initialized = false;
        }
        else {
            // doesn't own manager... so it cannot be deleted
            // reinit cmd_context if this is not a finalization step
            if (!finalize)
                init_external_manager();
            else 
                m_manager_initialized = false;
        }
    }
    if (m_sexpr_manager) {
        dealloc(m_sexpr_manager);
        m_sexpr_manager = 0;
    }
    SASSERT(!m_own_manager || !has_manager());
}

void cmd_context::assert_expr(expr * t) {
    if (!m_check_logic(t))
        throw cmd_exception(m_check_logic.get_last_error());
    m_check_sat_result = 0;
    m().inc_ref(t);
    m_assertions.push_back(t);
    if (produce_unsat_cores())
        m_assertion_names.push_back(0);
    if (m_solver)
        m_solver->assert_expr(t);
}

void cmd_context::assert_expr(symbol const & name, expr * t) {
    if (!m_check_logic(t))
        throw cmd_exception(m_check_logic.get_last_error());
    if (!produce_unsat_cores() || name == symbol::null) {
        assert_expr(t);
        return;
    }
    m_check_sat_result = 0;
    m().inc_ref(t);
    m_assertions.push_back(t);
    expr * ans  = m().mk_const(name, m().mk_bool_sort());
    m().inc_ref(ans);
    m_assertion_names.push_back(ans);
    if (m_solver)
        m_solver->assert_expr(t, ans);
}

void cmd_context::push() {
    m_check_sat_result = 0;
    init_manager();
    m_scopes.push_back(scope());
    scope & s = m_scopes.back();
    s.m_func_decls_stack_lim   = m_func_decls_stack.size();
    s.m_psort_decls_stack_lim  = m_psort_decls_stack.size();
    s.m_macros_stack_lim       = m_macros_stack.size();
    s.m_aux_pdecls_lim         = m_aux_pdecls.size();
    s.m_assertions_lim         = m_assertions.size();
    if (m_solver) 
        m_solver->push();
    if (m_opt) 
        m_opt->push();
}

void cmd_context::push(unsigned n) {
    for (unsigned i = 0; i < n; i++) 
        push();
}

void cmd_context::restore_func_decls(unsigned old_sz) {
    SASSERT(old_sz <= m_func_decls_stack.size());
    svector<sf_pair>::iterator it  = m_func_decls_stack.begin() + old_sz;
    svector<sf_pair>::iterator end = m_func_decls_stack.end();
    for (; it != end; ++it) {
        sf_pair const & p = *it;
        erase_func_decl_core(p.first, p.second);
    }
    m_func_decls_stack.shrink(old_sz);
}

void cmd_context::restore_psort_decls(unsigned old_sz) {
    SASSERT(old_sz <= m_psort_decls_stack.size());
    svector<symbol>::iterator it  = m_psort_decls_stack.begin() + old_sz;
    svector<symbol>::iterator end = m_psort_decls_stack.end();
    for (; it != end; ++it) {
        symbol const & s = *it;
        psort_decl * d = 0;
        if (!m_psort_decls.find(s, d)) {
            UNREACHABLE();
        }
        pm().dec_ref(d);
        m_psort_decls.erase(s);
    }
    m_psort_decls_stack.shrink(old_sz);
}

void cmd_context::restore_macros(unsigned old_sz) {
    SASSERT(old_sz <= m_macros_stack.size());
    svector<symbol>::iterator it  = m_macros_stack.begin() + old_sz;
    svector<symbol>::iterator end = m_macros_stack.end();
    for (; it != end; ++it) {
        symbol const & s = *it;
        macro _m;
        if (!m_macros.find(s, _m)) {
            UNREACHABLE();
        }
        m().dec_ref(_m.second);
        m_macros.erase(s);
    }
    m_macros_stack.shrink(old_sz);
}

void cmd_context::restore_aux_pdecls(unsigned old_sz) {
    SASSERT(old_sz <= m_aux_pdecls.size());
    ptr_vector<pdecl>::iterator it  = m_aux_pdecls.begin() + old_sz;
    ptr_vector<pdecl>::iterator end = m_aux_pdecls.end();
    for (; it != end; ++it) {
        pm().dec_ref(*it);
    }
    m_aux_pdecls.shrink(old_sz);
}

static void restore(ast_manager & m, ptr_vector<expr> & c, unsigned old_sz) {
    ptr_vector<expr>::iterator it  = c.begin() + old_sz;
    ptr_vector<expr>::iterator end = c.end();
    for (; it != end; ++it) {
        m.dec_ref(*it);
    }
    c.shrink(old_sz);
}

void cmd_context::restore_assertions(unsigned old_sz) {
    if (!has_manager()) {
        // restore_assertions invokes m(), so if cmd_context does not have a manager, it will try to create one.
        SASSERT(old_sz == m_assertions.size());
        SASSERT(m_assertions.empty());
        return;
    }
    SASSERT(old_sz <= m_assertions.size());
    SASSERT(!m_interactive_mode || m_assertions.size() == m_assertion_strings.size());
    restore(m(), m_assertions, old_sz);
    if (produce_unsat_cores())
        restore(m(), m_assertion_names, old_sz);
    if (m_interactive_mode)
        m_assertion_strings.shrink(old_sz);
}

void cmd_context::pop(unsigned n) {
    m_check_sat_result = 0;
    if (n == 0)
        return;
    unsigned lvl     = m_scopes.size();
    if (n > lvl)
        throw cmd_exception("invalid pop command, argument is greater than the current stack depth");
    if (m_solver) {
        m_solver->pop(n);
    }
    if (m_opt) 
        m_opt->pop(n);
    unsigned new_lvl = lvl - n;
    scope & s        = m_scopes[new_lvl];
    restore_func_decls(s.m_func_decls_stack_lim);
    restore_psort_decls(s.m_psort_decls_stack_lim);
    restore_macros(s.m_macros_stack_lim);
    restore_aux_pdecls(s.m_aux_pdecls_lim);
    restore_assertions(s.m_assertions_lim);
    m_scopes.shrink(new_lvl);
}

void cmd_context::check_sat(unsigned num_assumptions, expr * const * assumptions) {
    if (m_ignore_check)
        return;
    IF_VERBOSE(100, verbose_stream() << "(started \"check-sat\")" << std::endl;);
    TRACE("before_check_sat", dump_assertions(tout););
    init_manager();
    unsigned timeout = m_params.m_timeout;
    scoped_watch sw(*this);
    lbool r;

    if (m_opt && !m_opt->empty()) {
        bool was_pareto = false;
        m_check_sat_result = get_opt();
        cancel_eh<opt_wrapper> eh(*get_opt());
        scoped_ctrl_c ctrlc(eh);
        scoped_timer timer(timeout, &eh);
        ptr_vector<expr> cnstr(m_assertions);
        cnstr.append(num_assumptions, assumptions);
        get_opt()->set_hard_constraints(cnstr);
        try {
            r = get_opt()->optimize();
            while (r == l_true && get_opt()->is_pareto()) {
                was_pareto = true;
                get_opt()->display_assignment(regular_stream());
                regular_stream() << "\n";
                if (get_opt()->print_model()) {
                    model_ref mdl;
                    get_opt()->get_model(mdl);
                    if (mdl) {
                        regular_stream() << "(model " << std::endl;
                        model_smt2_pp(regular_stream(), *this, *(mdl.get()), 2);
                        regular_stream() << ")" << std::endl;                    
                    }
                }
                r = get_opt()->optimize();
            }
        }
        catch (z3_error & ex) {
            throw ex;
        }
        catch (z3_exception & ex) {
            throw cmd_exception(ex.msg());
        }
        if (was_pareto && r == l_false) {
            r = l_true;
        }
        get_opt()->set_status(r);
        if (r != l_false && !was_pareto) {
            get_opt()->display_assignment(regular_stream());
        }
    }
    else if (m_solver) {
        m_check_sat_result = m_solver.get(); // solver itself stores the result.
        m_solver->set_progress_callback(this);
        cancel_eh<solver> eh(*m_solver);
        scoped_ctrl_c ctrlc(eh);
        scoped_timer timer(timeout, &eh);
        try {
            r = m_solver->check_sat(num_assumptions, assumptions);
        }
        catch (z3_error & ex) {
            throw ex;
        }
        catch (z3_exception & ex) {
            throw cmd_exception(ex.msg());
        }
        m_solver->set_status(r);
    }
    else {
        // There is no solver installed in the command context.
        regular_stream() << "unknown" << std::endl;
        return;
    }
    display_sat_result(r);
    validate_check_sat_result(r);
    if (r == l_true)
        validate_model();

}

void cmd_context::display_sat_result(lbool r) {
    switch (r) {
    case l_true:
        regular_stream() << "sat" << std::endl;
        break;
    case l_false:
        regular_stream() << "unsat" << std::endl;
        break;
    case l_undef:
        regular_stream() << "unknown" << std::endl;
        break;
    }
}

void cmd_context::validate_check_sat_result(lbool r) {
    switch (r) {
    case l_true:
        if (m_status == UNSAT) {
#ifdef _EXTERNAL_RELEASE
            throw cmd_exception("check annotation that says unsat");
#else
            diagnostic_stream() << "BUG: incompleteness" << std::endl;
            exit(ERR_INCOMPLETENESS);
#endif
        }
        break;
    case l_false:
        if (m_status == SAT) {
#ifdef _EXTERNAL_RELEASE
            throw cmd_exception("check annotation that says sat");
#else
            diagnostic_stream() << "BUG: unsoundness" << std::endl;
            exit(ERR_UNSOUNDNESS);
#endif
        }
        break;
    default:
        break;
    }
}

void cmd_context::set_diagnostic_stream(char const * name) { 
    m_diagnostic.set(name); 
    if (m_main_ctx) {
        set_warning_stream(&(*m_diagnostic));
        set_verbose_stream(diagnostic_stream());
    }
}

struct contains_array_op_proc {
    struct found {};
    family_id m_array_fid;
    contains_array_op_proc(ast_manager & m):m_array_fid(m.mk_family_id("array")) {}
    void operator()(var * n)        {}
    void operator()(app * n)        { 
        if (n->get_family_id() != m_array_fid)
            return;
        decl_kind k = n->get_decl_kind();
        if (k == OP_AS_ARRAY || 
            k == OP_STORE || 
            k == OP_ARRAY_MAP || 
            k == OP_CONST_ARRAY)
            throw found(); 
    }
    void operator()(quantifier * n) {}
};

/**
   \brief Check if the current model satisfies the quantifier free formulas.
*/
void cmd_context::validate_model() {
    if (!validate_model_enabled()) 
        return;
    if (!is_model_available())
        return;
    model_ref md;
    get_check_sat_result()->get_model(md);
    SASSERT(md.get() != 0);
    params_ref p;
    p.set_uint("max_degree", UINT_MAX); // evaluate algebraic numbers of any degree.
    p.set_uint("sort_store", true); 
    p.set_bool("completion", true); 
    model_evaluator evaluator(*(md.get()), p);
    contains_array_op_proc contains_array(m());
    {
        cancel_eh<model_evaluator> eh(evaluator);
        expr_ref r(m());
        scoped_ctrl_c ctrlc(eh);
        ptr_vector<expr>::const_iterator it  = begin_assertions();
        ptr_vector<expr>::const_iterator end = end_assertions();
        for (; it != end; ++it) {
            expr * a = *it;
            if (is_ground(a)) {
                r = 0;
                evaluator(a, r);
                TRACE("model_validate", tout << "checking\n" << mk_ismt2_pp(a, m()) << "\nresult:\n" << mk_ismt2_pp(r, m()) << "\n";);
                if (m().is_true(r))
                    continue;
                // The evaluator for array expressions is not complete
                // If r contains as_array/store/map/const expressions, then we do not generate the error.
                // TODO: improve evaluator for model expressions.
                // Note that, if "a" evaluates to false, then the error will be generated.
                try {
                    for_each_expr(contains_array, r);
                }
                catch (contains_array_op_proc::found) {
                    continue;
                }
                throw cmd_exception("an invalid model was generated");
            }
        }
    }
}

// FIXME: really interpolants_enabled ought to be a parameter to the solver factory,
// but this is a global change, so for now, we use an alternate solver factory
// for interpolation

void cmd_context::mk_solver() {
    bool proofs_enabled, models_enabled, unsat_core_enabled;
    params_ref p;
    m_params.get_solver_params(m(), p, proofs_enabled, models_enabled, unsat_core_enabled);
    if(produce_interpolants()){
        SASSERT(m_interpolating_solver_factory);
        m_solver = (*m_interpolating_solver_factory)(m(), p, true /* must have proofs */, models_enabled, unsat_core_enabled, m_logic);
    }
    else
        m_solver = (*m_solver_factory)(m(), p, proofs_enabled, models_enabled, unsat_core_enabled, m_logic);
}



void cmd_context::set_interpolating_solver_factory(solver_factory * f) {
  SASSERT(!has_manager());
  m_interpolating_solver_factory   = f;
}

void cmd_context::set_solver_factory(solver_factory * f) {
    m_solver_factory   = f;
    m_check_sat_result = 0;
    if (has_manager() && f != 0) {
        mk_solver();
        // assert formulas and create scopes in the new solver.
        unsigned lim = 0;
        svector<scope>::iterator it  = m_scopes.begin();
        svector<scope>::iterator end = m_scopes.end();
        for (; it != end; ++it) {
            scope & s = *it;
            for (unsigned i = lim; i < s.m_assertions_lim; i++) {
                m_solver->assert_expr(m_assertions[i]);
            }
            lim = s.m_assertions_lim;
            m_solver->push();
        }
        unsigned sz = m_assertions.size();
        for (unsigned i = lim; i < sz; i++) {
            m_solver->assert_expr(m_assertions[i]);
        }
    }
}

void cmd_context::display_statistics(bool show_total_time, double total_time) {
    statistics st;
    unsigned long long mem = memory::get_max_used_memory();
    if (show_total_time)
        st.update("total time", total_time);
    st.update("time", get_seconds());
    st.update("memory", static_cast<double>(mem)/static_cast<double>(1024*1024));
    if (m_check_sat_result) {
        m_check_sat_result->collect_statistics(st);
    }
    else if (m_solver) {
        m_solver->collect_statistics(st);
    }
    else if (m_opt) {
        m_opt->collect_statistics(st);
    }
    st.display_smt2(regular_stream());
}

void cmd_context::display_assertions() {
    if (!m_interactive_mode)
        throw cmd_exception("command is only available in interactive mode, use command (set-option :interactive-mode true)");
    vector<std::string>::const_iterator it  = m_assertion_strings.begin();
    vector<std::string>::const_iterator end = m_assertion_strings.end();
    regular_stream() << "(";
    for (bool first = true; it != end; ++it) {
        std::string const & s = *it;
        if (first)
            first = false;
        else
            regular_stream() << "\n ";
        regular_stream() << s;
    }
    regular_stream() << ")" << std::endl;
}

bool cmd_context::is_model_available() const {
    if (produce_models() &&
        has_manager() &&
        (cs_state() == css_sat || cs_state() == css_unknown)) {
        model_ref md;
        get_check_sat_result()->get_model(md);
        return md.get() != 0;
    }
    return false;
}

format_ns::format * cmd_context::pp(sort * s) const {
    TRACE("cmd_context", tout << "pp(sort * s), s: " << mk_pp(s, m()) << "\n";);
    return pm().pp(s);
}

cmd_context::pp_env & cmd_context::get_pp_env() const {
    if (m_pp_env.get() == 0) {
        const_cast<cmd_context*>(this)->m_pp_env = alloc(pp_env, *const_cast<cmd_context*>(this));
    }
    return *(m_pp_env.get());
}

void cmd_context::pp(expr * n, unsigned num_vars, char const * var_prefix, format_ns::format_ref & r, sbuffer<symbol> & var_names) const {
    mk_smt2_format(n, get_pp_env(), params_ref(), num_vars, var_prefix, r, var_names);
}

void cmd_context::pp(expr * n, format_ns::format_ref & r) const {
    sbuffer<symbol> buf;
    pp(n, 0, 0, r, buf);
}

void cmd_context::pp(func_decl * f, format_ns::format_ref & r) const {
    mk_smt2_format(f, get_pp_env(), params_ref(), r);
}

void cmd_context::display(std::ostream & out, sort * s, unsigned indent) const {
    format_ns::format_ref f(format_ns::fm(m()));
    f = pp(s);
    if (indent > 0) 
        f = format_ns::mk_indent(m(), indent, f);
    ::pp(out, f.get(), m());
}

void cmd_context::display(std::ostream & out, expr * n, unsigned indent, unsigned num_vars, char const * var_prefix, sbuffer<symbol> & var_names) const {
    format_ns::format_ref f(format_ns::fm(m()));
    pp(n, num_vars, var_prefix, f, var_names);
    if (indent > 0) 
        f = format_ns::mk_indent(m(), indent, f);
    ::pp(out, f.get(), m());
}

void cmd_context::display(std::ostream & out, expr * n, unsigned indent) const {
    sbuffer<symbol> buf;
    display(out, n, indent, 0, 0, buf);
}

void cmd_context::display(std::ostream & out, func_decl * d, unsigned indent) const {
    format_ns::format_ref f(format_ns::fm(m()));
    pp(d, f);
    if (indent > 0) 
        f = format_ns::mk_indent(m(), indent, f);
    ::pp(out, f.get(), m());
}

void cmd_context::dump_assertions(std::ostream & out) const {
    ptr_vector<expr>::const_iterator it  = m_assertions.begin();
    ptr_vector<expr>::const_iterator end = m_assertions.end();
    for (; it != end; ++it) {
        display(out, *it);
        out << std::endl;
    }
}

void cmd_context::display_smt2_benchmark(std::ostream & out, unsigned num, expr * const * assertions, symbol const & logic) const {
    if (logic != symbol::null)
        out << "(set-logic " << logic << ")" << std::endl;
    // collect uninterpreted function declarations
    decl_collector decls(m(), false);
    for (unsigned i = 0; i < num; i++) {
        decls.visit(assertions[i]);
    }

    // TODO: display uninterpreted sort decls, and datatype decls.
    
    unsigned num_decls = decls.get_num_decls();
    func_decl * const * fs = decls.get_func_decls();
    for (unsigned i = 0; i < num_decls; i++) {
        display(out, fs[i]);
        out << std::endl;
    }

    for (unsigned i = 0; i < num; i++) {
        out << "(assert ";
        display(out, assertions[i], 8);
        out << ")" << std::endl;
    }
    out << "(check-sat)" << std::endl;
}

void cmd_context::slow_progress_sample() { 
    SASSERT(m_solver);
    statistics st;
    regular_stream() << "(progress\n";
    m_solver->collect_statistics(st);
    st.display_smt2(regular_stream());
    svector<symbol> labels;
    m_solver->get_labels(labels);
    regular_stream() << "(labels";
    for (unsigned i = 0; i < labels.size(); i++) {
        regular_stream() << " " << labels[i];
    }
    regular_stream() << "))" << std::endl;
}

void cmd_context::fast_progress_sample() {
}

cmd_context::dt_eh::dt_eh(cmd_context & owner):
    m_owner(owner),
    m_dt_util(owner.m()) {
}

cmd_context::dt_eh::~dt_eh() {
}

void cmd_context::dt_eh::operator()(sort * dt) {
    TRACE("new_dt_eh", tout << "new datatype: "; m_owner.pm().display(tout, dt); tout << "\n";);
    ptr_vector<func_decl> const * constructors = m_dt_util.get_datatype_constructors(dt);
    unsigned num_constructors = constructors->size();
    for (unsigned j = 0; j < num_constructors; j++) {
        func_decl * c = constructors->get(j);
        m_owner.insert(c);
        TRACE("new_dt_eh", tout << "new constructor: " << c->get_name() << "\n";);
        func_decl * r = m_dt_util.get_constructor_recognizer(c);
        m_owner.insert(r);
        TRACE("new_dt_eh", tout << "new recognizer: " << r->get_name() << "\n";);
        ptr_vector<func_decl> const * accessors = m_dt_util.get_constructor_accessors(c);
        unsigned num_accessors = accessors->size();
        for (unsigned k = 0; k < num_accessors; k++) {
            func_decl * a = accessors->get(k);
            m_owner.insert(a);
            TRACE("new_dt_eh", tout << "new accessor: " << a->get_name() << "\n";);
        }
    }
}

std::ostream & operator<<(std::ostream & out, cmd_context::status st) {
    switch (st) {
    case cmd_context::UNSAT: out << "unsat"; break;
    case cmd_context::SAT: out << "sat"; break;
    default: out << "unknown"; break;
    }
    return out;
}

