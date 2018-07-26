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
#include "util/tptr.h"
#include "util/cancel_eh.h"
#include "util/scoped_ctrl_c.h"
#include "util/dec_ref_util.h"
#include "util/scoped_timer.h"
#include "ast/func_decl_dependencies.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include "ast/pb_decl_plugin.h"
#include "ast/fpa_decl_plugin.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/var_subst.h"
#include "ast/pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/decl_collector.h"
#include "ast/well_sorted.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/th_rewriter.h"
#include "model/model_evaluator.h"
#include "model/model_smt2_pp.h"
#include "model/model_v2_pp.h"
#include "model/model_params.hpp"
#include "tactic/tactic_exception.h"
#include "tactic/generic_model_converter.h"
#include "solver/smt_logics.h"
#include "cmd_context/basic_cmds.h"
#include "cmd_context/cmd_context.h"

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
        for (func_decl * f : *fs) {
            TRACE("func_decls", tout << "dec_ref of " << f->get_name() << " ref_count: " << f->get_ref_count() << "\n";);
            m.dec_ref(f);
        }
        dealloc(fs);
    }
    m_decls = nullptr;
}

bool func_decls::signatures_collide(func_decl* f, func_decl* g) const {
    return f == g;
}

bool func_decls::signatures_collide(unsigned n, sort* const* domain, sort* range, func_decl* g) const {
    if (g->get_range() != range) return false;
    if (n != g->get_arity()) return false;
    for (unsigned i = 0; i < n; ++i) {
        if (domain[i] != g->get_domain(i)) return false;
    }
    return true;
}

bool func_decls::contains(func_decl * f) const {
    if (GET_TAG(m_decls) == 0) {
        func_decl* g = UNTAG(func_decl*, m_decls);
        return g && signatures_collide(f, g);
    }
    else {
        func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
        for (func_decl* g : *fs) {
            if (signatures_collide(f, g)) return true;
        }
    }
    return false;
}


bool func_decls::contains(unsigned n, sort* const* domain, sort* range) const {
    if (GET_TAG(m_decls) == 0) {
        func_decl* g = UNTAG(func_decl*, m_decls);
        return g && signatures_collide(n, domain, range, g);
    }
    else {
        func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
        for (func_decl* g : *fs) {
            if (signatures_collide(n, domain, range, g)) return true;
        }
    }
    return false;
}

bool func_decls::insert(ast_manager & m, func_decl * f) {
    if (contains(f))
        return false;
    m.inc_ref(f);
    if (m_decls == nullptr) {
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
        m_decls = nullptr;
    }
    else {
        func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
        fs->erase(f);
        m.dec_ref(f);
        if (fs->empty()) {
            dealloc(fs);
            m_decls = nullptr;
        }
    }
}

/**
   \brief Return true if func_decls contains a declaration different from f, but with the same domain.
*/
bool func_decls::clash(func_decl * f) const {
    if (m_decls == nullptr)
        return false;
    if (GET_TAG(m_decls) == 0)
        return false;
    func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
    for (func_decl * g : *fs) {
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
    if (m_decls == nullptr || GET_TAG(m_decls) == 0)
        return false;
    func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
    return fs->size() > 1;
}

func_decl * func_decls::first() const {
    if (m_decls == nullptr)
        return nullptr;
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
    for (func_decl * f : *fs) {
        if (range != nullptr && f->get_range() != range)
            continue;
        if (f->get_arity() != arity)
            continue;
        unsigned i = 0;
        for (i = 0; domain && i < arity; i++) {
            if (f->get_domain(i) != domain[i])
                break;
        }
        if (i == arity)
            return f;
    }
    return nullptr;
}

func_decl * func_decls::find(ast_manager & m, unsigned num_args, expr * const * args, sort * range) const {
    if (!more_than_one())
        first();
    ptr_buffer<sort> sorts;
    for (unsigned i = 0; i < num_args; i++)
        sorts.push_back(m.get_sort(args[i]));
    return find(num_args, sorts.c_ptr(), range);
}

unsigned func_decls::get_num_entries() const {
    if (!more_than_one())
        return 1;

    func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
    return fs->size();
}

func_decl * func_decls::get_entry(unsigned inx) {
    if (!more_than_one()) {
        SASSERT(inx == 0);
        return first();
    }
    else {
        func_decl_set * fs = UNTAG(func_decl_set *, m_decls);
        auto b = fs->begin();
        for (unsigned i = 0; i < inx; i++)
            b++;
        return *b;
    }
}

void macro_decls::finalize(ast_manager& m) {
    for (auto v : *m_decls) m.dec_ref(v.m_body);
    dealloc(m_decls);
}

bool macro_decls::insert(ast_manager& m, unsigned arity, sort *const* domain, expr* body) {
    if (find(arity, domain)) return false;
    m.inc_ref(body);
    if (!m_decls) m_decls = alloc(vector<macro_decl>);
    m_decls->push_back(macro_decl(arity, domain, body));
    return true;
}

expr* macro_decls::find(unsigned arity, sort *const* domain) const {
    if (!m_decls) return nullptr;
    for (auto v : *m_decls) {
        if (v.m_domain.size() != arity) continue;
        bool eq = true;
        for (unsigned i = 0; eq && i < arity; ++i) {
            eq = domain[i] == v.m_domain[i];
        }
        if (eq) return v.m_body;
    }
    return nullptr;
}

void macro_decls::erase_last(ast_manager& m) {
    SASSERT(m_decls);
    SASSERT(!m_decls->empty());
    m.dec_ref(m_decls->back().m_body);
    m_decls->pop_back();
}

bool cmd_context::contains_func_decl(symbol const& s, unsigned n, sort* const* domain, sort* range) const {
    func_decls fs;
    return m_func_decls.find(s, fs) && fs.contains(n, domain, range);
}

bool cmd_context::contains_macro(symbol const& s) const {
    return m_macros.contains(s);
}

bool cmd_context::contains_macro(symbol const& s, func_decl* f) const {
    return contains_macro(s, f->get_arity(), f->get_domain());
}

bool cmd_context::contains_macro(symbol const& s, unsigned arity, sort *const* domain) const {
    macro_decls decls;
    return m_macros.find(s, decls) && nullptr != decls.find(arity, domain);
}

void cmd_context::insert_macro(symbol const& s, unsigned arity, sort*const* domain, expr* t) {
    macro_decls decls;
    if (!m_macros.find(s, decls)) {
        VERIFY(decls.insert(m(), arity, domain, t));
        m_macros.insert(s, decls);
    }
    else {
        VERIFY(decls.insert(m(), arity, domain, t));
    }
}

void cmd_context::erase_macro(symbol const& s) {
    macro_decls decls;
    VERIFY(m_macros.find(s, decls));
    decls.erase_last(m());
}

bool cmd_context::macros_find(symbol const& s, unsigned n, expr*const* args, expr*& t) const {
    macro_decls decls;
    if (!m_macros.find(s, decls)) {
        return false;
    }
    for (macro_decl const& d : decls) {
        if (d.m_domain.size() != n) continue;
        bool eq = true;
        for (unsigned i = 0; eq && i < n; ++i) {
            eq = m().compatible_sorts(d.m_domain[i], m().get_sort(args[i]));
        }
        if (eq) {
            t = d.m_body;
            return true;
        }
    }
    return false;
}


ast_object_ref::ast_object_ref(cmd_context & ctx, ast * a):m_ast(a) {
    ctx.m().inc_ref(a);
}

void ast_object_ref::finalize(cmd_context & ctx) {
    ctx.m().dec_ref(m_ast);
}

void stream_ref::set(std::ostream& out) {
    reset();
    m_owner = false;
    m_name = "caller-owned";
    m_stream = &out;
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
            throw cmd_exception(std::move(msg));
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
    seq_util      m_sutil;
    datatype_util m_dtutil;

    datalog::dl_decl_util m_dlutil;

    format_ns::format * pp_fdecl_name(symbol const & s, func_decls const & fs, func_decl * f, unsigned & len) {
        format_ns::format * f_name = smt2_pp_environment::pp_fdecl_name(s, len, f->is_skolem());
        if (!fs.more_than_one())
            return f_name;
        if (!fs.clash(f))
            return f_name;
        return pp_as(f_name, f->get_range());
    }

    format_ns::format * pp_fdecl_ref_core(symbol const & s, func_decls const & fs, func_decl * f) {
        unsigned len;
        format_ns::format * f_name = smt2_pp_environment::pp_fdecl_name(s, len, f->is_skolem());
        if (!fs.more_than_one())
            return f_name;
        return pp_signature(f_name, f);
    }

public:
    pp_env(cmd_context & o):m_owner(o), m_autil(o.m()), m_bvutil(o.m()), m_arutil(o.m()), m_futil(o.m()), m_sutil(o.m()), m_dtutil(o.m()), m_dlutil(o.m()) {}
    ~pp_env() override {}
    ast_manager & get_manager() const override { return m_owner.m(); }
    arith_util & get_autil() override { return m_autil; }
    bv_util & get_bvutil() override { return m_bvutil; }
    array_util & get_arutil() override { return m_arutil; }
    fpa_util & get_futil() override { return m_futil; }
    seq_util & get_sutil() override { return m_sutil; }
    datatype_util & get_dtutil() override { return m_dtutil; }

    datalog::dl_decl_util& get_dlutil() override { return m_dlutil; }
    bool uses(symbol const & s) const override {
        return
            m_owner.m_builtin_decls.contains(s) ||
            m_owner.m_func_decls.contains(s);
    }
    format_ns::format * pp_sort(sort * s) override {
        return m_owner.pp(s);
    }
    format_ns::format * pp_fdecl(func_decl * f, unsigned & len) override {
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
    format_ns::format * pp_fdecl_ref(func_decl * f) override {
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
    m_produce_unsat_assumptions(false),
    m_produce_assignments(false),
    m_status(UNKNOWN),
    m_numeral_as_real(false),
    m_ignore_check(false),
    m_processing_pareto(false),
    m_exit_on_error(false),
    m_manager(m),
    m_own_manager(m == nullptr),
    m_manager_initialized(false),
    m_rec_fun_declared(false),
    m_pmanager(nullptr),
    m_sexpr_manager(nullptr),
    m_regular("stdout", std::cout),
    m_diagnostic("stderr", std::cerr) {
    SASSERT(m != 0 || !has_manager());
    install_basic_cmds(*this);
    install_ext_basic_cmds(*this);
    install_core_tactic_cmds(*this);
    SASSERT(m != 0 || !has_manager());
    if (m_main_ctx) {
        set_verbose_stream(diagnostic_stream());
    }
}

cmd_context::~cmd_context() {
    if (m_main_ctx) {
        set_verbose_stream(std::cerr);
    }
    pop(m_scopes.size());
    finalize_cmds();
    finalize_tactic_cmds();
    finalize_probes();
    reset(true);
    m_mc0 = nullptr;
    m_solver = nullptr;
    m_check_sat_result = nullptr;
}

void cmd_context::set_cancel(bool f) {
    if (has_manager()) {
        if (f) {
            m().limit().cancel();
        }
        else {
            m().limit().reset_cancel();
        }
    }
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
    if (m_opt) {
        get_opt()->updt_params(gparams::get_module("opt"));
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
    if (m_check_sat_result.get() == nullptr)
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
    for (builtin_name const& n : names) {
        psort_decl * d = pm().mk_psort_builtin_decl(n.m_name, fid, n.m_kind);
        insert(d);
    }
}

void cmd_context::register_builtin_ops(decl_plugin * p) {
    svector<builtin_name> names;
    p->get_op_names(names, m_logic);
    family_id fid = p->get_family_id();
    for (builtin_name const& n : names) {
        if (m_builtin_decls.contains(n.m_name)) {
            builtin_decl & d = m_builtin_decls.find(n.m_name);
            builtin_decl * new_d = alloc(builtin_decl, fid, n.m_kind, d.m_next);
            d.m_next = new_d;
            m_extra_builtin_decls.push_back(new_d);
        }
        else {
            m_builtin_decls.insert(n.m_name, builtin_decl(fid, n.m_kind));
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


bool cmd_context::logic_has_arith() const {
    return !has_logic() || smt_logics::logic_has_arith(m_logic);
}



bool cmd_context::logic_has_bv() const {
    return !has_logic() || smt_logics::logic_has_bv(m_logic);
}

bool cmd_context::logic_has_seq() const {
    return !has_logic() || smt_logics::logic_has_seq(m_logic);
}

bool cmd_context::logic_has_pb() const {
    return !has_logic() || smt_logics::logic_has_pb(m_logic);
}

bool cmd_context::logic_has_fpa() const {
    return !has_logic() || smt_logics::logic_has_fpa(m_logic);
}

bool cmd_context::logic_has_array() const {
    return !has_logic() || smt_logics::logic_has_array(m_logic);
}

bool cmd_context::logic_has_datatype() const {
    return !has_logic() || smt_logics::logic_has_datatype(m_logic);
}

void cmd_context::init_manager_core(bool new_manager) {
    SASSERT(m_manager != 0);
    SASSERT(m_pmanager != 0);
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
        register_plugin(symbol("pb"),       alloc(pb_decl_plugin), logic_has_pb());
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
        load_plugin(symbol("pb"),       logic_has_pb(), fids);
        for (family_id fid : fids) {
            decl_plugin * p = m_manager->get_plugin(fid);
            if (p) {
                register_builtin_sorts(p);
                register_builtin_ops(p);
            }
        }
    }
    m_dt_eh = alloc(dt_eh, *this);
    m_pmanager->set_new_datatype_eh(m_dt_eh.get());
    if (!has_logic() && new_manager) {
        TRACE("cmd_context", tout << "init manager " << m_logic << "\n";);
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
        m_check_sat_result = nullptr;
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

bool cmd_context::set_logic(symbol const & s) {
    TRACE("cmd_context", tout << s << "\n";);
    if (has_logic())
        throw cmd_exception("the logic has already been set");
    if (has_manager() && m_main_ctx)
        throw cmd_exception("logic must be set before initialization");
    if (!smt_logics::supported_logic(s)) {
        return false;
    }
    m_logic = s;
    if (smt_logics::logic_has_reals_only(s)) {
        m_numeral_as_real = true;
    }
    return true;
}

std::string cmd_context::reason_unknown() const {
    if (m_check_sat_result.get() == nullptr)
        return "state of the most recent check-sat command is not known";
    return m_check_sat_result->reason_unknown();
}

bool cmd_context::is_func_decl(symbol const & s) const {
    return m_builtin_decls.contains(s) || m_func_decls.contains(s);
}

void cmd_context::insert(symbol const & s, func_decl * f) {
    if (!m_check_logic(f)) {
        throw cmd_exception(m_check_logic.get_last_error());
    }
    if (contains_macro(s, f)) {
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

void cmd_context::insert(symbol const & s, unsigned arity, sort *const* domain, expr * t) {
    expr_ref _t(t, m());
    if (m_builtin_decls.contains(s)) {
        throw cmd_exception("invalid macro/named expression, builtin symbol ", s);
    }
    if (contains_macro(s, arity, domain)) {
        throw cmd_exception("named expression already defined");
    }
    if (contains_func_decl(s, arity, domain, m().get_sort(t))) {
        throw cmd_exception("invalid named expression, declaration already defined with this name ", s);
    }
    TRACE("insert_macro", tout << "new macro " << arity << "\n" << mk_pp(t, m()) << "\n";);
    insert_macro(s, arity, domain, t);
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
    object_ref * old_r = nullptr;
    if (m_object_refs.find(s, old_r)) {
        old_r->dec_ref(*this);
    }
    m_object_refs.insert(s, r);
}

void cmd_context::model_add(symbol const & s, unsigned arity, sort *const* domain, expr * t) {
    if (!m_mc0.get()) m_mc0 = alloc(generic_model_converter, m(), "cmd_context");
    if (m_solver.get() && !m_solver->mc0()) m_solver->set_model_converter(m_mc0.get()); 
    func_decl_ref fn(m().mk_func_decl(s, arity, domain, m().get_sort(t)), m());
    dictionary<func_decls>::entry * e = m_func_decls.insert_if_not_there2(s, func_decls());
    func_decls & fs = e->get_data().m_value;
    fs.insert(m(), fn);
    VERIFY(fn->get_range() == m().get_sort(t));
    m_mc0->add(fn, t);
}

void cmd_context::model_del(func_decl* f) {
    if (!m_mc0.get()) m_mc0 = alloc(generic_model_converter, m(), "cmd_context");
    if (m_solver.get() && !m_solver->mc0()) m_solver->set_model_converter(m_mc0.get()); 
    m_mc0->hide(f);
}

void cmd_context::insert_rec_fun(func_decl* f, expr_ref_vector const& binding, svector<symbol> const& ids, expr* e) {
    expr_ref eq(m());
    app_ref lhs(m());
    lhs = m().mk_app(f, binding.size(), binding.c_ptr());
    eq  = m().mk_eq(lhs, e);
    if (!ids.empty()) {
        if (is_var(e)) {
            ptr_vector<sort> domain;
            for (expr* b : binding) domain.push_back(m().get_sort(b));
            insert_macro(f->get_name(), domain.size(), domain.c_ptr(), e);
            return;
        }
        if (!is_app(e)) {
            throw cmd_exception("Z3 only supports recursive definitions that are proper terms (not binders or variables)");
        }
        expr* pats[2] = { m().mk_pattern(lhs), m().mk_pattern(to_app(e)) };
        eq  = m().mk_forall(ids.size(), f->get_domain(), ids.c_ptr(), eq, 0, m().rec_fun_qid(), symbol::null, 2, pats);
    }

    //
    // disable warning given the current way they are used
    // (Z3 will here silently assume and not check the definitions to be well founded,
    // and please use HSF for everything else).
    //
    if (false && !ids.empty() && !m_rec_fun_declared) {
        warning_msg("recursive function definitions are assumed well-founded");
        m_rec_fun_declared = true;
    }
    assert_expr(eq);
}

func_decl * cmd_context::find_func_decl(symbol const & s) const {
    builtin_decl d;
    if (m_builtin_decls.find(s, d)) {
        try {
            // Remark: ignoring m_next of d. We do not allow two different theories to define the same constant name.
            func_decl * f;
            f = m().mk_func_decl(d.m_fid, d.m_decl, 0, nullptr, 0, static_cast<sort*const*>(nullptr), nullptr);
            if (f != nullptr)
                return f;
        }
        catch (ast_exception &) {
        }
        throw cmd_exception("invalid function declaration reference, must provide signature for builtin symbol ", s);
    }
    if (contains_macro(s)) {
        throw cmd_exception("invalid function declaration reference, named expressions (aka macros) cannot be referenced ", s);
    }
    func_decls fs;
    if (m_func_decls.find(s, fs)) {
        if (fs.more_than_one())
            throw cmd_exception("ambiguous function declaration reference, provide full signature to disumbiguate (<symbol> (<sort>*) <sort>) ", s);
        return fs.first();
    }
    throw cmd_exception("invalid function declaration reference, unknown function ", s);
    return nullptr;
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
    while (curr != nullptr) {
        if (curr->m_fid == target_id)
            return *curr;
        curr = curr->m_next;
    }
    return first;
}

func_decl * cmd_context::find_func_decl(symbol const & s, unsigned num_indices, unsigned const * indices,
                                        unsigned arity, sort * const * domain, sort * range) const {
    builtin_decl d;
    if (domain && m_builtin_decls.find(s, d)) {
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
            f = m().mk_func_decl(fid, k, 0, nullptr, arity, domain, range);
        }
        else {
            buffer<parameter> ps;
            for (unsigned i = 0; i < num_indices; i++)
                ps.push_back(parameter(indices[i]));
            f = m().mk_func_decl(fid, k, num_indices, ps.c_ptr(), arity, domain, range);
        }
        if (f == nullptr)
            throw cmd_exception("invalid function declaration reference, invalid builtin reference ", s);
        return f;
    }

    if (domain && contains_macro(s, arity, domain))
        throw cmd_exception("invalid function declaration reference, named expressions (aka macros) cannot be referenced ", s);

    if (num_indices > 0)
        throw cmd_exception("invalid indexed function declaration reference, unknown builtin function ", s);

    func_decl * f = nullptr;
    func_decls fs;
    if (m_func_decls.find(s, fs)) {
        f = fs.find(arity, domain, range);
    }
    if (f == nullptr)
        throw cmd_exception("invalid function declaration reference, unknown function ", s);
    return f;
}

psort_decl * cmd_context::find_psort_decl(symbol const & s) const {
    psort_decl * p = nullptr;
    m_psort_decls.find(s, p);
    return p;
}


cmd * cmd_context::find_cmd(symbol const & s) const {
    cmd * c = nullptr;
    m_cmds.find(s, c);
    return c;
}

sexpr * cmd_context::find_user_tactic(symbol const & s) const {
    sexpr * n = nullptr;
    m_user_tactic_decls.find(s, n);
    return n;
}

object_ref * cmd_context::find_object_ref(symbol const & s) const {
    object_ref * r = nullptr;
    m_object_refs.find(s, r);
    if (r == nullptr) throw cmd_exception("unknown global variable ", s);
    return r;
}

#define CHECK_SORT(T) if (well_sorted_check_enabled()) m().check_sorts_core(T)

void cmd_context::mk_const(symbol const & s, expr_ref & result) const {
    mk_app(s, 0, nullptr, 0, nullptr, nullptr, result);
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
            result = m().mk_app(fid, k, 0, nullptr, num_args, args, range);
        }
        else {
            result = m().mk_app(fid, k, num_indices, indices, num_args, args, range);
        }
        if (result.get() == nullptr)
            throw cmd_exception("invalid builtin application ", s);
        CHECK_SORT(result.get());
        return;
    }
    if (num_indices > 0)
        throw cmd_exception("invalid use of indexed identifier, unknown builtin function ", s);
    expr* _t;
    if (macros_find(s, num_args, args, _t)) {
        TRACE("macro_bug", tout << "well_sorted_check_enabled(): " << well_sorted_check_enabled() << "\n";
              tout << "s: " << s << "\n";
              tout << "body:\n" << mk_ismt2_pp(_t, m()) << "\n";
              tout << "args:\n"; for (unsigned i = 0; i < num_args; i++) tout << mk_ismt2_pp(args[i], m()) << "\n" << mk_pp(m().get_sort(args[i]), m()) << "\n";);
        var_subst subst(m());
        result = subst(_t, num_args, args);
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

    if (num_args == 0 && range == nullptr) {
        if (fs.more_than_one())
            throw cmd_exception("ambiguous constant reference, more than one constant with the same sort, use a qualified expression (as <symbol> <sort>) to disumbiguate ", s);
        func_decl * f = fs.first();
        if (f == nullptr) {
            throw cmd_exception("unknown constant ", s);
        }
        if (f->get_arity() != 0)
            throw cmd_exception("invalid function application, missing arguments ", s);
        result = m().mk_const(f);
    }
    else {
        func_decl * f = fs.find(m(), num_args, args, range);
        if (f == nullptr) {
            std::ostringstream buffer;
            buffer << "unknown constant " << s << " ";
            buffer << " (";
            bool first = true;
            for (unsigned i = 0; i < num_args; ++i, first = false) {
                if (!first) buffer << " ";
                buffer << mk_pp(m().get_sort(args[i]), m());
            }            
            buffer << ") ";
            if (range) buffer << mk_pp(range, m()) << " ";
            for (unsigned i = 0; i < fs.get_num_entries(); ++i) {
                buffer << "\ndeclared: " << mk_pp(fs.get_entry(i), m()) << " ";
            }
            throw cmd_exception(buffer.str().c_str());
        }
        if (well_sorted_check_enabled())
            m().check_sort(f, num_args, args);
        result = m().mk_app(f, num_args, args);
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
    object_ref * r = nullptr;
    if (m_object_refs.find(s, r)) {
        r->dec_ref(*this);
        m_object_refs.erase(s);
    }
}

void cmd_context::reset_func_decls() {
    for (auto & kv : m_func_decls) {
        kv.m_value.finalize(m());
    }
    m_func_decls.reset();
    m_func_decls_stack.reset();
    m_func_decl2alias.reset();
}

void cmd_context::reset_psort_decls() {
    for (auto & kv : m_psort_decls) {
        psort_decl * p = kv.m_value;
        pm().dec_ref(p);
    }
    m_psort_decls.reset();
    m_psort_decls_stack.reset();
}

void cmd_context::reset_macros() {
    for (auto & kv : m_macros) {
        kv.m_value.finalize(m());
    }
    m_macros.reset();
    m_macros_stack.reset();
}

void cmd_context::reset_cmds() {
    for (auto& kv : m_cmds) {
        kv.m_value->reset(*this);
    }
}

void cmd_context::finalize_cmds() {
    for (auto& kv : m_cmds) {
        cmd * c = kv.m_value;
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
    for (auto& kv : m_object_refs) {
        object_ref * r = kv.m_value;
        r->dec_ref(*this);
    }
    m_object_refs.reset();
}

void cmd_context::insert_aux_pdecl(pdecl * p) {
    pm().inc_ref(p);
    m_aux_pdecls.push_back(p);
}

void cmd_context::reset(bool finalize) {    
    m_processing_pareto = false;
    m_logic = symbol::null;
    m_check_sat_result = nullptr;
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
    m_solver = nullptr;
    m_mc0 = nullptr;
    m_scopes.reset();
    m_opt = nullptr;
    m_pp_env = nullptr;
    m_dt_eh  = nullptr;
    if (m_manager) {
        dealloc(m_pmanager);
        m_pmanager = nullptr;
        if (m_own_manager) {
            dealloc(m_manager);
            m_manager = nullptr;
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
        m_sexpr_manager = nullptr;
    }
    SASSERT(!m_own_manager || !has_manager());
}

void cmd_context::assert_expr(expr * t) {
    m_processing_pareto = false;
    if (!m_check_logic(t))
        throw cmd_exception(m_check_logic.get_last_error());
    m_check_sat_result = nullptr;
    m().inc_ref(t);
    m_assertions.push_back(t);
    if (produce_unsat_cores())
        m_assertion_names.push_back(0);
    if (m_solver)
        m_solver->assert_expr(t);
}

void cmd_context::assert_expr(symbol const & name, expr * t) {
    m_processing_pareto = false;
    if (!m_check_logic(t))
        throw cmd_exception(m_check_logic.get_last_error());
    if (!produce_unsat_cores() || name == symbol::null) {
        assert_expr(t);
        return;
    }
    m_check_sat_result = nullptr;
    m().inc_ref(t);
    m_assertions.push_back(t);
    expr * ans  = m().mk_const(name, m().mk_bool_sort());
    m().inc_ref(ans);
    m_assertion_names.push_back(ans);
    if (m_solver)
        m_solver->assert_expr(t, ans);
}

void cmd_context::push() {
    m_check_sat_result = nullptr;
    init_manager();
    m_scopes.push_back(scope());
    scope & s = m_scopes.back();
    s.m_func_decls_stack_lim   = m_func_decls_stack.size();
    s.m_psort_decls_stack_lim  = m_psort_decls_stack.size();
    s.m_psort_inst_stack_lim   = m_psort_inst_stack.size();
    s.m_macros_stack_lim       = m_macros_stack.size();
    s.m_aux_pdecls_lim         = m_aux_pdecls.size();
    s.m_assertions_lim         = m_assertions.size();
    m().limit().push(m_params.rlimit());
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
    m_func_decls_stack.resize(old_sz);
}

void cmd_context::restore_psort_inst(unsigned old_sz) {
    for (unsigned i = m_psort_inst_stack.size(); i-- > old_sz; ) {
        pdecl * s = m_psort_inst_stack[i];
        s->reset_cache(pm());
        pm().dec_ref(s);
    }
    m_psort_inst_stack.resize(old_sz);
}

void cmd_context::restore_psort_decls(unsigned old_sz) {
    SASSERT(old_sz <= m_psort_decls_stack.size());
    svector<symbol>::iterator it  = m_psort_decls_stack.begin() + old_sz;
    svector<symbol>::iterator end = m_psort_decls_stack.end();
    for (; it != end; ++it) {
        symbol const & s = *it;
        psort_decl * d = nullptr;
        VERIFY(m_psort_decls.find(s, d));
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
        erase_macro(s);
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
    m_processing_pareto = false;
    if (!has_manager()) {
        // restore_assertions invokes m(), so if cmd_context does not have a manager, it will try to create one.
        SASSERT(old_sz == m_assertions.size());
        SASSERT(m_assertions.empty());
        return;
    }
    if (old_sz == m_assertions.size())
        return;
    SASSERT(old_sz < m_assertions.size());
    SASSERT(!m_interactive_mode || m_assertions.size() == m_assertion_strings.size());
    restore(m(), m_assertions, old_sz);
    if (produce_unsat_cores())
        restore(m(), m_assertion_names, old_sz);
    if (m_interactive_mode)
        m_assertion_strings.resize(old_sz);
}

void cmd_context::pop(unsigned n) {
    m_check_sat_result = nullptr;
    m_processing_pareto = false;
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
    restore_psort_inst(s.m_psort_inst_stack_lim);
    m_scopes.shrink(new_lvl);
    while (n--) {
        m().limit().pop();
    }

}

void cmd_context::check_sat(unsigned num_assumptions, expr * const * assumptions) {
    if (m_ignore_check)
        return;
    IF_VERBOSE(100, verbose_stream() << "(started \"check-sat\")" << std::endl;);
    TRACE("before_check_sat", dump_assertions(tout););
    init_manager();
    unsigned timeout = m_params.m_timeout;
    unsigned rlimit  = m_params.rlimit();
    scoped_watch sw(*this);
    lbool r;
    bool was_opt = false;

    if (m_opt && !m_opt->empty()) {
        was_opt = true;
        m_check_sat_result = get_opt();
        cancel_eh<reslimit> eh(m().limit());
        scoped_ctrl_c ctrlc(eh);
        scoped_timer timer(timeout, &eh);
        scoped_rlimit _rlimit(m().limit(), rlimit);
        if (!m_processing_pareto) {
            ptr_vector<expr> cnstr(m_assertions);
            cnstr.append(num_assumptions, assumptions);
            get_opt()->set_hard_constraints(cnstr);
        }
        try {
            r = get_opt()->optimize();
            if (r == l_true && get_opt()->is_pareto()) {
                m_processing_pareto = true;
            }
        }
        catch (z3_error & ex) {
            throw ex;
        }
        catch (z3_exception & ex) {
            throw cmd_exception(ex.msg());
        }
        if (m_processing_pareto && r != l_true) {
            m_processing_pareto = false;
        }
        get_opt()->set_status(r);
    }
    else if (m_solver) {
        m_check_sat_result = m_solver.get(); // solver itself stores the result.
        m_solver->set_progress_callback(this);
        cancel_eh<reslimit> eh(m().limit());
        scoped_ctrl_c ctrlc(eh);
        scoped_timer timer(timeout, &eh);
        scoped_rlimit _rlimit(m().limit(), rlimit);
        try {
            r = m_solver->check_sat(num_assumptions, assumptions);
            if (r == l_undef && m().canceled()) {
                m_solver->set_reason_unknown(eh);
            }
        }
        catch (z3_error & ex) {
            throw ex;
        }
        catch (z3_exception & ex) {
            if (m().canceled()) {
                m_solver->set_reason_unknown(eh);
            }
            else {
                m_solver->set_reason_unknown(ex.msg());
            }
            r = l_undef;
        }
        m_solver->set_status(r);
    }
    else {
        // There is no solver installed in the command context.
        regular_stream() << "unknown" << std::endl;
        return;
    }
    display_sat_result(r);
    if (r == l_true) {
        validate_model();
    }
    validate_check_sat_result(r);
    if (was_opt && r != l_false && !m_processing_pareto) {
        // get_opt()->display_assignment(regular_stream());
    }

    model_ref md;
    if (r == l_true && m_params.m_dump_models && is_model_available(md)) {
        display_model(md);
    }
}

void cmd_context::get_consequences(expr_ref_vector const& assumptions, expr_ref_vector const& vars, expr_ref_vector & conseq) {
    unsigned timeout = m_params.m_timeout;
    unsigned rlimit  = m_params.rlimit();
    lbool r;
    m_check_sat_result = m_solver.get(); // solver itself stores the result.
    m_solver->set_progress_callback(this);
    cancel_eh<reslimit> eh(m().limit());
    scoped_ctrl_c ctrlc(eh);
    scoped_timer timer(timeout, &eh);
    scoped_rlimit _rlimit(m().limit(), rlimit);
    try {
        r = m_solver->get_consequences(assumptions, vars, conseq);
    }
    catch (z3_error & ex) {
        throw ex;
    }
    catch (z3_exception & ex) {
        m_solver->set_reason_unknown(ex.msg());
        r = l_undef;
    }
    m_solver->set_status(r);
    display_sat_result(r);
}


void cmd_context::reset_assertions() {
    if (!m_global_decls) {
        reset(false);
        return;
    }

    if (m_opt) {
        m_opt = nullptr;
    }
    if (m_solver) {
        m_solver = nullptr;
        mk_solver();
    }
    restore_assertions(0);
    for (scope& s : m_scopes) {
        s.m_assertions_lim = 0;
        if (m_solver) m_solver->push();
    }
}


void cmd_context::display_dimacs() {
    if (m_solver) {
        try {
            gparams::set("sat.dimacs.display", "true");
            params_ref p;
            m_solver->updt_params(p);
            m_solver->check_sat(0, nullptr);
        }
        catch (...) {
            gparams::set("sat.dimacs.display", "false");        
            params_ref p;
            m_solver->updt_params(p);
            throw;
        }
        gparams::set("sat.dimacs.display", "false");        
        params_ref p;
        m_solver->updt_params(p);
    }
}

void cmd_context::display_model(model_ref& mdl) {
    if (mdl) {
        if (m_mc0) (*m_mc0)(mdl);
        if (m_params.m_model_compress) mdl->compress();
        model_params p;
        if (p.v1() || p.v2()) {
            std::ostringstream buffer;
            model_v2_pp(buffer, *mdl, p.partial());
            regular_stream() << "\"" << escaped(buffer.str().c_str(), true) << "\"" << std::endl;
        } else {
            regular_stream() << "(model " << std::endl;
            model_smt2_pp(regular_stream(), *this, *mdl, 2);
            regular_stream() << ")" << std::endl;
        }
    }
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
            // WORKAROUND: `exit()` causes LSan to be invoked and produce
            // many false positives.
            _Exit(ERR_INCOMPLETENESS);
#endif
        }
        break;
    case l_false:
        if (m_status == SAT) {
#ifdef _EXTERNAL_RELEASE
            throw cmd_exception("check annotation that says sat");
#else
            diagnostic_stream() << "BUG: unsoundness" << std::endl;
            // WORKAROUND: `exit()` causes LSan to be invoked and produce
            // many false positives.
            _Exit(ERR_UNSOUNDNESS);
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

struct contains_underspecified_op_proc {
    struct found {};
    family_id m_array_fid;
    datatype_util m_dt;
    
    contains_underspecified_op_proc(ast_manager & m):m_array_fid(m.mk_family_id("array")), m_dt(m) {}
    void operator()(var * n)        {}
    void operator()(app * n)        {
        if (m_dt.is_accessor(n->get_decl())) 
            throw found();
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
    \brief Complete the model if necessary.
*/
void cmd_context::complete_model(model_ref& md) const {
    if (gparams::get_value("model.completion") != "true" || !md.get())
        return;

    params_ref p;
    p.set_uint("max_degree", UINT_MAX); // evaluate algebraic numbers of any degree.
    p.set_uint("sort_store", true);
    p.set_bool("completion", true);
    model_evaluator evaluator(*(md.get()), p);
    evaluator.set_expand_array_equalities(false);

    scoped_rlimit _rlimit(m().limit(), 0);
    cancel_eh<reslimit> eh(m().limit());
    expr_ref r(m());
    scoped_ctrl_c ctrlc(eh);

    for (auto kd : m_psort_decls) {
        symbol const & k = kd.m_key;
        psort_decl * v = kd.m_value;
        if (v->is_user_decl()) {
            SASSERT(!v->has_var_params());
            IF_VERBOSE(12, verbose_stream() << "(model.completion " << k << ")\n"; );
            ptr_vector<sort> param_sorts(v->get_num_params(), m().mk_bool_sort());
            sort * srt = v->instantiate(*m_pmanager, param_sorts.size(), param_sorts.c_ptr());
            if (!md->has_uninterpreted_sort(srt)) {
                expr * singleton = m().get_some_value(srt);
                md->register_usort(srt, 1, &singleton);
            }
        }
    }

    for (unsigned i = 0; i < md->get_num_functions(); i++) {
        func_decl * f = md->get_function(i);
        func_interp * fi = md->get_func_interp(f);
        IF_VERBOSE(12, verbose_stream() << "(model.completion " << f->get_name() << ")\n"; );
        if (fi->is_partial()) {
            sort * range = f->get_range();
            fi->set_else(m().get_some_value(range));
        }
    }

    for (auto kd : m_func_decls) {
        symbol const & k = kd.m_key;
        func_decls & v = kd.m_value;
        IF_VERBOSE(12, verbose_stream() << "(model.completion " << k << ")\n"; );
        for (unsigned i = 0; i < v.get_num_entries(); i++) {
            func_decl * f = v.get_entry(i);
            if (!md->has_interpretation(f)) {
                sort * range = f->get_range();
                expr * some_val = m().get_some_value(range);
                if (f->get_arity() > 0) {
                    func_interp * fi = alloc(func_interp, m(), f->get_arity());
                    fi->set_else(some_val);
                    md->register_decl(f, fi);
                }
                else
                    md->register_decl(f, some_val);
            }
        }
    }
}

/**
   \brief Check if the current model satisfies the quantifier free formulas.
*/
void cmd_context::validate_model() {
    model_ref md;
    if (!validate_model_enabled())
        return;
    if (!is_model_available(md))
        return;
    SASSERT(md.get() != 0);
    params_ref p;
    p.set_uint("max_degree", UINT_MAX); // evaluate algebraic numbers of any degree.
    p.set_uint("sort_store", true);
    p.set_bool("completion", true);
    model_evaluator evaluator(*(md.get()), p);
    evaluator.set_expand_array_equalities(false);
    contains_underspecified_op_proc contains_underspecified(m());
    {
        scoped_rlimit _rlimit(m().limit(), 0);
        cancel_eh<reslimit> eh(m().limit());
        expr_ref r(m());
        scoped_ctrl_c ctrlc(eh);
        ptr_vector<expr>::const_iterator it  = begin_assertions();
        ptr_vector<expr>::const_iterator end = end_assertions();
        bool invalid_model = false;
        for (; it != end; ++it) {
            expr * a = *it;
            if (is_ground(a)) {
                r = nullptr;
                evaluator(a, r);
                TRACE("model_validate", tout << "checking\n" << mk_ismt2_pp(a, m()) << "\nresult:\n" << mk_ismt2_pp(r, m()) << "\n";);
                if (m().is_true(r))
                    continue;

                // The evaluator for array expressions is not complete
                // If r contains as_array/store/map/const expressions, then we do not generate the error.
                // TODO: improve evaluator for model expressions.
                // Note that, if "a" evaluates to false, then the error will be generated.
                if (has_quantifiers(r)) {
                    continue;
                }
                try {
                    for_each_expr(contains_underspecified, a);
                    for_each_expr(contains_underspecified, r);
                }
                catch (contains_underspecified_op_proc::found) {
                    continue;
                }
                TRACE("model_validate", model_smt2_pp(tout, *this, *md, 0););
                IF_VERBOSE(10, verbose_stream() << "model check failed on: " << mk_pp(a, m()) << "\n";);                
                IF_VERBOSE(11, model_smt2_pp(verbose_stream(), *this, *md, 0););                
                invalid_model = true;
            }
        }
        if (invalid_model) {
            throw cmd_exception("an invalid model was generated");
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
    if (produce_interpolants() && m_interpolating_solver_factory) {
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
    m_check_sat_result = nullptr;
    if (has_manager() && f != nullptr) {
        mk_solver();
        // assert formulas and create scopes in the new solver.
        unsigned lim = 0;
        for (scope& s : m_scopes) {
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
    if (show_total_time)
        st.update("total time", total_time);
    st.update("time", get_seconds());
    get_memory_statistics(st);
    get_rlimit_statistics(m().limit(), st);
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
    regular_stream() << "(";
    bool first = true;
    for (std::string const& s : m_assertion_strings) {
        if (first)
            first = false;
        else
            regular_stream() << "\n ";
        regular_stream() << s;
    }
    regular_stream() << ")" << std::endl;
}

bool cmd_context::is_model_available(model_ref& md) const {
    if (produce_models() &&
        has_manager() &&
        (cs_state() == css_sat || cs_state() == css_unknown)) {
        get_check_sat_result()->get_model(md);
        complete_model(md);
        return md.get() != nullptr;
    }
    return false;
}

format_ns::format * cmd_context::pp(sort * s) const {
    TRACE("cmd_context", tout << "pp(sort * s), s: " << mk_pp(s, m()) << "\n";);
    return pm().pp(s);
}

cmd_context::pp_env & cmd_context::get_pp_env() const {
    if (m_pp_env.get() == nullptr) {
        const_cast<cmd_context*>(this)->m_pp_env = alloc(pp_env, *const_cast<cmd_context*>(this));
    }
    return *(m_pp_env.get());
}

void cmd_context::pp(expr * n, unsigned num_vars, char const * var_prefix, format_ns::format_ref & r, sbuffer<symbol> & var_names) const {
    mk_smt2_format(n, get_pp_env(), params_ref(), num_vars, var_prefix, r, var_names);
}

void cmd_context::pp(expr * n, format_ns::format_ref & r) const {
    sbuffer<symbol> buf;
    pp(n, 0, nullptr, r, buf);
}

void cmd_context::pp(func_decl * f, format_ns::format_ref & r) const {
    mk_smt2_format(f, get_pp_env(), params_ref(), r, "declare-fun");
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
    display(out, n, indent, 0, nullptr, buf);
}

void cmd_context::display(std::ostream & out, func_decl * d, unsigned indent) const {
    format_ns::format_ref f(format_ns::fm(m()));
    pp(d, f);
    if (indent > 0)
        f = format_ns::mk_indent(m(), indent, f);
    ::pp(out, f.get(), m());
}

void cmd_context::dump_assertions(std::ostream & out) const {
    for (expr * e : m_assertions) {
        display(out, e);
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

void cmd_context::dt_eh::operator()(sort * dt, pdecl* pd) {
    TRACE("new_dt_eh", tout << "new datatype: "; m_owner.pm().display(tout, dt); tout << "\n";);
    for (func_decl * c : *m_dt_util.get_datatype_constructors(dt)) {
        TRACE("new_dt_eh", tout << "new constructor: " << c->get_name() << "\n";);
        m_owner.insert(c);
        func_decl * r = m_dt_util.get_constructor_recognizer(c);
        m_owner.insert(r);
        // TRACE("new_dt_eh", tout << "new recognizer: " << r->get_name() << "\n";);
        for (func_decl * a : *m_dt_util.get_constructor_accessors(c)) {
            TRACE("new_dt_eh", tout << "new accessor: " << a->get_name() << "\n";);
            m_owner.insert(a);
        }
    }
    if (m_owner.m_scopes.size() > 0) {
        m_owner.pm().inc_ref(pd);
        m_owner.m_psort_inst_stack.push_back(pd);
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

