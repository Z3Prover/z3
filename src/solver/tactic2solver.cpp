/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    tactic2solver.cpp

Abstract:

    Wrapper for implementing the solver interface
    using a tactic.

    This is a light version of the strategic solver.

Author:

    Leonardo (leonardo) 2012-01-23

Notes:

--*/
#include"solver_na2as.h"
#include"tactic.h"
#include"ast_pp_util.h"

/**
   \brief Simulates the incremental solver interface using a tactic.

   Every query will be solved from scratch.  So, this is not a good
   option for applications trying to solve many easy queries that a
   similar to each other.
*/
class tactic2solver : public solver_na2as {
    expr_ref_vector              m_assertions;
    unsigned_vector              m_scopes;
    ref<simple_check_sat_result> m_result;
    tactic_ref                   m_tactic;
    symbol                       m_logic;
    params_ref                   m_params;
    bool                         m_produce_models;
    bool                         m_produce_proofs;
    bool                         m_produce_unsat_cores;
    statistics                   m_stats;
public:
    tactic2solver(ast_manager & m, tactic * t, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores, symbol const & logic);
    virtual ~tactic2solver();

    virtual void updt_params(params_ref const & p);
    virtual void collect_param_descrs(param_descrs & r);

    virtual void set_produce_models(bool f) { m_produce_models = f; }

    virtual void assert_expr(expr * t);

    virtual void push_core();
    virtual void pop_core(unsigned n);
    virtual lbool check_sat_core(unsigned num_assumptions, expr * const * assumptions);

    virtual void set_cancel(bool f);

    virtual void collect_statistics(statistics & st) const;
    virtual void get_unsat_core(ptr_vector<expr> & r);
    virtual void get_model(model_ref & m);
    virtual proof * get_proof();
    virtual std::string reason_unknown() const;
    virtual void get_labels(svector<symbol> & r) {}

    virtual void set_progress_callback(progress_callback * callback) {}

    virtual unsigned get_num_assertions() const;
    virtual expr * get_assertion(unsigned idx) const;

    virtual void display(std::ostream & out) const;
};

tactic2solver::tactic2solver(ast_manager & m, tactic * t, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores, symbol const & logic):
    solver_na2as(m),
    m_assertions(m) {

    m_tactic = t;
    m_logic  = logic;
    m_params = p;
    
    m_produce_models      = produce_models;
    m_produce_proofs      = produce_proofs;
    m_produce_unsat_cores = produce_unsat_cores;
}

tactic2solver::~tactic2solver() {
}

void tactic2solver::updt_params(params_ref const & p) {
    m_params = p;
}

void tactic2solver::collect_param_descrs(param_descrs & r) {
    if (m_tactic.get())
        m_tactic->collect_param_descrs(r);
}

void tactic2solver::assert_expr(expr * t) {
    m_assertions.push_back(t);
    m_result = 0;
}

void tactic2solver::push_core() {
    m_scopes.push_back(m_assertions.size());
    m_result = 0;
}

void tactic2solver::pop_core(unsigned n) {
    unsigned new_lvl = m_scopes.size() - n;
    unsigned old_sz  = m_scopes[new_lvl];
    m_assertions.shrink(old_sz);
    m_scopes.shrink(new_lvl);
    m_result = 0;
}

lbool tactic2solver::check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
    if (m_tactic.get() == 0)
        return l_false;
    ast_manager & m = m_assertions.m();
    m_result = alloc(simple_check_sat_result, m);
    m_tactic->cleanup();
    m_tactic->updt_params(m_params);
    m_tactic->set_logic(m_logic);
    goal_ref g = alloc(goal, m, m_produce_proofs, m_produce_models, m_produce_unsat_cores);

    unsigned sz = m_assertions.size();
    for (unsigned i = 0; i < sz; i++) {
        g->assert_expr(m_assertions.get(i));
    }
    for (unsigned i = 0; i < num_assumptions; i++) {
        g->assert_expr(assumptions[i], m.mk_asserted(assumptions[i]), m.mk_leaf(assumptions[i]));
    }

    model_ref           md;
    proof_ref           pr(m);
    expr_dependency_ref core(m);
    std::string         reason_unknown = "unknown";
    try {
        switch (::check_sat(*m_tactic, g, md, pr, core, reason_unknown)) {
        case l_true: 
            m_result->set_status(l_true);
            break;
        case l_false: 
            m_result->set_status(l_false);
            break;
        default: 
            m_result->set_status(l_undef);
            if (reason_unknown != "")
                m_result->m_unknown = reason_unknown;
            break;
        }
    }
    catch (z3_error & ex) {
        throw ex;
    }
    catch (z3_exception & ex) {
        TRACE("tactic2solver", tout << "exception: " << ex.msg() << "\n";);
        m_result->set_status(l_undef);
        m_result->m_unknown = ex.msg();
    }
    m_tactic->collect_statistics(m_result->m_stats);
    m_tactic->collect_statistics(m_stats);
    m_result->m_model = md;
    m_result->m_proof = pr;
    if (m_produce_unsat_cores) {
        ptr_vector<expr> core_elems;
        m.linearize(core, core_elems);
        m_result->m_core.append(core_elems.size(), core_elems.c_ptr());
    }
    m_tactic->cleanup();
    return m_result->status();
}

void tactic2solver::set_cancel(bool f) {
    if (m_tactic.get()) {
        if (f) 
            m_tactic->cancel();
        else
            m_tactic->reset_cancel();
    }
}

void tactic2solver::collect_statistics(statistics & st) const {    
    st.copy(m_stats);
    //SASSERT(m_stats.size() > 0);
}

void tactic2solver::get_unsat_core(ptr_vector<expr> & r) {
    if (m_result.get())
        m_result->get_unsat_core(r);
}

void tactic2solver::get_model(model_ref & m) {
    if (m_result.get())
        m_result->get_model(m);
}

proof * tactic2solver::get_proof() {
    if (m_result.get())
        return m_result->get_proof();
    else
        return 0;
}

std::string tactic2solver::reason_unknown() const {
    if (m_result.get())
        return m_result->reason_unknown();
    else
        return std::string("unknown");
}

unsigned tactic2solver::get_num_assertions() const {
    return m_assertions.size();
}

expr * tactic2solver::get_assertion(unsigned idx) const {
    return m_assertions.get(idx);
}

void tactic2solver::display(std::ostream & out) const {
    ast_pp_util visitor(m_assertions.m());
    visitor.collect(m_assertions);
    visitor.display_decls(out);
    visitor.display_asserts(out, m_assertions, true);
#if 0
    ast_manager & m = m_assertions.m();
    unsigned num = m_assertions.size();
    out << "(solver";
    for (unsigned i = 0; i < num; i++) {
        out << "\n  " << mk_ismt2_pp(m_assertions.get(i), m, 2);
    }
    out << ")";
#endif
}

solver * mk_tactic2solver(ast_manager & m, 
                          tactic * t, 
                          params_ref const & p,
                          bool produce_proofs,
                          bool produce_models,
                          bool produce_unsat_cores,
                          symbol const & logic) {
    return alloc(tactic2solver, m, t, p, produce_proofs, produce_models, produce_unsat_cores, logic);
}

class tactic2solver_factory : public solver_factory {
    ref<tactic> m_tactic;
public:
    tactic2solver_factory(tactic * t):m_tactic(t) {
    }
    
    virtual ~tactic2solver_factory() {}
    
    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
        return mk_tactic2solver(m, m_tactic.get(), p, proofs_enabled, models_enabled, unsat_core_enabled, logic);
    }
};

class tactic_factory2solver_factory : public solver_factory {
    scoped_ptr<tactic_factory> m_factory;
public:
    tactic_factory2solver_factory(tactic_factory * f):m_factory(f) {
    }
    
    virtual ~tactic_factory2solver_factory() {}
    
    virtual solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) {
        tactic * t = (*m_factory)(m, p);
        return mk_tactic2solver(m, t, p, proofs_enabled, models_enabled, unsat_core_enabled, logic);
    }
};

solver_factory * mk_tactic2solver_factory(tactic * t) {
    return alloc(tactic2solver_factory, t);
}

solver_factory * mk_tactic_factory2solver_factory(tactic_factory * f) {
    return alloc(tactic_factory2solver_factory, f);
}
