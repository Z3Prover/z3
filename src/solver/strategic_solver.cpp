/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    strategic_solver.h

Abstract:

    Strategies -> Solver

Author:

    Leonardo (leonardo) 2011-05-19

Notes:

--*/
#include"strategic_solver.h"
#include"scoped_timer.h"
#include"front_end_params.h"
#include"params2front_end_params.h"
#include"ast_smt2_pp.h"

// minimum verbosity level for portfolio verbose messages
#define PS_VB_LVL 15

    
strategic_solver::ctx::ctx(ast_manager & m):
    m_assertions(m), 
    m_assertion_names(m) {
    }    

strategic_solver::strategic_solver():
    m_manager(0),
    m_fparams(0),
    m_force_tactic(false),
    m_inc_mode(false),
    m_check_sat_executed(false),
    m_inc_solver(0),
    m_inc_solver_timeout(UINT_MAX),
    m_inc_unknown_behavior(IUB_USE_TACTIC_IF_QF),
    m_default_fct(0),
    m_curr_tactic(0),
    m_proof(0),
    m_core(0),
    m_callback(0) {
    m_use_inc_solver_results = false;
    DEBUG_CODE(m_num_scopes = 0;);
    m_produce_proofs = false;
    m_produce_models = false;
    m_produce_unsat_cores = false;
}

strategic_solver::~strategic_solver() {
    SASSERT(!m_curr_tactic);
    dictionary<tactic_factory*>::iterator it  = m_logic2fct.begin();
    dictionary<tactic_factory*>::iterator end = m_logic2fct.end();
    for (; it != end; ++it) {
        dealloc(it->m_value);
    }
    if (m_proof)
        m().dec_ref(m_proof);
    if (m_core)
        m().dec_ref(m_core);
}

bool strategic_solver::has_quantifiers() const {
    unsigned sz = get_num_assertions();
    for (unsigned i = 0; i < sz; i++) {
        if (::has_quantifiers(get_assertion(i)))
            return true;
    }
    return false;
}

/**
   \brief Return true if a tactic should be used when the incremental solver returns unknown.
*/
bool strategic_solver::use_tactic_when_undef() const {
    switch (m_inc_unknown_behavior) {
    case IUB_RETURN_UNDEF: return false;
    case IUB_USE_TACTIC_IF_QF: return !has_quantifiers();
    case IUB_USE_TACTIC: return true;
    default:
        UNREACHABLE();
        return false;
    }
}

void strategic_solver::set_inc_solver(solver * s) {
    SASSERT(m_inc_solver == 0);
    SASSERT(m_num_scopes == 0);
    m_inc_solver = s;
    if (m_callback)
        m_inc_solver->set_progress_callback(m_callback);
}

void strategic_solver::updt_params(params_ref const & p) {
    if (m_inc_solver)
        m_inc_solver->updt_params(p);
    if (m_fparams)
        params2front_end_params(p, *m_fparams);
}


void strategic_solver::collect_param_descrs(param_descrs & r) {
    if (m_inc_solver)
        m_inc_solver->collect_param_descrs(r);
}

/**
   \brief Set a timeout for each check_sat query that is processed by the inc_solver.
   timeout == UINT_MAX means infinite
   After the timeout a strategy is used.
*/
void strategic_solver::set_inc_solver_timeout(unsigned timeout) {
    m_inc_solver_timeout = timeout;
}

/**
   \brief Set the default tactic factory.
   It is used if there is no tactic for a given logic.
*/
void strategic_solver::set_default_tactic(tactic_factory * fct) {
    m_default_fct = fct;
}

/**
   \brief Set a tactic factory for a given logic.
*/
void strategic_solver::set_tactic_for(symbol const & logic, tactic_factory * fct) {
    tactic_factory * old_fct;
    if (m_logic2fct.find(logic, old_fct)) {
        dealloc(old_fct);
    }
    m_logic2fct.insert(logic, fct);
}

void strategic_solver::init(ast_manager & m, symbol const & logic) {
    m_manager = &m;
    m_logic   = logic;
    if (m_inc_mode) {
        SASSERT(m_inc_solver);
        m_inc_solver->init(m, logic);
    }
    m_ctx = alloc(ctx, m);
    TRACE("strategic_solver", tout << "strategic_solver was initialized.\n";);
}

unsigned strategic_solver::get_num_assertions() const {
    if (m_ctx == 0)
        return 0;
    return m_ctx->m_assertions.size();
}

expr * strategic_solver::get_assertion(unsigned idx) const {
    SASSERT(m_ctx);
    return m_ctx->m_assertions.get(idx);
}

expr * strategic_solver::get_assertion_name(unsigned idx) const {
    SASSERT(m_ctx);
    SASSERT(m_produce_unsat_cores);
    return m_ctx->m_assertion_names.get(idx);
}

void strategic_solver::set_produce_proofs(bool f) { 
    m_produce_proofs = f; 
    // do not need to propagate to inc_solver since flag cannot be changed after initialization
}

void strategic_solver::set_produce_models(bool f) { 
    m_produce_models = f; 
    if (m_inc_solver) 
        m_inc_solver->set_produce_models(f);
}

void strategic_solver::set_produce_unsat_cores(bool f) { 
    m_produce_unsat_cores = f; 
    // do not need to propagate to inc_solver since flag cannot be changed after initialization
}

// delayed inc solver initialization
void strategic_solver::init_inc_solver() {
    if (m_inc_mode) 
        return; // solver was already initialized
    if (!m_inc_solver)
        return; // inc solver was not installed
    m_inc_mode = true;
    m_inc_solver->set_produce_proofs(m_produce_proofs);
    m_inc_solver->set_produce_models(m_produce_models);
    m_inc_solver->set_produce_unsat_cores(m_produce_unsat_cores);
    m_inc_solver->set_front_end_params(*m_fparams);
    m_inc_solver->init(m(), m_logic);
    unsigned sz = get_num_assertions();
    if (m_produce_unsat_cores) {
        SASSERT(m_ctx->m_assertions.size() == m_ctx->m_assertion_names.size());
        for (unsigned i = 0; i < sz; i++) {
            m_inc_solver->assert_expr(get_assertion(i), get_assertion_name(i));
        }
    }
    else {
        for (unsigned i = 0; i < sz; i++) {
            m_inc_solver->assert_expr(get_assertion(i));
        }
    }
}

void strategic_solver::collect_statistics(statistics & st) const {
    if (m_use_inc_solver_results) {
        SASSERT(m_inc_solver);
        m_inc_solver->collect_statistics(st);
    }
    else {
        if (m_curr_tactic) 
            m_curr_tactic->collect_statistics(st); // m_curr_tactic is still being executed.
        else
            st.copy(m_stats);
    }
}

void strategic_solver::reset() {
    m_ctx      = 0;
    m_logic    = symbol::null;
    m_inc_mode = false;
    m_check_sat_executed = false;
    if (m_inc_solver)
        m_inc_solver->reset();
    SASSERT(!m_curr_tactic);
    m_use_inc_solver_results = false;
    reset_results();
}

void strategic_solver::reset_results() {
    m_use_inc_solver_results = false;
    m_model = 0;
    if (m_proof) {
        m().dec_ref(m_proof);
        m_proof = 0;
    }
    if (m_core) {
        m().dec_ref(m_core);
        m_core = 0;
    }
    m_reason_unknown.clear();
    m_stats.reset();
}

void strategic_solver::assert_expr(expr * t) {
    if (m_check_sat_executed && !m_inc_mode) {
        // a check sat was already executed --> switch to incremental mode
        init_inc_solver();
        SASSERT(m_inc_solver == 0 || m_inc_mode);
    }
    if (m_inc_mode) {
        SASSERT(m_inc_solver);
        m_inc_solver->assert_expr(t);
    }
    SASSERT(m_ctx);
    m_ctx->m_assertions.push_back(t);
    if (m_produce_unsat_cores)
        m_ctx->m_assertion_names.push_back(0);
}

void strategic_solver::assert_expr(expr * t, expr * a) {
    if (m_check_sat_executed && !m_inc_mode) {
        // a check sat was already executed --> switch to incremental mode
        init_inc_solver();
        SASSERT(m_inc_solver == 0 || m_inc_mode);
    }
    if (m_inc_mode) {
        SASSERT(m_inc_solver);
        m_inc_solver->assert_expr(t, a);
    }
    SASSERT(m_ctx);
    m_ctx->m_assertions.push_back(t);
    if (m_produce_unsat_cores)
        m_ctx->m_assertion_names.push_back(a);
}

void strategic_solver::push() {
    DEBUG_CODE(m_num_scopes++;);
    init_inc_solver();
    if (m_inc_solver)
        m_inc_solver->push();
    m_ctx->m_scopes.push_back(m_ctx->m_assertions.size());
}

void strategic_solver::pop(unsigned n) {
    DEBUG_CODE({
            SASSERT(n <= m_num_scopes);
            m_num_scopes -= n;
        });
    init_inc_solver();
    if (m_inc_solver)
        m_inc_solver->pop(n);

    SASSERT(m_ctx);
    unsigned new_lvl = m_ctx->m_scopes.size() - n;
    unsigned old_sz  = m_ctx->m_scopes[new_lvl];
    m_ctx->m_assertions.shrink(old_sz);
    if (m_produce_unsat_cores)
        m_ctx->m_assertion_names.shrink(old_sz);
    m_ctx->m_scopes.shrink(new_lvl);
}

unsigned strategic_solver::get_scope_level() const {
    if (m_ctx == 0)
        return 0;
    return m_ctx->m_assertions.size();
}

struct aux_timeout_eh : public event_handler {
    solver *        m_solver;
    volatile bool   m_canceled;
    aux_timeout_eh(solver * s):m_solver(s), m_canceled(false) {}
    virtual void operator()() {
        m_solver->cancel();
        m_canceled = true;
    }
};

struct strategic_solver::mk_tactic {
    strategic_solver *  m_solver;

    mk_tactic(strategic_solver * s, tactic_factory * f):m_solver(s) {
        ast_manager & m = s->m();
        params_ref p;
        front_end_params2params(*s->m_fparams, p);
        tactic * tct = (*f)(m, p);
        tct->set_front_end_params(*s->m_fparams);
        tct->set_logic(s->m_logic);
        if (s->m_callback)
            tct->set_progress_callback(s->m_callback);
        #pragma omp critical (strategic_solver) 
        {
            s->m_curr_tactic = tct;
        }
    }

    ~mk_tactic() {
        #pragma omp critical (strategic_solver)
        {
            m_solver->m_curr_tactic = 0;
        }
    }
};

tactic_factory * strategic_solver::get_tactic_factory() const {
    tactic_factory * f = 0;
    if (m_logic2fct.find(m_logic, f))
        return f;
    return m_default_fct.get();
}

lbool strategic_solver::check_sat_with_assumptions(unsigned num_assumptions, expr * const * assumptions) {
    if (!m_inc_solver) {
        IF_VERBOSE(PS_VB_LVL, verbose_stream() << "incremental solver was not installed, returning unknown...\n";);
        m_use_inc_solver_results = false;
        m_reason_unknown         = "incomplete";
        return l_undef; 
    }
    init_inc_solver();
    m_use_inc_solver_results = true;
    TRACE("strategic_solver", tout << "invoking inc_solver with " << num_assumptions << " assumptions\n";);
    return m_inc_solver->check_sat(num_assumptions, assumptions);
}

lbool strategic_solver::check_sat(unsigned num_assumptions, expr * const * assumptions) {
    TRACE("strategic_solver", tout << "assumptions at strategic_solver:\n";
          for (unsigned i = 0; i < num_assumptions; i++) {
              tout << mk_ismt2_pp(assumptions[i], m()) << "\n";
          }
          tout << "m_produce_unsat_cores: " << m_produce_unsat_cores << ", m_inc_mode: " << m_inc_mode << "\n";);
    reset_results();
    m_check_sat_executed = true;
    if (num_assumptions > 0 || // assumptions were provided
        (!m_fparams->m_auto_config && !m_force_tactic) // auto config and force_tactic are turned off
        ) {
        // must use incremental solver
        return check_sat_with_assumptions(num_assumptions, assumptions);
    }

    tactic_factory * factory = get_tactic_factory();
    if (factory == 0)
        init_inc_solver(); // try to switch to incremental solver
    
    if (m_inc_mode) {
        SASSERT(m_inc_solver);
        unsigned timeout = m_inc_solver_timeout;
        if (factory == 0)
            timeout = UINT_MAX; // there is no tactic available
        if (timeout == UINT_MAX) {
            IF_VERBOSE(PS_VB_LVL, verbose_stream() << "using incremental solver (without a timeout).\n";);            
            m_use_inc_solver_results = true;
            lbool r = m_inc_solver->check_sat(0, 0);
            if (r != l_undef || factory == 0 || !use_tactic_when_undef()) {
                m_use_inc_solver_results = true;
                return r;
            }
        }
        else {
            IF_VERBOSE(PS_VB_LVL, verbose_stream() << "using incremental solver (with timeout).\n";);            
            SASSERT(factory != 0);
            aux_timeout_eh eh(m_inc_solver.get());
            lbool r;
            {
                scoped_timer timer(m_inc_solver_timeout, &eh);
                r = m_inc_solver->check_sat(0, 0);
            }
            if ((r != l_undef || !use_tactic_when_undef()) && !eh.m_canceled) {
                m_use_inc_solver_results = true;
                return r;
            }
        }
        IF_VERBOSE(PS_VB_LVL, verbose_stream() << "incremental solver failed, trying tactic.\n";);                        
    }
    
    m_use_inc_solver_results = false;
    
    if (factory == 0) {
        IF_VERBOSE(PS_VB_LVL, verbose_stream() << "there is no tactic available for the current logic.\n";);            
        m_reason_unknown         = "incomplete";
        return l_undef; 
    }

    goal_ref g = alloc(goal, m(), m_produce_proofs, m_produce_models, m_produce_unsat_cores);
    unsigned sz = get_num_assertions();
    if (m_produce_unsat_cores) {
        SASSERT(m_ctx->m_assertions.size() == m_ctx->m_assertion_names.size());
        for (unsigned i = 0; i < sz; i++)
            g->assert_expr(get_assertion(i), get_assertion_name(i));
    }
    else {
        for (unsigned i = 0; i < sz; i++)
            g->assert_expr(get_assertion(i));
    }
    expr_dependency_ref core(m());

    TRACE("strategic_solver", tout << "using goal...\n"; g->display_with_dependencies(tout););
    
    mk_tactic tct_maker(this, factory);
    SASSERT(m_curr_tactic);

    proof_ref pr(m());
    lbool r = ::check_sat(*(m_curr_tactic.get()), g, m_model, pr, core, m_reason_unknown);
    m_curr_tactic->collect_statistics(m_stats);
    if (pr) {
        m_proof = pr; 
        m().inc_ref(m_proof);
    }
    if (core) {
        m_core = core;
        m().inc_ref(m_core);
    }
    return r;
}

void strategic_solver::set_cancel(bool f) {
    if (m_inc_solver)
        m_inc_solver->set_cancel(f);
    #pragma omp critical (strategic_solver)
    {
        if (m_curr_tactic)
            m_curr_tactic->set_cancel(f);
    }
}

void strategic_solver::get_unsat_core(ptr_vector<expr> & r) {
    TRACE("strategic_solver", tout << "get_unsat_core, m_use_inc_solver_results: " << m_use_inc_solver_results << "\n";);
    if (m_use_inc_solver_results) {
        SASSERT(m_inc_solver);
        m_inc_solver->get_unsat_core(r); 
    }
    else {
        m().linearize(m_core, r);
    }
}

void strategic_solver::get_model(model_ref & m) {
    if (m_use_inc_solver_results) {
        SASSERT(m_inc_solver);
        m_inc_solver->get_model(m);
    }
    else {
        m = m_model;
    }
}

proof * strategic_solver::get_proof() {
    if (m_use_inc_solver_results) {
        SASSERT(m_inc_solver);
        return m_inc_solver->get_proof();
    }
    else {
        return m_proof;
    }
}

std::string strategic_solver::reason_unknown() const {
    if (m_use_inc_solver_results) {
        SASSERT(m_inc_solver);
        return m_inc_solver->reason_unknown();
    }
    return m_reason_unknown;
}

void strategic_solver::get_labels(svector<symbol> & r) {
    if (m_use_inc_solver_results) {
        SASSERT(m_inc_solver);
        m_inc_solver->get_labels(r);
    }
}

void strategic_solver::set_progress_callback(progress_callback * callback) { 
    m_callback = callback; 
    if (m_inc_solver)
        m_inc_solver->set_progress_callback(callback);
}

void strategic_solver::display(std::ostream & out) const {
    if (m_manager) {
        unsigned num = get_num_assertions();
        out << "(solver";
        for (unsigned i = 0; i < num; i++) {
            out << "\n  " << mk_ismt2_pp(get_assertion(i), m(), 2);
        }
        out << ")";
    }
    else {
        out << "(solver)";
    }
}






