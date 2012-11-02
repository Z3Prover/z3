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
#include"tactic2solver.h"
#include"params2front_end_params.h"
#include"ast_smt2_pp.h"

tactic2solver_core::ctx::ctx(ast_manager & m, symbol const & logic):
    m_logic(logic),
    m_assertions(m) {
}

tactic2solver_core::~tactic2solver_core() {
}

void tactic2solver_core::init_core(ast_manager & m, symbol const & logic) {
    m_ctx = alloc(ctx, m, logic);
}

void tactic2solver_core::updt_params(params_ref const & p) {
    m_params = p;
}

void tactic2solver_core::collect_param_descrs(param_descrs & r) {
    if (m_ctx) {
        if (!m_ctx->m_tactic) {
            #pragma omp critical (tactic2solver_core)
            {
                m_ctx->m_tactic = get_tactic(m_ctx->m(), m_params);
            }

            if (m_ctx->m_tactic) {
                m_ctx->m_tactic->collect_param_descrs(r);
            }

            #pragma omp critical (tactic2solver_core)
            {
                m_ctx->m_tactic = 0;
            }
        }
        else {
            m_ctx->m_tactic->collect_param_descrs(r);
        }
    }
}

void tactic2solver_core::reset_core() {
    SASSERT(m_ctx);
    m_ctx->m_assertions.reset();
    m_ctx->m_scopes.reset();
    m_ctx->m_result = 0;
}

void tactic2solver_core::assert_expr(expr * t) {
    SASSERT(m_ctx);
    m_ctx->m_assertions.push_back(t);
    m_ctx->m_result = 0;
}

void tactic2solver_core::push_core() {
    SASSERT(m_ctx);
    m_ctx->m_scopes.push_back(m_ctx->m_assertions.size());
    m_ctx->m_result = 0;
}

void tactic2solver_core::pop_core(unsigned n) {
    SASSERT(m_ctx);
    unsigned new_lvl = m_ctx->m_scopes.size() - n;
    unsigned old_sz  = m_ctx->m_scopes[new_lvl];
    m_ctx->m_assertions.shrink(old_sz);
    m_ctx->m_scopes.shrink(new_lvl);
    m_ctx->m_result = 0;
}

lbool tactic2solver_core::check_sat_core(unsigned num_assumptions, expr * const * assumptions) {
    SASSERT(m_ctx);
    ast_manager & m = m_ctx->m();
    params_ref p = m_params;
    if (m_fparams)
        front_end_params2params(*m_fparams, p);
    #pragma omp critical (tactic2solver_core)
    {
        m_ctx->m_tactic = get_tactic(m, p);
        if (m_ctx->m_tactic) {
            m_ctx->m_result = alloc(simple_check_sat_result, m);
        }
    }
    if (!m_ctx->m_tactic)
        return l_undef;
    tactic & t                       = *(m_ctx->m_tactic);
    simple_check_sat_result & result = *(m_ctx->m_result);
    if (m_fparams)
        t.set_front_end_params(*m_fparams);
    goal_ref g = alloc(goal, m, m_produce_proofs, m_produce_models, m_produce_unsat_cores);
    t.set_logic(m_ctx->m_logic);
    unsigned sz = m_ctx->m_assertions.size();
    for (unsigned i = 0; i < sz; i++) {
        g->assert_expr(m_ctx->m_assertions.get(i));
    }
    for (unsigned i = 0; i < num_assumptions; i++) {
        g->assert_expr(assumptions[i], m.mk_asserted(assumptions[i]), m.mk_leaf(assumptions[i]));
    }

    model_ref           md;
    proof_ref           pr(m);
    expr_dependency_ref core(m);
    std::string         reason_unknown = "unknown";
    try {
        switch (::check_sat(t, g, md, pr, core, reason_unknown)) {
        case l_true: 
            result.set_status(l_true);
            break;
        case l_false: 
            result.set_status(l_false);
            break;
        default: 
            result.set_status(l_undef);
            if (reason_unknown != "")
                result.m_unknown = reason_unknown;
            break;
        }
    }
    catch (z3_error & ex) {
        throw ex;
    }
    catch (z3_exception & ex) {
        TRACE("tactic2solver_core", tout << "exception: " << ex.msg() << "\n";);
        result.set_status(l_undef);
        result.m_unknown = ex.msg();
    }
    t.collect_statistics(result.m_stats);
    result.m_model = md;
    result.m_proof = pr;
    if (m_produce_unsat_cores) {
        ptr_vector<expr> core_elems;
        m.linearize(core, core_elems);
        result.m_core.append(core_elems.size(), core_elems.c_ptr());
    }
    
    #pragma omp critical (tactic2solver_core)
    {
        m_ctx->m_tactic = 0;
    }
    return result.status();
}

void tactic2solver_core::set_cancel(bool f) {
    #pragma omp critical (tactic2solver_core)
    {
        if (m_ctx && m_ctx->m_tactic)
            m_ctx->m_tactic->set_cancel(f);
    }
}

void tactic2solver_core::collect_statistics(statistics & st) const {
    if (m_ctx->m_result.get())
        m_ctx->m_result->collect_statistics(st);
}

void tactic2solver_core::get_unsat_core(ptr_vector<expr> & r) {
    if (m_ctx->m_result.get())
        m_ctx->m_result->get_unsat_core(r);
}

void tactic2solver_core::get_model(model_ref & m) {
    if (m_ctx->m_result.get())
        m_ctx->m_result->get_model(m);
}

proof * tactic2solver_core::get_proof() {
    if (m_ctx->m_result.get())
        return m_ctx->m_result->get_proof();
    else
        return 0;
}

std::string tactic2solver_core::reason_unknown() const {
    if (m_ctx->m_result.get())
        return m_ctx->m_result->reason_unknown();
    else
        return std::string("unknown");
}

unsigned tactic2solver_core::get_num_assertions() const {
    if (m_ctx) 
        return m_ctx->m_assertions.size();
    else
        return 0;
}

expr * tactic2solver_core::get_assertion(unsigned idx) const {
    SASSERT(m_ctx);
    return m_ctx->m_assertions.get(idx);
}

void tactic2solver_core::display(std::ostream & out) const {
    if (m_ctx) {
        ast_manager & m = m_ctx->m_assertions.m();
        unsigned num = m_ctx->m_assertions.size();
        out << "(solver";
        for (unsigned i = 0; i < num; i++) {
            out << "\n  " << mk_ismt2_pp(m_ctx->m_assertions.get(i), m, 2);
        }
        out << ")";
    }
    else {
        out << "(solver)";
    }
}

tactic2solver::tactic2solver(tactic * t):
    m_tactic(t) {
}

tactic2solver::~tactic2solver() {
}

tactic * tactic2solver::get_tactic(ast_manager & m, params_ref const & p) {
    m_tactic->cleanup();
    m_tactic->updt_params(p);
    return m_tactic.get();
}

tactic_factory2solver::~tactic_factory2solver() {
}

void tactic_factory2solver::set_tactic(tactic_factory * f) {
    m_tactic_factory = f;
}

tactic * tactic_factory2solver::get_tactic(ast_manager & m, params_ref const & p) {
    if (m_tactic_factory == 0)
        return 0;
    return (*m_tactic_factory)(m, p);
}
