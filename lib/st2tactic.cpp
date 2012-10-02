/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    st2tactic.h

Abstract:

    Temporary adapter that converts a assertion_set_strategy into a tactic.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#include"assertion_set_strategy.h"
#include"tactic.h"

class st2tactic_wrapper : public tactic {
    assertion_set_strategy * m_st;
    params_ref               m_params;
public:
    st2tactic_wrapper(assertion_set_strategy * st):m_st(st) {}
    ~st2tactic_wrapper() { dealloc(m_st); }

    virtual tactic * translate(ast_manager & m) {
        // st2tactic_wrapper is a temporary hack to support the old strategy framework.
        // This class will be deleted in the future.
        UNREACHABLE();
        NOT_IMPLEMENTED_YET();
        return 0;
    }

    virtual void operator()(goal_ref const & g, goal_ref_buffer & result, model_converter_ref & mc, proof_converter_ref & pc, expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        pc = 0; mc = 0; core = 0;
        fail_if_unsat_core_generation("st2tactic", g);
        assertion_set s(g->m());
        for (unsigned i = 0; i < g->size(); i++)
            s.assert_expr(g->form(i), g->pr(i));
        if (g->models_enabled()) {
            params_ref mp = m_params;
            mp.set_bool(":produce-models", true);
            m_st->updt_params(mp);
        }
        try {
            (*m_st)(s, mc);
        }
        catch (strategy_exception & ex) {
            throw tactic_exception(ex.msg());
        }
        g->reset();
        for (unsigned i = 0; i < s.size(); i++) {
            g->assert_expr(s.form(i), s.pr(i), 0);
        }
        g->inc_depth();
        result.push_back(g.get());
        SASSERT(g->is_well_sorted());
    }

    virtual void updt_params(params_ref const & p) { m_params = p; m_st->updt_params(p); }
    virtual void collect_param_descrs(param_descrs & r) { m_st->collect_param_descrs(r); }
    virtual void cleanup() { m_st->cleanup(); }
    virtual void set_cancel(bool f) { m_st->set_cancel(f); }
    virtual void collect_statistics(statistics & st) const { m_st->collect_statistics(st); }
    virtual void reset_statistics() { m_st->reset_statistics(); }
    virtual void set_front_end_params(front_end_params & p) { m_st->set_front_end_params(p); }
    virtual void set_logic(symbol const & l) { m_st->set_logic(l); }
    virtual void set_progress_callback(progress_callback * callback) { m_st->set_progress_callback(callback); }
};

tactic * st2tactic(assertion_set_strategy * st) {
    return alloc(st2tactic_wrapper, st);
}
