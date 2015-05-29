/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    qsat.cpp

Abstract:

    Quantifier Satisfiability Solver.

Author:

    Nikolaj Bjorner (nbjorner) 2015-5-28

Revision History:


--*/

#include "qsat.h"
#include "smt_kernel.h"
#include "qe_mbp.h"

namespace qe;

sturct qdef_t {
    expr_ref        m_pred;
    expr_ref        m_expr;
    expr_ref_vector m_vars;
    bool            m_is_forall;
    qdef_t(expr_ref& p, expr_ref& e, expr_ref_vector const& vars, bool is_forall):
        m_pred(p), 
        m_expr(e),
        m_vars(vars),
        m_is_forall(is_forall) {}
};

typedef vector<qdef_t> qdefs_t;

struct pdef_t {
    expr_ref  m_pred;
    expr_ref  m_atom;
    pdef_t(expr_ref& p, expr_ref& a):
        m_pred(p), 
        m_atom(a)
    {}
};

class qsat::impl {
    ast_manager& m;
    mbp          mbp;

    /**
       \brief replace quantified sub-formulas by a predicate, introduce definitions for the predicate.
     */
    void remove_quantifiers(expr_ref_vector& fmls, qdefs_t& defs) {
        
    }

    /** 
        \brief create propositional abstration of formula by replacing atomic sub-formulas by fresh 
        propositional variables, and adding definitions for each propositional formula on the side.
        Assumption is that the formula is quantifier-free.
    */
    void mk_abstract(expr_ref_vector& fmls, vector<pdef_t>& pdefs) {
        expr_ref_vector todo(fmls), trail(m);
        obj_map<expr,expr*> cache;
        ptr_vector<expr> args;
        expr_ref r(m);
        while (!todo.empty()) {
            expr* e = todo.back();
            if (cache.contains(e)) {
                todo.pop_back();
                continue;
            }
            SASSERT(is_app(e));
            app* a = to_app(e);
            if (a->get_family_id() == m.get_basic_family_id()) {
                unsigned sz = a->get_num_args();
                args.reset();
                for (unsigned i = 0; i < sz; ++i) {
                    expr* f = a->get_arg(i);
                    if (cache.find(f, f)) {
                        args.push_back(f);
                    }
                    else {
                        todo.push_back(f);
                    }
                }
                if (args.size() == sz) {
                    r = m.mk_app(a->get_decl(), sz, args.c_ptr());
                    cache.insert(e, r);
                    trail.push_back(r);
                    todo.pop_back(e);
                }
            }
            else if (is_uninterpreted_const(a)) {
                cache.insert(e, e);
            }
            else {
                // TBD: nested Booleans.
                r = m.mk_fresh_const("p",m.mk_bool_sort());
                trail.push_back(r);
                cache.insert(e, r);
                pdefs.push_back(pdef_t(e, r));
            }
        }
        
        for (unsigned i = 0; i < fmls.size(); ++i) {
            fmls[i] = cache.find(fmls[i].get());
        }
    }

    /** 
        \brief use dual propagation to minimize model.
    */
    void minimize_assignment(app_ref_vector& assignment) {
        
    }

public:
    impl(ast_manager& m):
        m(m),
        mbp(m) {}

    void updt_params(params_ref const & p) {
    }
    void collect_param_descrs(param_descrs & r) {
    }
    void operator()(/* in */  goal_ref const & in, 
                    /* out */ goal_ref_buffer & result, 
                    /* out */ model_converter_ref & mc, 
                    /* out */ proof_converter_ref & pc,
                    /* out */ expr_dependency_ref & core) {

    }

    void collect_statistics(statistics & st) const {

    }
    void reset_statistics() {
    }
    void cleanup() {
    }
    void set_logic(symbol const & l) {
    }
    void set_progress_callback(progress_callback * callback) {
    }
    tactic * translate(ast_manager & m) {
        return 0;
    }

};

qsat::qsat(ast_manager& m) {
    m_impl = alloc(impl, m);
}

qsat::~qsat() {
    dealloc(m_impl);
}

void qsat::updt_params(params_ref const & p) {
    m_impl->updt_params(p);
}
void qsat::collect_param_descrs(param_descrs & r) {
    m_impl->collect_param_descrs(r);
}
void qsat::operator()(/* in */  goal_ref const & in, 
                      /* out */ goal_ref_buffer & result, 
                      /* out */ model_converter_ref & mc, 
                      /* out */ proof_converter_ref & pc,
                      /* out */ expr_dependency_ref & core) {
    (*m_impl)(in, result, mc, pc, core);
}

void qsat::collect_statistics(statistics & st) const {
    m_impl->collect_statistics(st);
}
void qsat::reset_statistics() {
    m_impl->reset_statistics();
}
void qsat::cleanup() {
    m_impl->cleanup();
}
void qsat::set_logic(symbol const & l) {
    m_impl->set_logic(l);
}
void qsat::set_progress_callback(progress_callback * callback) {
    m_impl->set_progress_callback(callback);
}
tactic * qsat::translate(ast_manager & m) {
    return m_impl->translate(m);
}


};

#endif 
