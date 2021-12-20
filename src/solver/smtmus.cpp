/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    musrmr.cpp

Abstract:
   
    MUS extraction with model rotation modulo arithmatic.

Author:

    Jaroslav Bendik, Nikolaj Bjorner (nbjorner) 2021-12-20

--*/

#include "solver/solver.h"
#include "solver/smtmus.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "model/model_evaluator.h"
#include "ast/arith_decl_plugin.h"


struct smtmus::imp {

    typedef obj_hashtable<expr> expr_set;

    solver&                  m_solver;
    ast_manager&             m;
    expr_ref_vector          m_lit2expr;
    obj_map<expr, unsigned>  m_expr2lit;
    model_ref                m_model;
    expr_ref_vector          m_soft;
    vector<expr_ref_vector>  m_soft_clauses;
    obj_map<expr, expr_ref_vector*> m_lit2vars;

    imp(solver& s): 
        m_solver(s), m(s.get_manager()), m_lit2expr(m),  m_soft(m)
    {}

    ~imp() {
        for (auto& [k, v] : m_lit2vars)
            dealloc(v);
    }

    
    unsigned add_soft(expr* lit) {
        unsigned idx = m_lit2expr.size();
        m_expr2lit.insert(lit, idx);
        m_lit2expr.push_back(lit);
        TRACE("mus", tout << idx << ": " << mk_pp(lit, m) << "\n" << m_lit2expr << "\n";);
        return idx;
    }

    void init() {
        // initialize soft_clauses based on control variables in mus, or if mus already is a clause.
    }


    lbool get_mus(expr_ref_vector& mus) {
        m_model.reset();
        mus.reset();
        if (m_lit2expr.size() == 1) {
            mus.push_back(m_lit2expr.back());
            return l_true;
        }
        return l_undef;
    }

    // extract clauses corresponding to added soft constraints.
    // extract integer, real variables from clauses
    //

    unsigned rotate(bool_vector& crits, unsigned i, model& mdl, bool top_level) {
        unsigned rot = 0;
        for (auto const& lit : m_soft_clauses[i]) {
            auto const& vars = get_vars(lit);
            for (expr* v : vars) {
                expr_ref_vector flips = rotate_get_flips(lit, v, mdl, 1);
                for (auto& flip : flips) {
                    NOT_IMPLEMENTED_YET();
                }
            }
        }
    }

    // access and update lit2vars on demand.
    expr_ref_vector const& get_vars(expr* lit) {
        if (!m_lit2vars.contains(lit)) {
            expr_ref_vector* vars = alloc(expr_ref_vector, m);
            extract_vars(lit, *vars);
            m_lit2vars.insert(lit, vars);            
        }
        return *m_lit2vars[lit];
    }

    void extract_vars(expr* e, expr_ref_vector& vars) {
        NOT_IMPLEMENTED_YET();
    }

    expr_ref_vector rotate_get_flips(expr* lit, expr* v, model& mdl, unsigned xx) {
        NOT_IMPLEMENTED_YET();
        return expr_ref_vector(m);
    }


};

smtmus::smtmus(solver& s) {
    m_imp = alloc(imp, s);
}

smtmus::~smtmus() {
    dealloc(m_imp);
}

unsigned smtmus::add_soft(expr* lit) {
    return m_imp->add_soft(lit);
}

 
lbool smtmus::get_mus(expr_ref_vector& mus) {
    return m_imp->get_mus(mus);
}

